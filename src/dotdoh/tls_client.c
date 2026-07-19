/* Pi-hole: A black hole for Internet advertisements
*  (c) 2026 Pi-hole, LLC (https://pi-hole.net)
*  Network-wide ad blocking via your own hardware.
*
*  FTL Engine
*  Outbound TLS client for encrypted upstreams (DoT/DoH)
*
*  Talks TLS to the real upstream resolver. Verification is REQUIRED (chain +
*  hostname): a failed check aborts the handshake, so the path is fail-closed by
*  construction. The caller then gets -1 and drops the query, and FTL fails over
*  to the next server - we never downgrade to plaintext.
*
*  This file is copyright under the latest version of the EUPL.
*  Please see LICENSE file for your rights under this license. */

#include "FTL.h"
#include "log.h"
#include "tls_client.h"

#ifdef HAVE_TLS

#include "framing.h"
#include <openssl/ssl.h>
#include <openssl/x509.h>
#include <openssl/err.h>
// For the bounded, non-blocking connect and the socket-level send timeout below.
#include <sys/socket.h>
#include <netdb.h>
#include <poll.h>
#include <fcntl.h>
#include <time.h>

// Read timeout (ms) applied to the handshake and to reading the answer. Keeps a
// dead or slow upstream from stalling the query indefinitely; on timeout the
// exchange fails and dnsmasq fails over.
#define TLS_READ_TIMEOUT_MS 5000

// Timeout (ms) for the TCP connect to the upstream, plus an overall wall-clock
// budget for the whole exchange (connect + handshake + write + read). The
// per-op read timeout above only bounds an idle peer; it does not bound a
// black-holed connect(), a blocking write to a peer whose receive window is
// full, or a peer that trickles one byte before each idle timeout. These hard
// deadlines do, so a single unreachable or misbehaving upstream cannot pin the
// single worker thread and stall every other encrypted upstream with it.
#define TLS_CONNECT_TIMEOUT_MS 5000
#define TLS_EXCHANGE_TIMEOUT_MS 10000

// Where to look for trust anchors when no explicit CA path is configured.
// Distributions place the system bundle differently, so try the common
// single-file locations in turn and finally the hashed directory. FTL ships as
// a musl binary that can run on any of these, so this is deliberately not
// Debian-only.
static const char *const TLS_DEFAULT_CA_FILES[] = {
	"/etc/ssl/certs/ca-certificates.crt", // Debian, Ubuntu, Alpine, Gentoo
	"/etc/pki/tls/certs/ca-bundle.crt",   // RHEL, Fedora, CentOS
	"/etc/ssl/ca-bundle.pem",             // openSUSE
	"/etc/ssl/cert.pem",                  // Alpine, *BSD, macOS
};
#define TLS_DEFAULT_CA_DIR  "/etc/ssl/certs"

// Shared, read-only-after-init crypto state. One SSL_CTX carries the trust
// store and the fail-closed verify mode for all upstreams; each connection
// draws its own SSL object from it. OpenSSL seeds its own RNG, so no explicit
// DRBG is wired up here.
static bool g_ready = false;
static SSL_CTX *g_ctx = NULL;

// One pooled connection per upstream. The scratch buffers live here (not on the
// stack and not shared) so that concurrent exchanges on different connections
// never clobber each other.
struct tls_conn {
	bool connected;
	int fd;                                         // connected TCP socket
	SSL *ssl;
	uint8_t req[DNS_MSG_MAX + 512];                 // framed request we send
	uint8_t rbuf[DNS_MSG_MAX + DOH_HEADER_MAX];     // response accumulation buffer
};

bool tls_client_global_init(const char *ca_file)
{
	// Idempotent: the proxy may be (re)started, but the context only needs to
	// be built once.
	if(g_ready)
		return true;

	g_ctx = SSL_CTX_new(TLS_client_method());
	if(g_ctx == NULL)
	{
		log_err("dotdoh: SSL_CTX_new() failed");
		return false;
	}

	// Require at least TLS 1.2 for encrypted DNS upstreams.
	SSL_CTX_set_min_proto_version(g_ctx, TLS1_2_VERSION);

	// This is the fail-closed heart of the client: SSL_VERIFY_PEER makes a bad
	// chain abort the handshake instead of merely being reported after the
	// fact. The hostname is checked per-connection via SSL_set1_host() below.
	SSL_CTX_set_verify(g_ctx, SSL_VERIFY_PEER, NULL);

	// Load the trust anchors. An explicit path (dns.upstreamCA, or the test CA
	// during E2E) always wins. Otherwise try each well-known system bundle and
	// finally the hashed directory.
	int loaded = 0;
	if(ca_file != NULL && ca_file[0] != '\0')
		loaded = SSL_CTX_load_verify_file(g_ctx, ca_file) == 1;
	else
	{
		for(size_t i = 0; !loaded && i < sizeof(TLS_DEFAULT_CA_FILES) / sizeof(*TLS_DEFAULT_CA_FILES); i++)
			loaded = SSL_CTX_load_verify_file(g_ctx, TLS_DEFAULT_CA_FILES[i]) == 1;
		if(!loaded)
			loaded = SSL_CTX_load_verify_dir(g_ctx, TLS_DEFAULT_CA_DIR) == 1;
	}
	if(!loaded)
	{
		log_err("dotdoh: could not load a CA trust store "
		        "(set dns.upstreamCA or install a system CA bundle)");
		SSL_CTX_free(g_ctx);
		g_ctx = NULL;
		return false;
	}

	g_ready = true;
	return true;
}

void tls_client_global_free(void)
{
	if(!g_ready)
		return;
	SSL_CTX_free(g_ctx);
	g_ctx = NULL;
	g_ready = false;
}

struct tls_conn *tls_conn_new(void)
{
	struct tls_conn *c = calloc(1, sizeof(struct tls_conn));
	if(c != NULL)
		c->fd = -1;
	return c;
}

// Tear down an established connection so the next exchange reconnects cleanly.
static void conn_close(struct tls_conn *c)
{
	if(!c->connected)
		return;
	// Best-effort notify; we do not care whether the peer sees it.
	if(c->ssl != NULL)
	{
		SSL_shutdown(c->ssl);
		SSL_free(c->ssl);
		c->ssl = NULL;
	}
	if(c->fd >= 0)
	{
		close(c->fd);
		c->fd = -1;
	}
	c->connected = false;
}

void tls_conn_free(struct tls_conn *c)
{
	if(c == NULL)
		return;
	conn_close(c);
	free(c);
}

// Monotonic clock in milliseconds, for the exchange deadline.
static uint64_t now_ms(void)
{
	struct timespec ts;
	clock_gettime(CLOCK_MONOTONIC, &ts);
	return (uint64_t)ts.tv_sec * 1000u + (uint64_t)ts.tv_nsec / 1000000u;
}

// Milliseconds left until deadline, clamped to [0, cap].
static int ms_left(uint64_t deadline, int cap)
{
	const uint64_t n = now_ms();
	if(n >= deadline)
		return 0;
	const uint64_t left = deadline - n;
	return left < (uint64_t)cap ? (int)left : cap;
}

// Bounded, non-blocking TCP connect returning a connected socket in *out_fd. A
// plain blocking connect() has no timeout, so a black-holed upstream (dropped
// SYN) would pin the single worker thread for the kernel's full SYN timeout
// (~2 min) and stall every other encrypted upstream with it. Connect
// non-blocking and poll() for the deadline instead, then restore blocking mode
// for the OpenSSL I/O.
static int net_connect_timeout(int *out_fd, const char *host,
                               const char *port, int timeout_ms)
{
	struct addrinfo hints = { 0 };
	hints.ai_family = AF_UNSPEC;
	hints.ai_socktype = SOCK_STREAM;
	hints.ai_protocol = IPPROTO_TCP;

	struct addrinfo *res = NULL;
	if(getaddrinfo(host, port, &hints, &res) != 0)
		return -1;

	// timeout_ms is the budget for the whole connect, not per address: share
	// the remaining time across every A/AAAA record rather than restarting the
	// full timeout for each, so a multi-homed host cannot blow the deadline.
	const uint64_t deadline = now_ms() + (uint64_t)timeout_ms;

	int ret = -1;
	for(struct addrinfo *cur = res; cur != NULL; cur = cur->ai_next)
	{
		// SOCK_CLOEXEC so a connected upstream socket is not inherited across
		// FTL's execvp() self-restart.
		const int fd = socket(cur->ai_family, cur->ai_socktype | SOCK_CLOEXEC, cur->ai_protocol);
		if(fd < 0)
			continue;

		// Non-blocking connect, then wait for writability within the deadline.
		const int flags = fcntl(fd, F_GETFL, 0);
		if(flags < 0)
		{
			close(fd);
			continue;
		}
		fcntl(fd, F_SETFL, flags | O_NONBLOCK);

		struct pollfd pfd = { .fd = fd, .events = POLLOUT };
		int soerr = 0;
		socklen_t sl = sizeof(soerr);
		if((connect(fd, cur->ai_addr, cur->ai_addrlen) == 0 || errno == EINPROGRESS) &&
		   poll(&pfd, 1, ms_left(deadline, timeout_ms)) == 1 && (pfd.revents & POLLOUT) &&
		   getsockopt(fd, SOL_SOCKET, SO_ERROR, &soerr, &sl) == 0 && soerr == 0)
		{
			fcntl(fd, F_SETFL, flags); // restore blocking mode for OpenSSL I/O
			*out_fd = fd;
			ret = 0;
			break;
		}
		close(fd);
	}

	freeaddrinfo(res);
	return ret;
}

// Open a TCP connection and drive the TLS handshake to the upstream described
// by u. Returns true only once the connection is verified and ready. deadline
// bounds the connect and handshake so a stalled peer cannot pin the worker.
static bool conn_connect(struct tls_conn *c, const struct upstream_uri *u, uint64_t deadline)
{
	c->fd = -1;
	c->ssl = NULL;

	// net_connect_timeout() wants the port as a string.
	char portstr[8];
	snprintf(portstr, sizeof(portstr), "%d", u->port);

	if(net_connect_timeout(&c->fd, u->connect_host, portstr,
	                       ms_left(deadline, TLS_CONNECT_TIMEOUT_MS)) != 0)
	{
		log_warn("dotdoh: connect to %s#%d failed", u->connect_host, u->port);
		goto fail;
	}

	// Bound blocking reads and sends: the socket has no timeout of its own, so
	// without these a peer that stops sending (or stops reading, once its
	// receive window fills) would block SSL_read()/SSL_write() forever. On a
	// timeout the call returns an error and the exchange fails over.
	const struct timeval to = { .tv_sec = TLS_READ_TIMEOUT_MS / 1000,
	                            .tv_usec = (TLS_READ_TIMEOUT_MS % 1000) * 1000 };
	setsockopt(c->fd, SOL_SOCKET, SO_RCVTIMEO, &to, sizeof(to));
	setsockopt(c->fd, SOL_SOCKET, SO_SNDTIMEO, &to, sizeof(to));

	c->ssl = SSL_new(g_ctx);
	if(c->ssl == NULL)
		goto fail;

	// verify_name is the hostname the certificate is checked against and the
	// SNI sent to the server. For a pinned "sni-host@ip" upstream this is the
	// hostname, not the IP, so verification still matches the real cert.
	// SSL_set1_host() ties the (fail-closed) chain verification to this name.
	if(SSL_set1_host(c->ssl, u->verify_name) != 1)
		goto fail;
	SSL_set_tlsext_host_name(c->ssl, u->verify_name);

	if(SSL_set_fd(c->ssl, c->fd) != 1)
		goto fail;

	// Blocking sockets should not normally yield WANT_READ/WANT_WRITE, but the
	// socket read timeout can surface them; loop until the handshake resolves
	// or the deadline passes. A verification failure (bad chain or hostname)
	// returns a hard error here, which is exactly the fail-closed behaviour.
	int rc;
	while((rc = SSL_connect(c->ssl)) != 1)
	{
		const int err = SSL_get_error(c->ssl, rc);
		if(err != SSL_ERROR_WANT_READ && err != SSL_ERROR_WANT_WRITE)
		{
			log_warn("dotdoh: TLS handshake with %s (%s#%d) failed",
			         u->verify_name, u->connect_host, u->port);
			goto fail;
		}
		if(now_ms() >= deadline)
		{
			log_warn("dotdoh: TLS handshake with %s (%s#%d) timed out",
			         u->verify_name, u->connect_host, u->port);
			goto fail;
		}
	}

	c->connected = true;
	return true;

fail:
	// We never reached the "connected" state, so free the half-initialised
	// objects directly rather than via conn_close().
	if(c->ssl != NULL)
	{
		SSL_free(c->ssl);
		c->ssl = NULL;
	}
	if(c->fd >= 0)
	{
		close(c->fd);
		c->fd = -1;
	}
	c->connected = false;
	return false;
}

// Write the whole buffer, tolerating short writes and the transient
// WANT_READ/WANT_WRITE conditions. Returns true once everything is sent.
static bool ssl_write_all(struct tls_conn *c, const uint8_t *buf, size_t len, uint64_t deadline)
{
	size_t off = 0;
	while(off < len)
	{
		const int w = SSL_write(c->ssl, buf + off, (int)(len - off));
		if(w > 0)
		{
			off += (size_t)w;
			continue;
		}
		const int err = SSL_get_error(c->ssl, w);
		if(err == SSL_ERROR_WANT_READ || err == SSL_ERROR_WANT_WRITE)
		{
			if(now_ms() >= deadline)
				return false;
			continue;
		}
		return false;
	}
	return true;
}

// Send one query and read back the framed answer over the established
// connection. Returns the answer length, or -1 on any protocol/transport error
// (which makes the caller drop and, once, rebuild the connection).
static ssize_t conn_do(struct tls_conn *c, const struct upstream_uri *u,
                       const uint8_t *query, size_t qlen,
                       uint8_t *answer, size_t answer_sz, uint64_t deadline)
{
	// Frame the request: DoT prepends a 2-byte length, DoH wraps it in a
	// POST.
	ssize_t reqlen;
	if(u->type == UST_DOT)
		reqlen = dot_frame(query, qlen, c->req, sizeof(c->req));
	else
		reqlen = doh_build_request(u->verify_name, u->doh_path, query, qlen, c->req, sizeof(c->req));
	if(reqlen < 0)
		return -1;

	if(!ssl_write_all(c, c->req, (size_t)reqlen, deadline))
		return -1;

	// Accumulate the response until the framer says a full message is
	// present. The buffer is bounded, so a misbehaving upstream cannot make
	// us grow it.
	uint8_t *buf = c->rbuf;
	const size_t bufcap = sizeof(c->rbuf);
	size_t have = 0;
	for(;;)
	{
		// Bounds both a full buffer and a peer that trickles a byte at a time:
		// such reads return r > 0 and would otherwise loop until the buffer
		// fills (many hours) without ever hitting the WANT_READ deadline below.
		if(have >= bufcap || now_ms() >= deadline)
			return -1;
		const int r = SSL_read(c->ssl, buf + have, (int)(bufcap - have));
		if(r <= 0)
		{
			// TLS 1.3 delivers post-handshake messages (e.g. a
			// NewSessionTicket, which the upstream sends right after the
			// handshake, before our answer) to SSL_read() as WANT_READ once
			// it has consumed them without app data. That is not an error -
			// just read again for the actual response.
			const int err = SSL_get_error(c->ssl, r);
			if(err == SSL_ERROR_WANT_READ || err == SSL_ERROR_WANT_WRITE)
				continue; // deadline is enforced at the top of the loop
			return -1; // timeout, close_notify or hard error
		}
		have += (size_t)r;

		size_t off = 0, blen = 0;
		if(u->type == UST_DOT)
		{
			const ssize_t m = dot_deframe(buf, have, &off);
			if(m < 0)
				return -1;
			if(m > 0)
			{
				if((size_t)m > answer_sz)
					return -1;
				memcpy(answer, buf + off, (size_t)m);
				return m;
			}
		}
		else
		{
			const ssize_t consumed = doh_parse_response(buf, have, &off, &blen);
			if(consumed < 0)
				return -1;
			if(consumed > 0)
			{
				if(blen > answer_sz)
					return -1;
				memcpy(answer, buf + off, blen);
				return (ssize_t)blen;
			}
		}
		// Otherwise we need more bytes; loop and read again.
	}
}

ssize_t tls_exchange(struct tls_conn *c, const struct upstream_uri *u,
                     const uint8_t *query, size_t qlen,
                     uint8_t *answer, size_t answer_sz)
{
	if(!g_ready || c == NULL || u == NULL)
		return -1;

	// Two attempts at most: a pooled keep-alive connection the upstream
	// closed while idle is transparently rebuilt once. A second failure is
	// real and we give up (fail-closed) rather than retry forever.
	// One overall budget for the whole exchange (both attempts share it) so a
	// stalled connect, handshake, read or write cannot pin the single worker
	// thread and starve every other encrypted upstream.
	const uint64_t deadline = now_ms() + TLS_EXCHANGE_TIMEOUT_MS;

	for(int attempt = 0; attempt < 2; attempt++)
	{
		if(!c->connected && !conn_connect(c, u, deadline))
			continue;

		const ssize_t r = conn_do(c, u, query, qlen, answer, answer_sz, deadline);
		if(r >= 0)
			return r;

		conn_close(c);
	}
	return -1;
}

#else // !HAVE_TLS

// Without TLS there is no TLS client; encrypted upstreams are unavailable
// and every exchange fails closed. The config layer refuses to enable them.
// These trivial stubs are const-folding candidates, so GCC raises
// -Wsuggest-attribute=const; the attribute cannot be applied (it conflicts with
// tls_conn_new()'s malloc attribute), so silence the suggestion here. clang
// does not have this warning, hence the GCC-only guard.
#if defined(__GNUC__) && !defined(__clang__)
#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wsuggest-attribute=const"
#endif
bool tls_client_global_init(const char *ca_file) { (void)ca_file; return false; }
void tls_client_global_free(void) { }
struct tls_conn *tls_conn_new(void) { return NULL; }
void tls_conn_free(struct tls_conn *c) { (void)c; }
ssize_t tls_exchange(struct tls_conn *c, const struct upstream_uri *u,
                     const uint8_t *query, size_t qlen,
                     uint8_t *answer, size_t answer_sz)
{
	(void)c; (void)u; (void)query; (void)qlen; (void)answer; (void)answer_sz;
	return -1;
}
#if defined(__GNUC__) && !defined(__clang__)
#pragma GCC diagnostic pop
#endif

#endif // HAVE_TLS
