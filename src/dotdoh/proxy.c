/* Pi-hole: A black hole for Internet advertisements
*  (c) 2026 Pi-hole, LLC (https://pi-hole.net)
*  Network-wide ad blocking via your own hardware.
*
*  FTL Engine
*  Encrypted-upstream forward proxy
*
*  FTL forwards plaintext DNS to a loopback address in 127.47.11.0/24; this
*  module re-encrypts it to the real resolver over DoT/DoH and hands the answer
*  back. A pool of worker threads shares the armed listeners; each borrows a
*  connection from the per-upstream pool for the exchange, so many queries run
*  concurrently and one slow upstream cannot stall the others. On any TLS failure
*  the query is dropped, not answered, so FTL fails over to the next server
*  instead of ever downgrading to plaintext.
*
*  This file is copyright under the latest version of the EUPL.
*  Please see LICENSE file for your rights under this license. */

#include "FTL.h"
#include "log.h"
// killed, thread_names
#include "signals.h"

#include "proxy.h"
#include "registry.h"
#include "tls_client.h"
#include "framing.h"
#include "edns_pad.h"
// global config
#include "config/config.h"
// upstream list iteration
#include "webserver/cJSON/cJSON.h"

#include <poll.h>
#include <sys/socket.h>
#include <netinet/in.h>
#include <arpa/inet.h>
#include <sys/prctl.h>
#include <sys/sysinfo.h>
#include <unistd.h>
#include <errno.h>
#include <string.h>
#include <stdlib.h>
#include <time.h>
#include <fcntl.h>
#include <pthread.h>

// Per-upstream state, one entry per encrypted upstream. Plaintext entries are
// not tracked here - dnsmasq talks to those directly.
struct proxy_up {
	bool active;                    // armed: listener bound and pool ready
	struct upstream_uri uri;        // parsed descriptor
	struct proxy_listener listener; // bound UDP+TCP pair
	struct tls_pool *pool;          // per-upstream connection pool
	char target[INET_ADDRSTRLEN + 8]; // "127.47.11.N#P", for logging
};

static struct proxy_up g_ups[DOTDOH_MAX_UPSTREAMS];
static int g_nups = 0;       // number of encrypted upstreams recorded
static int g_nactive = 0;    // number of those successfully armed
static bool g_armed = false; // init runs once per process

// Auto-scaled worker pool. Workers are I/O-bound, so we run more than one per
// core; each per-upstream connection pool is capped separately. Both are derived
// once from the hardware in compute_scale(), never user-configured.
#define WORKERS_MIN   4
#define WORKERS_MAX   64
#define POOLCONN_MIN   2
#define POOLCONN_MAX  32
static pthread_t g_workers[WORKERS_MAX];
static int g_nworkers = 0;
static int g_pool_k = POOLCONN_MIN;

// Tuple -> upstream lookup, precomputed once at arm time so the per-query hot
// path (findUpstreamID) is an O(1) array access, not a config walk + URI parse.
static char g_uri_map[DOTDOH_MAX_UPSTREAMS][256];
static int  g_uri_port[DOTDOH_MAX_UPSTREAMS];
static int  g_uri_count = 0;

// Monotonic clock in milliseconds, for the per-request deadline and the stats
// summary interval.
static uint64_t now_ms(void)
{
	struct timespec ts;
	clock_gettime(CLOCK_MONOTONIC, &ts);
	return (uint64_t)ts.tv_sec * 1000u + (uint64_t)ts.tv_nsec / 1000000u;
}

// Derive the worker count and per-upstream connection cap from the hardware,
// with a RAM guard so a low-memory box cannot be pushed into swapping by a high
// core count. Each connection costs roughly ~170 KiB (buffers + OpenSSL state);
// we keep the total connection budget under ~5% of physical RAM.
static void compute_scale(int nupstreams)
{
	int ncpu = get_nprocs();
	if(ncpu < 1)
		ncpu = 1;

	int w = 4 * ncpu;
	if(w < WORKERS_MIN) w = WORKERS_MIN;
	if(w > WORKERS_MAX) w = WORKERS_MAX;

	int k = 2 * ncpu;
	if(k < POOLCONN_MIN) k = POOLCONN_MIN;
	if(k > POOLCONN_MAX) k = POOLCONN_MAX;

	struct sysinfo si;
	if(nupstreams > 0 && sysinfo(&si) == 0)
	{
		const uint64_t ram = (uint64_t)si.totalram * si.mem_unit;
		const uint64_t budget = (ram / 20u) / (170u * 1024u); // 5% / ~170 KiB
		int kmax = (int)(budget / (uint64_t)nupstreams);
		if(kmax < POOLCONN_MIN)
			kmax = POOLCONN_MIN;
		if(k > kmax)
			k = kmax;
	}

	g_nworkers = w;
	g_pool_k = k;
}

// Put a listener fd in non-blocking mode so many workers can share the poll set:
// after poll() wakes them all, the losers of the recvfrom()/accept4() race get
// EAGAIN instead of blocking.
static void set_nonblock(int fd)
{
	const int flags = fcntl(fd, F_GETFL, 0);
	if(flags >= 0)
		fcntl(fd, F_SETFL, flags | O_NONBLOCK);
}

static void *worker_main(void *val);

// Arm one loopback listener pair per encrypted upstream, build its connection
// pool, and start the shared worker threads. Runs exactly once per process,
// after dnsmasq startup so the freshly bound listener fds cannot collide with
// dnsmasq's.
void dotdoh_init(void)
{
	// Arm exactly once per process (upstreams are RESTART_FTL, so the set
	// cannot change without a full restart).
	if(g_armed)
		return;
	g_armed = true;

	cJSON *ups = config.dns.upstreams.v.json;
	if(ups == NULL || cJSON_GetArraySize(ups) <= 0)
		return;

	// Count encrypted upstreams first: the TLS stack is only brought up if at
	// least one exists, and the count feeds the RAM guard in compute_scale().
	int n_encrypted = 0;
	cJSON *it = NULL;
	cJSON_ArrayForEach(it, ups)
		if(it != NULL && cJSON_IsString(it) && it->valuestring != NULL &&
		   (strncmp(it->valuestring, "tls://", 6) == 0 || strncmp(it->valuestring, "https://", 8) == 0))
			n_encrypted++;
	if(n_encrypted == 0)
		return; // fail-closed: nothing to arm, no plaintext fallback

	const bool tls_ok = tls_client_global_init(config.dns.upstreamCA.v.s);
	if(!tls_ok)
		log_err("dotdoh: TLS init failed - encrypted upstreams are disabled");

	compute_scale(n_encrypted);

	// Walk the upstreams in order. Each encrypted entry consumes one slot in the
	// 127.47.11.N addressing (enc), matching the deterministic tuple the config
	// layer already emitted for it - so a disabled entry still keeps subsequent
	// ones aligned.
	int enc = 0;
	cJSON_ArrayForEach(it, ups)
	{
		if(it == NULL || !cJSON_IsString(it) || it->valuestring == NULL)
			continue;

		struct upstream_uri u;
		if(!parse_upstream_uri(it->valuestring, &u) || u.type == UST_PLAIN)
			continue; // plaintext -> dnsmasq handles it directly

		if(g_nups >= DOTDOH_MAX_UPSTREAMS)
			break;

		// Record the tuple->upstream mapping (tuple 127.47.11.(enc+1)) so the
		// API can resolve it without re-walking the config per query.
		strncpy(g_uri_map[enc], it->valuestring, sizeof(g_uri_map[enc]) - 1);
		g_uri_map[enc][sizeof(g_uri_map[enc]) - 1] = '\0';
		g_uri_port[enc] = u.port;
		g_uri_count = enc + 1;

		struct proxy_up *up = &g_ups[g_nups++];
		memset(up, 0, sizeof(*up));
		up->uri = u;

		// Deterministic tuple; no iteration, since dnsmasq is already pointed at
		// exactly this address. If we cannot own it, the upstream is left
		// disabled and queries to it fail closed (dnsmasq fails over).
		if(tls_ok && proxy_listener_bind(enc, &up->listener))
		{
			up->pool = tls_pool_new(&u, g_pool_k);
			if(up->pool != NULL)
			{
				snprintf(up->target, sizeof(up->target), "%s#%d",
				         up->listener.ip, up->listener.port);
				up->active = true;
				g_nactive++;
				log_info("dotdoh: %s upstream %s armed on %s",
				         u.type == UST_DOT ? "DoT" : "DoH", u.verify_name, up->target);
			}
			else
				proxy_listener_close(&up->listener);
		}
		if(!up->active)
			log_warn("dotdoh: encrypted upstream %s could not be armed (127.47.11.%d#%d)",
			         u.verify_name, enc + 1, DOTDOH_PORT_BASE + enc + 1);
		enc++;
	}

	if(g_nactive == 0)
		return;

	// Share the armed listeners across the worker pool: make them non-blocking
	// and spawn the workers. If a spawn fails we still run with the workers we
	// have (or none, in which case queries fail closed).
	for(int i = 0; i < g_nups; i++)
	{
		if(!g_ups[i].active)
			continue;
		set_nonblock(g_ups[i].listener.udp_fd);
		set_nonblock(g_ups[i].listener.tcp_fd);
	}

	for(int i = 0; i < g_nworkers; i++)
	{
		if(pthread_create(&g_workers[i], NULL, worker_main, NULL) != 0)
		{
			log_err("dotdoh: could not start worker %d/%d", i + 1, g_nworkers);
			g_nworkers = i; // only the ones we actually started
			break;
		}
	}
	log_info("dotdoh: %d encrypted upstream(s) armed, %d worker(s), up to %d conn(s) each",
	         g_nactive, g_nworkers, g_pool_k);
}

int dotdoh_count(void)
{
	return g_nactive;
}

bool dotdoh_uri_for_listener(const char *ip, int port, char *out, size_t outlen, int *real_port)
{
	if(ip == NULL || out == NULL || outlen == 0)
		return false;

	// Cheap prefix check first, so plaintext upstreams (the common case) cost
	// almost nothing on the per-query hot path.
	const size_t plen = strlen(DOTDOH_NET_PREFIX);
	if(strncmp(ip, DOTDOH_NET_PREFIX, plen) != 0)
		return false;
	char *end = NULL;
	const long n = strtol(ip + plen, &end, 10);
	if(end == NULL || *end != '\0' || n < 1 || n > g_uri_count ||
	   port != DOTDOH_PORT_BASE + (int)n)
		return false;

	// O(1) lookup in the table dotdoh_init() precomputed - tuple N maps to the
	// N-th encrypted upstream, the same numbering the dnsmasq.conf emission uses.
	strncpy(out, g_uri_map[n - 1], outlen - 1);
	out[outlen - 1] = '\0';
	if(real_port != NULL)
		*real_port = g_uri_port[n - 1];
	return true;
}

// True for an IPv4 loopback source (127.0.0.0/8). Everything else is rejected:
// only dnsmasq on this host is a legitimate client, and this also closes any
// exposure via net.ipv4.conf.*.route_localnet.
static bool is_loopback_v4(const struct sockaddr_in *sa)
{
	return sa->sin_family == AF_INET &&
	       (ntohl(sa->sin_addr.s_addr) >> 24) == 127;
}

// Overall budget (ms) for one TCP request cycle (read query + write answer).
#define PROXY_REQUEST_TIMEOUT_MS 10000

// Per-connection caps so a single accepted TCP connection cannot monopolize a
// worker thread (the loopback listener is reachable by any local process, not
// just dnsmasq). Generous enough for dnsmasq's pipelining; on hitting either the
// connection is closed and dnsmasq reconnects.
#define PROXY_CONN_MAX_QUERIES 64
#define PROXY_CONN_TIMEOUT_MS  60000

// Read exactly len bytes (or fail), giving up once deadline passes.
static bool read_full(int fd, uint8_t *buf, size_t len, uint64_t deadline)
{
	size_t off = 0;
	while(off < len)
	{
		if(now_ms() >= deadline)
			return false;
		const ssize_t r = read(fd, buf + off, len - off);
		if(r < 0 && errno == EINTR)
			continue;
		if(r <= 0)
			return false;
		off += (size_t)r;
	}
	return true;
}

// Write exactly len bytes (or fail), giving up once deadline passes.
static bool write_full(int fd, const uint8_t *buf, size_t len, uint64_t deadline)
{
	size_t off = 0;
	while(off < len)
	{
		if(now_ms() >= deadline)
			return false;
		const ssize_t w = write(fd, buf + off, len - off);
		if(w < 0 && errno == EINTR)
			continue;
		if(w <= 0)
			return false;
		off += (size_t)w;
	}
	return true;
}

// A single UDP query from dnsmasq: receive, forward over TLS, send the answer
// back to the same source. On failure we drop it (see the file header).
static void handle_udp(struct proxy_up *up)
{
	// 64 KiB each - too large for the worker's thread stack, declared
	// thread-local instead (one set per worker thread).
	static _Thread_local uint8_t query[DNS_MSG_MAX];
	static _Thread_local uint8_t answer[DNS_MSG_MAX];
	struct sockaddr_in src;
	socklen_t sl = sizeof(src);
	// Non-blocking listener: another worker may have taken the datagram, in
	// which case recvfrom() returns EAGAIN (n < 0) and we simply return.
	const ssize_t n = recvfrom(up->listener.udp_fd, query, sizeof(query), 0,
	                           (struct sockaddr *)&src, &sl);
	if(n <= 0)
		return;
	if(!is_loopback_v4(&src))
		return;

	// Pad the query to a block boundary (RFC 8467) before it is encrypted, so the
	// ciphertext size no longer leaks the query. Only this encrypted leg is
	// padded; the plaintext dnsmasq spoke to us over loopback is left untouched.
	const size_t qlen = edns_pad_query(query, (size_t)n, sizeof(query));
	const ssize_t a = tls_pool_exchange(up->pool, query, qlen, answer, sizeof(answer));
	if(a < 0)
		return; // drop -> dnsmasq times out and fails over

	sendto(up->listener.udp_fd, answer, (size_t)a, 0, (struct sockaddr *)&src, sl);
}

// A TCP connection from dnsmasq: length-prefixed queries in, length-prefixed
// answers out, until the peer closes or something fails.
static void handle_tcp(struct proxy_up *up)
{
	struct sockaddr_in peer;
	socklen_t pl = sizeof(peer);
	// accept4() with SOCK_CLOEXEC: the flag is not inherited from the listening
	// socket, so without it the accepted fd would leak across FTL's execvp()
	// self-restart. A non-blocking listener may return EAGAIN if another worker
	// won the accept - just return.
	const int cfd = accept4(up->listener.tcp_fd, (struct sockaddr *)&peer, &pl, SOCK_CLOEXEC);
	if(cfd < 0)
		return;
	if(!is_loopback_v4(&peer))
	{
		close(cfd);
		return;
	}

	// Bound how long we wait on this connection so a stalled peer cannot pin a
	// worker thread. Both directions are bounded: without SO_SNDTIMEO a peer that
	// stops reading would block write_full() forever.
	const struct timeval tv = { .tv_sec = 5, .tv_usec = 0 };
	setsockopt(cfd, SOL_SOCKET, SO_RCVTIMEO, &tv, sizeof(tv));
	setsockopt(cfd, SOL_SOCKET, SO_SNDTIMEO, &tv, sizeof(tv));

	// See handle_udp(): keep these 64 KiB buffers off the thread stack.
	static _Thread_local uint8_t query[DNS_MSG_MAX];
	static _Thread_local uint8_t answer[DNS_MSG_MAX];
	static _Thread_local uint8_t out[2 + DNS_MSG_MAX];
	// Bound one connection's hold on a worker thread: any local process can reach
	// the loopback listener, so without this a peer could stream valid queries
	// forever and starve other work. Cap both the total lifetime and the query
	// count; dnsmasq simply reconnects.
	const uint64_t conn_deadline = now_ms() + PROXY_CONN_TIMEOUT_MS;
	int served = 0;
	for(;;)
	{
		if(served >= PROXY_CONN_MAX_QUERIES || now_ms() >= conn_deadline)
			break;

		// Separate read and write budgets, each fresh: the upstream exchange
		// between them has its own deadline, so sharing one budget could let a
		// slow-but-valid exchange expire it before the answer is even written.
		const uint64_t rdeadline = now_ms() + PROXY_REQUEST_TIMEOUT_MS;

		uint8_t lenbuf[2];
		if(!read_full(cfd, lenbuf, 2, rdeadline))
			break;
		const size_t qlen = ((size_t)lenbuf[0] << 8) | (size_t)lenbuf[1];
		if(qlen == 0 || qlen > DNS_MSG_MAX)
			break;

		if(!read_full(cfd, query, qlen, rdeadline))
			break;

		// Pad before encrypting (see handle_udp()); the loopback leg stays plain.
		const size_t plen = edns_pad_query(query, qlen, sizeof(query));
		const ssize_t a = tls_pool_exchange(up->pool, query, plen, answer, sizeof(answer));
		if(a < 0)
			break; // drop: closing the connection makes dnsmasq retry/fail over

		out[0] = (uint8_t)(((size_t)a >> 8) & 0xff);
		out[1] = (uint8_t)((size_t)a & 0xff);
		memcpy(out + 2, answer, (size_t)a);
		const uint64_t wdeadline = now_ms() + PROXY_REQUEST_TIMEOUT_MS;
		if(!write_full(cfd, out, (size_t)a + 2, wdeadline))
			break;
		served++;
	}
	close(cfd);
}

// Periodic per-upstream keep-alive/resumption summary, emitted only under
// debug.dotdoh. Single-flighted so exactly one worker prints per interval. The
// interval is short because it only fires when the (verbose) debug flag is on.
#define SUMMARY_INTERVAL_MS 10000
static pthread_mutex_t g_summary_lock = PTHREAD_MUTEX_INITIALIZER;
static uint64_t g_last_summary_ms = 0;

static void emit_summary(void)
{
	for(int i = 0; i < g_nups; i++)
	{
		if(!g_ups[i].active || g_ups[i].pool == NULL)
			continue;
		struct dotdoh_stats s;
		tls_pool_get_stats(g_ups[i].pool, &s);
		const double avg = s.sessions_closed > 0
		                 ? (double)s.queries_per_session_sum / (double)s.sessions_closed : 0.0;
		log_debug(DEBUG_DOTDOH,
		          "dotdoh[%s]: queries=%llu sessions=%llu avg_reuse=%.1f max_reuse=%llu "
		          "resumed=%llu fresh_cold=%llu full_fallback=%llu opened=%llu reaped=%llu dead_on_reuse=%llu",
		          g_ups[i].uri.verify_name, s.queries_total, s.sessions_closed, avg,
		          s.queries_per_session_max, s.handshakes_resumed, s.handshakes_fresh_cold,
		          s.handshakes_full_fallback, s.conns_opened, s.conns_reaped_idle,
		          s.conns_dead_on_reuse);
	}
}

static void maybe_emit_summary(void)
{
	if(!debug_flags[DEBUG_DOTDOH])
		return;
	if(pthread_mutex_trylock(&g_summary_lock) != 0)
		return; // another worker is handling this tick
	const uint64_t now = now_ms();
	if(now - g_last_summary_ms >= SUMMARY_INTERVAL_MS)
	{
		g_last_summary_ms = now;
		emit_summary();
	}
	pthread_mutex_unlock(&g_summary_lock);
}

// Worker entry: poll every armed listener and service whatever is ready, sharing
// the listeners with the other workers. The armed set never changes after init,
// so the poll set is built once.
static void *worker_main(void *val)
{
	(void)val;
	prctl(PR_SET_NAME, thread_names[DOTDOH], 0, 0, 0);

	struct pollfd fds[2 * DOTDOH_MAX_UPSTREAMS];
	struct proxy_up *owner[2 * DOTDOH_MAX_UPSTREAMS];
	bool is_tcp[2 * DOTDOH_MAX_UPSTREAMS];
	nfds_t n = 0;
	for(int i = 0; i < g_nups; i++)
	{
		if(!g_ups[i].active)
			continue;
		fds[n].fd = g_ups[i].listener.udp_fd; fds[n].events = POLLIN; owner[n] = &g_ups[i]; is_tcp[n] = false; n++;
		fds[n].fd = g_ups[i].listener.tcp_fd; fds[n].events = POLLIN; owner[n] = &g_ups[i]; is_tcp[n] = true;  n++;
	}

	while(!killed)
	{
		const int r = poll(fds, n, 1000);
		if(r <= 0)
		{
			maybe_emit_summary(); // timeout or interrupt: housekeeping, re-check killed
			continue;
		}
		for(nfds_t k = 0; k < n; k++)
		{
			if(!(fds[k].revents & POLLIN))
				continue;
			if(is_tcp[k])
				handle_tcp(owner[k]);
			else
				handle_udp(owner[k]);
		}
	}
	return NULL;
}

void dotdoh_cleanup(void)
{
	// Stop the worker pool first: the process-wide `killed` flag is already set
	// by terminate_threads() before cleanup() calls us, so the workers are on
	// their way out (they re-check it every poll timeout). Break them out of a
	// blocking poll by shutting the listeners, then join. A plain join is safe
	// here: every worker blocking point is deadline-bounded (poll 1 s, an
	// in-flight exchange <=10 s), so this returns promptly without pthread_cancel
	// - which could re-lock a pool mutex from inside a condition wait and then
	// deadlock the teardown below.
	killed = true;
	for(int i = 0; i < g_nups; i++)
		if(g_ups[i].active)
		{
			shutdown(g_ups[i].listener.udp_fd, SHUT_RDWR);
			shutdown(g_ups[i].listener.tcp_fd, SHUT_RDWR);
		}
	for(int i = 0; i < g_nworkers; i++)
		pthread_join(g_workers[i], NULL);
	g_nworkers = 0;

	// A final statistics summary on the way out, if anyone is watching.
	if(debug_flags[DEBUG_DOTDOH])
		emit_summary();

	// Now no worker touches the pools; tear them down.
	for(int i = 0; i < g_nups; i++)
	{
		if(g_ups[i].pool != NULL)
			tls_pool_free(g_ups[i].pool);
		if(g_ups[i].active)
			proxy_listener_close(&g_ups[i].listener);
		memset(&g_ups[i], 0, sizeof(g_ups[i]));
	}
	g_nups = 0;
	g_nactive = 0;
	g_armed = false;
	g_uri_count = 0;
	tls_client_global_free();
}
