#!/bin/bash

echo "************ Installing PowerDNS configuration ************"

# Delete possibly existing zone database
mkdir -p /var/lib/powerdns/
rm /var/lib/powerdns/pdns.sqlite3 2> /dev/null

# Install config files
if [ -d /etc/powerdns ]; then
  # Debian
  cp test/pdns/pdns.conf /etc/powerdns/pdns.conf
  RECURSOR_CONF=/etc/powerdns/recursor.conf
elif [ -d /etc/pdns ]; then
  cp test/pdns/pdns.conf /etc/pdns/pdns.conf
  if [ -d /etc/pdns-recursor ]; then
    # Fedora
    RECURSOR_CONF=/etc/pdns-recursor/recursor.conf
  else
    # Alpine
    RECURSOR_CONF=/etc/pdns/recursor.conf
  fi
else
  echo "Error: Unable to determine powerDNS config directory"
  exit 1
fi

cp test/pdns/luadns.lua /etc/pdns/luadns.lua
cp test/pdns/recursor.conf $RECURSOR_CONF

# Create zone database
if [ -f /usr/share/doc/pdns-backend-sqlite3/schema.sqlite3.sql ]; then
  # Debian
  ./pihole-FTL sqlite3 /var/lib/powerdns/pdns.sqlite3 < /usr/share/doc/pdns-backend-sqlite3/schema.sqlite3.sql
elif [ -f /usr/share/doc/pdns/schema.sqlite3.sql ]; then
  # Alpine
  ./pihole-FTL sqlite3 /var/lib/powerdns/pdns.sqlite3 < /usr/share/doc/pdns/schema.sqlite3.sql
else
  echo "Error: powerDNS SQL schema not found"
  exit 1
fi
# Create zone ftl
pdnsutil create-zone ftl ns1.ftl
pdnsutil disable-dnssec ftl

# Create A records
pdnsutil add-record ftl. a A 192.168.1.1
pdnsutil add-record ftl. gravity A 192.168.1.2
pdnsutil add-record ftl. denied A 192.168.1.3
pdnsutil add-record ftl. allowed A 192.168.1.4
pdnsutil add-record ftl. gravity-allowed A 192.168.1.5
pdnsutil add-record ftl. antigravity A 192.168.1.6
pdnsutil add-record ftl. x.y.z.abp.antigravity A 192.168.1.7
pdnsutil add-record ftl. regex1 A 192.168.2.1
pdnsutil add-record ftl. regex2 A 192.168.2.2
pdnsutil add-record ftl. regex5 A 192.168.2.3
pdnsutil add-record ftl. regexA A 192.168.2.4
pdnsutil add-record ftl. regex-REPLYv4 A 192.168.2.5
pdnsutil add-record ftl. regex-REPLYv6 A 192.168.2.6
pdnsutil add-record ftl. regex-REPLYv46 A 192.168.2.7
pdnsutil add-record ftl. regex-A A 192.168.2.8
pdnsutil add-record ftl. regex-notA A 192.168.2.9
pdnsutil add-record ftl. any A 192.168.3.1

# Create AAAA records
pdnsutil add-record ftl. aaaa AAAA fe80::1c01
pdnsutil add-record ftl. regex-REPLYv4 AAAA fe80::2c01
pdnsutil add-record ftl. regex-REPLYv6 AAAA fe80::2c02
pdnsutil add-record ftl. regex-REPLYv46 AAAA fe80::2c03
pdnsutil add-record ftl. any AAAA fe80::3c01
pdnsutil add-record ftl. gravity-aaaa AAAA fe80::4c01

# Create CNAME records
pdnsutil add-record ftl. cname-1 CNAME gravity.ftl
pdnsutil add-record ftl. cname-2 CNAME cname-1.ftl
pdnsutil add-record ftl. cname-3 CNAME cname-2.ftl
pdnsutil add-record ftl. cname-4 CNAME cname-3.ftl
pdnsutil add-record ftl. cname-5 CNAME cname-4.ftl
pdnsutil add-record ftl. cname-6 CNAME cname-5.ftl
pdnsutil add-record ftl. cname-7 CNAME cname-6.ftl
pdnsutil add-record ftl. cname-ok CNAME a.ftl

# Create CNAME for SOA test domain
pdnsutil add-record ftl. soa CNAME ftl

# Create CNAME for NODATA tests
pdnsutil add-record ftl. aaaa-cname CNAME gravity-aaaa.ftl
pdnsutil add-record ftl. a-cname CNAME gravity.ftl

# Create PTR records
pdnsutil add-record ftl. ptr PTR ptr.ftl.

# Other testing records
pdnsutil add-record ftl. srv SRV "0 1 80 a.ftl"
pdnsutil add-record ftl. txt TXT "\"Some example text\""
# We want this to output $1 without expansion
# shellcheck disable=SC2016
pdnsutil add-record ftl. naptr NAPTR '10 10 "u" "smtp+E2U" "!.*([^\.]+[^\.]+)$!mailto:postmaster@$1!i" .'
pdnsutil add-record ftl. naptr NAPTR '20 10 "s" "http+N2L+N2C+N2R" "" ftl.'
pdnsutil add-record ftl. mx MX "50 ns1.ftl."

# SVCB + HTTPS
pdnsutil add-record ftl. svcb SVCB '1 port="80"'
pdnsutil add-record ftl. regex-multiple SVCB '1 port="80"'
pdnsutil add-record ftl. regex-notMultiple SVCB '1 port="80"'

# HTTPS
pdnsutil add-record ftl. https HTTPS '1 . alpn="h3,h2"'
pdnsutil add-record ftl. regex-multiple HTTPS '1 . alpn="h3,h2"'
pdnsutil add-record ftl. regex-notMultiple HTTPS '1 . alpn="h3,h2"'

# ANY
pdnsutil add-record ftl. regex-multiple A 192.168.3.12
pdnsutil add-record ftl. regex-multiple AAAA fe80::3f41
pdnsutil add-record ftl. regex-notMultiple A 192.168.3.12
pdnsutil add-record ftl. regex-notMultiple AAAA fe80::3f41

# TXT
pdnsutil add-record ftl. any TXT "\"Some example text\""

# NOERROR
pdnsutil add-record ftl. noerror A

# Blocked Cisco Umbrella IP (https://support.opendns.com/hc/en-us/articles/227986927-What-are-the-Cisco-Umbrella-Block-Page-IP-Addresses)
pdnsutil add-record ftl. umbrella A 146.112.61.104
pdnsutil add-record ftl. umbrella AAAA ::ffff:146.112.61.104

# Special record which consists of both blocked and non-blocked IP
pdnsutil add-record ftl. umbrella-multi A 1.2.3.4
pdnsutil add-record ftl. umbrella-multi A 146.112.61.104
pdnsutil add-record ftl. umbrella-multi A 8.8.8.8

# Null address
pdnsutil add-record ftl. null A 0.0.0.0
pdnsutil add-record ftl. null AAAA ::

# Create valid internal DNSSEC zone
pdnsutil create-zone dnssec ns1.ftl
pdnsutil add-record dnssec. a A 192.168.4.1
pdnsutil add-record dnssec. aaaa AAAA fe80::4c01
pdnsutil secure-zone dnssec
# Export zone DS records and convert to dnsmasq trust-anchor format
# Example:
#   dnssec. IN DS 42206 8 2 6d2007e292483fa061db37011676d9592649d1600e5b2ece1326f792ebedd412 ; ( SHA256 digest )
# --->
#   trust-anchor=dnssec.,42206,8,2,6d2007e292483fa061db37011676d9592649d1600e5b2ece1326f792ebedd412
pdnsutil export-zone-ds dnssec. | head -n1 | awk '{FS=" "; OFS=""; print "trust-anchor=",$1,",",$4,",",$5,",",$6,",",$7}' > /etc/dnsmasq.d/02-trust-anchor.conf

# Create intentionally broken DNSSEC (BOGUS) zone
# The only difference to above is that this zone is signed with a key that is
# not in the trust chain
# It will cause the DNSSEC validation to fail with error message:
#   unsupported DS digest
pdnsutil create-zone bogus ns1.ftl
pdnsutil add-record bogus. a A 192.168.5.1
pdnsutil add-record bogus. aaaa AAAA fe80::5c01
pdnsutil secure-zone bogus

# Create reverse lookup zone
pdnsutil create-zone arpa ns1.ftl
pdnsutil add-record arpa. 1.1.168.192.in-addr PTR ftl.
pdnsutil add-record arpa. 2.1.168.192.in-addr PTR a.ftl.
pdnsutil add-record arpa. 1.0.c.1.0.0.0.0.0.0.0.0.0.0.0.0.0.0.0.0.0.0.0.0.0.0.0.0.0.8.e.f.ip6 PTR ftl.
pdnsutil add-record arpa. 2.0.c.1.0.0.0.0.0.0.0.0.0.0.0.0.0.0.0.0.0.0.0.0.0.0.0.0.0.8.e.f.ip6 PTR aaaa.ftl.

# Calculates the ‘ordername’ and ‘auth’ fields for all zones so they comply with
# DNSSEC settings. Can be used to fix up migrated data. Can always safely be
# run, it does no harm.
pdnsutil rectify-all-zones

# Do final checking
pdnsutil check-zone ftl
pdnsutil check-zone arpa

pdnsutil list-all-zones

echo "********* Done installing PowerDNS configuration **********"

# Start services
killall pdns_server
pdns_server --daemon
# Have to create the socketdir or the recursor will fails to start
mkdir -p /var/run/pdns-recursor
killall pdns_recursor
pdns_recursor --daemon
