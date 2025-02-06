/* Pi-hole: A black hole for Internet advertisements
*  (c) 2025 Pi-hole, LLC (https://pi-hole.net)
*  Network-wide ad blocking via your own hardware.
*
*  FTL Engine
*  Version-related hard-coded strings
*
*  This file is copyright under the latest version of the EUPL.
*  Please see LICENSE file for your rights under this license. */

#include "version.h"

const char * __attribute__ ((const)) git_version(void)
{
	return "v5.25.2-2605-g04807af5";
}

const char * __attribute__ ((const)) git_date(void)
{
	return "2025-02-06 16:01:57 +0000";
}
const char * __attribute__ ((const)) git_branch(void)
{
	return "update/dnsmasq";
}
const char * __attribute__ ((const)) git_tag(void)
{
	return "v5.25.2";
}

const char * __attribute__ ((const)) git_hash(void)
{
	return "04807af5";
}

const char * __attribute__ ((const)) ftl_arch(void)
{
	return "x86_64 (compiled locally)";
}

const char * __attribute__ ((const)) ftl_cc(void)
{
	return "cc (Ubuntu 13.3.0-6ubuntu2~24.04) 13.3.0";
}
