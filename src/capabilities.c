/* Pi-hole: A black hole for Internet advertisements
*  (c) 2017 Pi-hole, LLC (https://pi-hole.net)
*  Network-wide ad blocking via your own hardware.
*
*  FTL Engine
*  Linux capability check routines
*
*  This file is copyright under the latest version of the EUPL.
*  Please see LICENSE file for your rights under this license. */

// Definition of LINUX_CAPABILITY_VERSION_*
#define FTLDNS
#include "dnsmasq/dnsmasq.h"
#undef __USE_XOPEN
#include "FTL.h"
#include "capabilities.h"
#include "config/config.h"
#include "log.h"

static const unsigned int capabilityIDs[]   = { CAP_CHOWN ,  CAP_DAC_OVERRIDE ,  CAP_DAC_READ_SEARCH ,  CAP_FOWNER ,  CAP_FSETID ,  CAP_KILL ,  CAP_SETGID ,  CAP_SETUID ,  CAP_SETPCAP ,  CAP_LINUX_IMMUTABLE ,  CAP_NET_BIND_SERVICE ,  CAP_NET_BROADCAST ,  CAP_NET_ADMIN ,  CAP_NET_RAW ,  CAP_IPC_LOCK ,  CAP_IPC_OWNER ,  CAP_SYS_MODULE ,  CAP_SYS_RAWIO ,  CAP_SYS_CHROOT ,  CAP_SYS_PTRACE ,  CAP_SYS_PACCT ,  CAP_SYS_ADMIN ,  CAP_SYS_BOOT ,  CAP_SYS_NICE ,  CAP_SYS_RESOURCE ,  CAP_SYS_TIME ,  CAP_SYS_TTY_CONFIG ,  CAP_MKNOD ,  CAP_LEASE ,  CAP_AUDIT_WRITE ,  CAP_AUDIT_CONTROL ,  CAP_SETFCAP };
static const char*        capabilityNames[] = {"CAP_CHOWN", "CAP_DAC_OVERRIDE", "CAP_DAC_READ_SEARCH", "CAP_FOWNER", "CAP_FSETID", "CAP_KILL", "CAP_SETGID", "CAP_SETUID", "CAP_SETPCAP", "CAP_LINUX_IMMUTABLE", "CAP_NET_BIND_SERVICE", "CAP_NET_BROADCAST", "CAP_NET_ADMIN", "CAP_NET_RAW", "CAP_IPC_LOCK", "CAP_IPC_OWNER", "CAP_SYS_MODULE", "CAP_SYS_RAWIO", "CAP_SYS_CHROOT", "CAP_SYS_PTRACE", "CAP_SYS_PACCT", "CAP_SYS_ADMIN", "CAP_SYS_BOOT", "CAP_SYS_NICE", "CAP_SYS_RESOURCE", "CAP_SYS_TIME", "CAP_SYS_TTY_CONFIG", "CAP_MKNOD", "CAP_LEASE", "CAP_AUDIT_WRITE", "CAP_AUDIT_CONTROL", "CAP_SETFCAP"};

/**
 * @brief Retrieves the capabilities of the current process.
 *
 * This function determines the capabilities version used by the current kernel
 * and retrieves the current capabilities of the process.
 *
 * @param data Pointer to a cap_user_data_t structure where the capabilities
 *             will be stored. The memory for this structure is allocated within
 *             the function and should be freed by the caller.
 */
static bool get_caps(cap_user_data_t *data)
{
	cap_user_header_t hdr = calloc(1, sizeof(*hdr));

	// Determine capabilities version used by the current kernel
	if(capget(hdr, NULL) != 0)
	{
		log_err("Failed to retrieve capabilities header: %s", strerror(errno));
		free(hdr);
		return false;
	}

	// Get size of capabilities
	int capsize = 1; // VFS_CAP_U32_1
	if (hdr->version != LINUX_CAPABILITY_VERSION_1)
	{
		// If unknown version, use largest supported version (3)
		// Version 2 is deprecated according to linux/capability.h
		if (hdr->version != LINUX_CAPABILITY_VERSION_2)
		{
			hdr->version = LINUX_CAPABILITY_VERSION_3;
			capsize = 2; // VFS_CAP_U32_3
		}
		else
		{
			// Use version 2
			capsize = 2; // VFS_CAP_U32_2
		}
	}

	// Get current capabilities
	*data = calloc(capsize, sizeof(**data));
	if(capget(hdr, *data) != 0)
	{
		log_err("Failed to retrieve capabilities data: %s", strerror(errno));
		free(hdr);
		free(*data);
		return false;
	}

	// Free allocated memory
	free(hdr);

	return true;
}

/**
 * @brief Checks if a specific capability is available.
 *
 * This function retrieves the current capabilities of the process and checks if
 * the specified capability is both permitted and effective.
 *
 * @param cap The capability to check.
 * @return true if the capability is available, false otherwise.
 */
bool check_capability(const unsigned int cap)
{
	cap_user_data_t data = NULL;
	if(!get_caps(&data))
		return false;

	// Check if the capability is available
	const bool available = ((data->permitted & (1 << cap)) && (data->effective & (1 << cap)));

	// Free memory
	free(data);

	return available;
}

/**
 * @brief Checks the required Linux capabilities for the application.
 *
 * This function retrieves the current Linux capabilities and logs the status of
 * each capability. It then checks if the necessary capabilities for the
 * application are available and logs warnings if any required capability is
 * missing.
 *
 * @return true if all required capabilities are available, false otherwise.
 */
bool check_capabilities(void)
{
	cap_user_data_t data = NULL;
	if(!get_caps(&data))
		return false;

	log_debug(DEBUG_CAPS, "***************************************");
	log_debug(DEBUG_CAPS, "* Linux capability debugging enabled  *");
	for(unsigned int i = 0u; i < ArraySize(capabilityIDs); i++)
	{
		const unsigned int capid = capabilityIDs[i];
		log_debug(DEBUG_CAPS, "* %-24s (%02u) = %s%s%s *",
			capabilityNames[capid], capid,
			((data->permitted   & (1 << capid)) ? "P":"-"),
			((data->inheritable & (1 << capid)) ? "I":"-"),
			((data->effective   & (1 << capid)) ? "E":"-"));
	}
	log_debug(DEBUG_CAPS, "***************************************");

	bool capabilities_okay = true;
	if (!(data->permitted & (1 << CAP_NET_ADMIN)) ||
	    !(data->effective & (1 << CAP_NET_ADMIN)))
	{
		// Needed for ARP-injection (used when we're the DHCP server)
		log_warn("Required Linux capability CAP_NET_ADMIN not available");
		capabilities_okay = false;
	}
	if (!(data->permitted & (1 << CAP_NET_RAW)) ||
	    !(data->effective & (1 << CAP_NET_RAW)))
	{
		// Needed for raw socket access (necessary for ICMP)
		log_warn("Required Linux capability CAP_NET_RAW not available");
		capabilities_okay = false;
	}
	if (!(data->permitted & (1 << CAP_NET_BIND_SERVICE)) ||
	    !(data->effective & (1 << CAP_NET_BIND_SERVICE)))
	{
		// Necessary for dynamic port binding
		log_warn("Required Linux capability CAP_NET_BIND_SERVICE not available");
		capabilities_okay = false;
	}
	if (!(data->permitted & (1 << CAP_SYS_NICE)) ||
	    !(data->effective & (1 << CAP_SYS_NICE)))
	{
		// Necessary for setting higher process priority through nice
		log_warn("Required Linux capability CAP_SYS_NICE not available");
		capabilities_okay = false;
	}
	if (!(data->permitted & (1 << CAP_CHOWN)) ||
	    !(data->effective & (1 << CAP_CHOWN)))
	{
		// Necessary to chown required files that are owned by another user
		log_warn("Required Linux capability CAP_CHOWN not available");
		capabilities_okay = false;
	}
	if (!(data->permitted & (1 << CAP_SYS_TIME)) ||
	    !(data->effective & (1 << CAP_SYS_TIME)))
	{
		// Necessary for setting the system time in the NTP client
		log_warn("Required Linux capability CAP_SYS_TIME not available");
		capabilities_okay = false;
	}

	// Free allocated memory
	free(data);

	// Return whether capabilities are all okay
	return capabilities_okay;
}
