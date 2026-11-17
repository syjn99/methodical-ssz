#include <stddef.h>
#include <stdint.h>

enum {
	ETHLIB_ACCEPT = 0,      // root and out hold the root and the re-encoding
	ETHLIB_REJECT = 1,      // EthLib rejects the bytes, out holds the message
	ETHLIB_UNSUPPORTED = 2, // EthLib code 0: no verdict, out holds the message
	ETHLIB_BROKEN = 3,      // the export returned a shape the shim does not know
};

// Starts the Lean runtime on the calling thread. Returns 1 on success.
int ethlib_init(void);

// Runs eth_consensus_ssz_static(preset, fork, type, data).
// out has room for *out_len bytes; *out_len returns the bytes written.
int ethlib_ssz_static(const char *preset, const char *fork, const char *type, const uint8_t *data, size_t n,
                      uint8_t root[32], uint8_t *out, size_t *out_len);
