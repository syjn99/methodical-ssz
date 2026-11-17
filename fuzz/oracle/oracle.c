// C shim around EthLib's `eth_consensus_ssz_static` export.
// The export takes and returns a PyValue (EthLib/Base/Exports/PyValueCore.lean).
#include "oracle.h"
#include <lean/lean.h>
#include <string.h>

extern void lean_initialize_runtime_module(void);
extern lean_object *runtime_initialize_EthLib_EthLib_Consensus_Exports_Ssz(uint8_t builtin);
extern lean_object *eth_consensus_ssz_static(lean_object *args);

// Constructor indices of PyValue.
enum { PV_BYTES = 4, PV_STR = 5, PV_TUPLE = 7 };

static lean_object *pv(unsigned tag, lean_object *field) {
	lean_object *o = lean_alloc_ctor(tag, 1, 0);
	lean_ctor_set(o, 0, field);
	return o;
}

int ethlib_init(void) {
	lean_initialize_runtime_module();
	lean_object *res = runtime_initialize_EthLib_EthLib_Consensus_Exports_Ssz(1);
	int ok = lean_io_result_is_ok(res);
	lean_dec(res);
	lean_io_mark_end_initialization();
	return ok;
}

// A borrowed ByteArray out of a PyValue.bytes, or NULL.
static lean_object *pv_bytes(lean_object *v) {
	if (lean_is_scalar(v) || lean_obj_tag(v) != PV_BYTES) return NULL;
	return lean_ctor_get(v, 0);
}

int ethlib_ssz_static(const char *preset, const char *fork, const char *type, const uint8_t *data, size_t n,
                      uint8_t root[32], uint8_t *out, size_t *out_len) {
	lean_object *bytes = lean_alloc_sarray(1, n, n);
	memcpy(lean_sarray_cptr(bytes), data, n);
	lean_object *items = lean_alloc_array(4, 4);
	lean_array_set_core(items, 0, pv(PV_STR, lean_mk_string(preset)));
	lean_array_set_core(items, 1, pv(PV_STR, lean_mk_string(fork)));
	lean_array_set_core(items, 2, pv(PV_STR, lean_mk_string(type)));
	lean_array_set_core(items, 3, pv(PV_BYTES, bytes));
	lean_object *res = eth_consensus_ssz_static(pv(PV_TUPLE, items));

	int status = ETHLIB_BROKEN;
	if (lean_obj_tag(res) == 0) { // Except.error (code, message)
		lean_object *pair = lean_ctor_get(res, 0);
		lean_object *msg = lean_ctor_get(pair, 1);
		size_t len = lean_string_size(msg) - 1;
		if (len > *out_len) len = *out_len;
		memcpy(out, lean_string_cstr(msg), len);
		*out_len = len;
		// Code 0: no such container, fork or argument. Codes >= 1: the SSZ error.
		status = lean_unbox_uint32(lean_ctor_get(pair, 0)) == 0 ? ETHLIB_UNSUPPORTED : ETHLIB_REJECT;
	} else { // Except.ok (PyValue.tuple #[bytes root, bytes encoding])
		lean_object *v = lean_ctor_get(res, 0);
		lean_object *r = NULL, *e = NULL;
		if (!lean_is_scalar(v) && lean_obj_tag(v) == PV_TUPLE && lean_array_size(lean_ctor_get(v, 0)) == 2) {
			r = pv_bytes(lean_array_get_core(lean_ctor_get(v, 0), 0));
			e = pv_bytes(lean_array_get_core(lean_ctor_get(v, 0), 1));
		}
		// The encoding of an accepted input has the length of the input, or
		// the oracle and the harness disagree anyway.
		if (r && e && lean_sarray_size(r) == 32 && lean_sarray_size(e) <= *out_len) {
			memcpy(root, lean_sarray_cptr(r), 32);
			*out_len = lean_sarray_size(e);
			memcpy(out, lean_sarray_cptr(e), *out_len);
			status = ETHLIB_ACCEPT;
		} else {
			*out_len = 0;
		}
	}
	lean_dec(res);
	return status;
}
