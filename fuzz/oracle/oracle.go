// Package oracle calls EthLib's SSZ specification in process.
// Build flags come from the environment, see ../ethlib.sh.
package oracle

// #include <stdlib.h>
// #include "oracle.h"
import "C"

import (
	"fmt"
	"runtime"
	"unsafe"
)

// Verdict is what EthLib says about the bytes of one container.
type Verdict int

const (
	Accept Verdict = C.ETHLIB_ACCEPT
	Reject Verdict = C.ETHLIB_REJECT
	// Unsupported is EthLib's code 0: it holds no such container at the fork,
	// or it could not read the arguments. It says nothing about the bytes.
	Unsupported Verdict = C.ETHLIB_UNSUPPORTED
)

type result struct {
	verdict Verdict
	root    [32]byte
	out     []byte // re-encoding on Accept, message otherwise
}

type request struct {
	preset, fork, typ string
	data              []byte
	reply             chan result
}

var requests = make(chan request)

// The Lean runtime keeps per-thread state, so one locked thread makes every call.
func init() {
	go func() {
		runtime.LockOSThread()
		if C.ethlib_init() != 1 {
			panic("oracle: EthLib initialization failed")
		}
		for r := range requests {
			r.reply <- call(r.preset, r.fork, r.typ, r.data)
		}
	}()
}

func call(preset, fork, typ string, data []byte) result {
	cpreset, cfork, ctyp := C.CString(preset), C.CString(fork), C.CString(typ)
	defer C.free(unsafe.Pointer(cpreset))
	defer C.free(unsafe.Pointer(cfork))
	defer C.free(unsafe.Pointer(ctyp))
	out := make([]byte, len(data)+256)
	n := C.size_t(len(out))
	var res result
	v := C.ethlib_ssz_static(cpreset, cfork, ctyp, (*C.uint8_t)(unsafe.SliceData(data)), C.size_t(len(data)),
		(*C.uint8_t)(&res.root[0]), (*C.uint8_t)(&out[0]), &n)
	if v == C.ETHLIB_BROKEN {
		panic(fmt.Sprintf("oracle: unexpected result shape for %s/%s", fork, typ))
	}
	res.verdict, res.out = Verdict(v), out[:n]
	return res
}

// SszStatic decodes data as the container `typ` of `fork` at `preset`.
// On Accept it returns the hash tree root and the re-encoding.
// Otherwise out holds EthLib's message.
func SszStatic(preset, fork, typ string, data []byte) (v Verdict, root [32]byte, out []byte) {
	r := request{preset, fork, typ, data, make(chan result)}
	requests <- r
	res := <-r.reply
	return res.verdict, res.root, res.out
}
