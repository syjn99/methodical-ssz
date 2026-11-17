package fuzz

import "github.com/OffchainLabs/methodical-ssz/fuzz/oracle"

// signal gives accept and each SSZ decode error, codes 1 to 20 of EthLib's
// Err (EthLib/Serialization/Ssz/Error.lean), its own branch. The Go fuzzer sees
// only the coverage of Go code, so this makes an input that reaches a new
// EthLib rejection reason new coverage. The compiler gives each case body its
// own coverage counter, also an empty body (walk/order.go, orderBlock).
// Higher codes name errors of declarations, proofs and JSON. They share the
// default branch.
func signal(v oracle.Verdict) {
	switch v {
	case 0:
	case 1:
	case 2:
	case 3:
	case 4:
	case 5:
	case 6:
	case 7:
	case 8:
	case 9:
	case 10:
	case 11:
	case 12:
	case 13:
	case 14:
	case 15:
	case 16:
	case 17:
	case 18:
	case 19:
	case 20:
	default:
	}
}
