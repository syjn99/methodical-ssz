// Package semtest reproduces findings F1 and F2 at the Go level (any
// architecture). The amd64 hardware comparison is run.sh (x86-64 Linux only).
package semtest

import (
	"bytes"
	"testing"

	"github.com/OffchainLabs/methodical-ssz/fv/kraken/target"
)

// F1: the BitVec decoder accepts a byte with a padding bit set (EthLib:
// paddingBits, Fv1.bv_spec_rejects_padding; Fk.bv_padding_counterexample).
func TestF1BitvectorPadding(t *testing.T) {
	var v target.BitVec
	if err := v.UnmarshalSSZ([]byte{0x10}); err != nil {
		t.Fatalf("F1 not reproduced: decoder rejects 0x10: %v", err)
	}
}

// F2: BitL.MarshalSSZTo checks len(c.B) > 2048 in bytes, so a 258-byte
// bitlist (2056 bits) encodes with a nil error; the same type's decoder
// rejects the output (EthLib: Fv1.bl_spec_rejects_overlong; Fk.bl_marshal_overlong).
func TestF2BitlistByteLimit(t *testing.T) {
	b := append(bytes.Repeat([]byte{0}, 257), 1)
	out, err := (&target.BitL{B: b}).MarshalSSZTo(nil)
	if err != nil {
		t.Fatalf("F2 not reproduced: encoder rejects: %v", err)
	}
	if len(out) != 4+258 {
		t.Fatalf("unexpected length %d", len(out))
	}
	if err := new(target.BitL).UnmarshalSSZ(out); err == nil {
		t.Fatal("decoder accepts its own over-limit output")
	}
}
