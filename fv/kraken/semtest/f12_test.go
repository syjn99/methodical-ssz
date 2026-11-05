// Package semtest checks findings F1 and F2 at the Go level (any
// architecture). The amd64 hardware comparison is run.sh (x86-64 Linux only).
//
// Before the generator fix (698c202), F1 and F2 were counterexamples: the
// decoder accepted 0x10 and the encoder accepted 258 bytes. Those tests are
// in commit 37efd44. The tests below are regression tests for the rejects.
package semtest

import (
	"bytes"
	"testing"

	"github.com/OffchainLabs/methodical-ssz/fv/kraken/target"
)

// F1: the BitVec decoder (Bitvector[4], one byte) accepts exactly b < 0x10.
// EthLib: Fk.bv_spec_accepts_iff. Machine code: Fk.bv_accept_main (b < 16),
// Fk.bv_reject_padding_main (16 <= b).
func TestF1BitvectorPadding(t *testing.T) {
	for b := range 256 {
		var v target.BitVec
		err := v.UnmarshalSSZ([]byte{byte(b)})
		if b < 0x10 && err != nil {
			t.Errorf("decoder rejects %#02x: %v", b, err)
		}
		if b >= 0x10 && err == nil {
			t.Errorf("decoder accepts %#02x (padding bit set)", b)
		}
		if b < 0x10 && err == nil && !bytes.Equal(v.J, []byte{byte(b)}) {
			t.Errorf("decoder gives %x for %#02x", v.J, b)
		}
	}
}

// F2: Bitlist[2048]. The rule is Fk.blValid_iff: 1 <= n <= 257 bytes, the last
// byte is not 0, and if n = 257 then the last byte is 1. Encoder:
// Fk.bl_marshal_main, Fk.bl_marshal_reject_main,
// Fk.bl_marshal_overlong_rejected (258 bytes), Fk.bl_marshal_rejects_overlong.
func TestF2BitlistByteLimit(t *testing.T) {
	zeros := func(n int, last ...byte) []byte { return append(bytes.Repeat([]byte{0}, n), last...) }
	cases := []struct {
		name string
		b    []byte
		ok   bool
	}{
		{"empty bitlist [1]", []byte{1}, true},
		{"2047 bits", zeros(255, 0xff), true},
		{"2048 bits", zeros(256, 1), true},
		{"2049 bits", zeros(256, 2), false},
		{"258 bytes (F2 input)", zeros(257, 1), false},
		{"no delimiter [0]", []byte{0}, false},
		{"no bytes []", []byte{}, false},
	}
	for _, c := range cases {
		out, err := (&target.BitL{B: c.b}).MarshalSSZTo(nil)
		if c.ok != (err == nil) {
			t.Errorf("%s: encoder error %v, want ok=%v", c.name, err, c.ok)
		}
		if c.ok && !bytes.Equal(out, append([]byte{4, 0, 0, 0}, c.b...)) {
			t.Errorf("%s: encoder output %x", c.name, out)
		}
		var v target.BitL
		err = v.UnmarshalSSZ(append([]byte{4, 0, 0, 0}, c.b...))
		if c.ok != (err == nil) {
			t.Errorf("%s: decoder error %v, want ok=%v", c.name, err, c.ok)
		}
		if c.ok && !bytes.Equal(v.B, c.b) {
			t.Errorf("%s: decoder gives %x", c.name, v.B)
		}
	}
}
