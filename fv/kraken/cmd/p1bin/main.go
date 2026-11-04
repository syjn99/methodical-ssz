// Command p1bin links the generated phase 1a methods into an ELF (fv/kraken: amd64).
// It calls them through interfaces held in package variables, so the
// compiler keeps each method as a standalone symbol and does not inline it.
//
// With the argument -test it reads one case per line from stdin and prints
// one result line per case (semtest/fnrun.sh runs this ELF under qemu).
//
//	<T> S                    -> "<T> S <size>"
//	<T> M <value hex> <len> <cap> -> "<T> M <out hex> <len> <cap> <err>"
//	<T> U <buf hex|->         -> "<T> U <err> <value hex>"
//
// <T> is SC (Scalars), FV (FixedVec) or LU (ListU64). <value hex> is the
// SSZ encoding of the value to marshal (it is decoded by the test driver
// without the code under test, see setValue).
package main

import (
	"bufio"
	"encoding/binary"
	"encoding/hex"
	"errors"
	"fmt"
	"os"
	"strconv"
	"strings"

	"github.com/OffchainLabs/methodical-ssz/fv/kraken/target"
	"github.com/OffchainLabs/methodical-ssz/ssz"
)

type codec interface {
	MarshalSSZTo([]byte) ([]byte, error)
	UnmarshalSSZ([]byte) error
	SizeSSZ() int
}

// Package variables so the compiler cannot devirtualize the calls.
var (
	sc       = &target.Scalars{}
	fv       = &target.FixedVec{}
	lu       = &target.ListU64{}
	codecs   = map[string]codec{"SC": sc, "FV": fv, "LU": lu}
	errNames = []struct {
		e error
		n string
	}{
		{ssz.ErrSize, "ErrSize"}, {ssz.ErrInvalidSerialization, "ErrInvalidSerialization"},
		{ssz.ErrInvalidVariableOffset, "ErrInvalidVariableOffset"}, {ssz.ErrOffset, "ErrOffset"},
		{ssz.ErrIncorrectListSize, "ErrIncorrectListSize"}, {ssz.ErrListTooBig, "ErrListTooBig"},
		{ssz.ErrBytesLength, "ErrBytesLength"},
	}
)

func errName(err error) string {
	if err == nil {
		return "nil"
	}
	for _, x := range errNames {
		if err == x.e {
			return x.n
		}
	}
	for _, x := range errNames {
		if errors.Is(err, x.e) {
			return "wrap:" + x.n
		}
	}
	return "other"
}

func unhex(s string) []byte {
	if s == "-" {
		return []byte{}
	}
	b, err := hex.DecodeString(s)
	if err != nil {
		panic(err)
	}
	return b
}

// setValue sets the receiver from a value description, independent of the
// code under test: SC = A B C D E as fixed-width little-endian fields,
// FV = R then W, LU = the list elements (8 bytes each).
func setValue(t string, b []byte) {
	le := binary.LittleEndian
	switch t {
	case "SC":
		sc.A, sc.B, sc.C, sc.D, sc.E = b[0], le.Uint16(b[1:]), le.Uint32(b[3:]), le.Uint64(b[7:]), b[15] != 0
	case "FV":
		copy(fv.R[:], b[:32])
		fv.W = make([]uint64, (len(b)-32)/8)
		for i := range fv.W {
			fv.W[i] = le.Uint64(b[32+8*i:])
		}
	case "LU":
		lu.L = make([]uint64, len(b)/8)
		for i := range lu.L {
			lu.L[i] = le.Uint64(b[8*i:])
		}
	}
}

func value(t string) []byte {
	le := binary.LittleEndian
	var b []byte
	switch t {
	case "SC":
		e := byte(0)
		if sc.E {
			e = 1
		}
		b = append(b, sc.A)
		b = le.AppendUint16(b, sc.B)
		b = le.AppendUint32(b, sc.C)
		b = le.AppendUint64(b, sc.D)
		b = append(b, e)
	case "FV":
		b = append(b, fv.R[:]...)
		for _, w := range fv.W {
			b = le.AppendUint64(b, w)
		}
	case "LU":
		for _, w := range lu.L {
			b = le.AppendUint64(b, w)
		}
	}
	return b
}

func runTests() {
	in := bufio.NewScanner(os.Stdin)
	in.Buffer(make([]byte, 1<<20), 1<<20)
	out := bufio.NewWriter(os.Stdout)
	defer out.Flush()
	for in.Scan() {
		w := strings.Fields(in.Text())
		t, c := w[0], codecs[w[0]]
		switch w[1] {
		case "S":
			setValue(t, unhex(w[2]))
			fmt.Fprintf(out, "%s S %d\n", t, c.SizeSSZ())
		case "M":
			setValue(t, unhex(w[2]))
			n, _ := strconv.Atoi(w[3])
			k, _ := strconv.Atoi(w[4])
			dst := make([]byte, n, k)
			for i := range dst {
				dst[i] = byte(i*7 + 1)
			}
			res, err := c.MarshalSSZTo(dst)
			fmt.Fprintf(out, "%s M %s %d %s\n", t, hex.EncodeToString(res), len(res), errName(err))
		case "U":
			err := c.UnmarshalSSZ(unhex(w[2]))
			v := "-"
			if err == nil {
				v = hex.EncodeToString(value(t))
			}
			fmt.Fprintf(out, "%s U %s %s\n", t, errName(err), v)
		}
	}
	if err := in.Err(); err != nil {
		panic(err)
	}
}

func main() {
	if len(os.Args) > 1 && os.Args[1] == "-test" {
		runTests()
		return
	}
	for _, c := range codecs {
		out, _ := c.MarshalSSZTo(make([]byte, 0, 4))
		if err := c.UnmarshalSSZ(out); err != nil || c.SizeSSZ() != len(out) {
			os.Exit(1)
		}
	}
}
