package fuzz

import (
	"encoding/binary"
	"math/bits"
	"reflect"
	"strconv"
	"strings"
	"testing"

	"github.com/OffchainLabs/methodical-ssz/fuzz/oracle"
	eth "github.com/OffchainLabs/prysm/v7/proto/prysm/v1alpha1"
)

// A fuzz input that starts with valuePrefix holds no SSZ bytes. It tells how
// to change a value: decode base number data[0], apply the changes in
// data[1:], encode the value with MarshalSSZ and give the bytes to EthLib.
// This tests MarshalSSZ and HashTreeRoot on values that no decode gives.
var valuePrefix = []byte("value:")

// mutated decodes the base that ops[0] selects and applies the changes in
// ops[1:]. Each change takes 3 bytes: the site (uint16, little endian, modulo
// the number of sites) and the argument of change.
func mutated[T any, P interface {
	*T
	codec
}](bases [][]byte, ops []byte) P {
	if len(ops) == 0 {
		ops = []byte{0}
	}
	obj := P(new(T))
	if err := obj.UnmarshalSSZ(bases[int(ops[0])%len(bases)]); err != nil {
		panic(err) // run keeps only the bases that decode
	}
	for ops = ops[1:]; len(ops) >= 3; ops = ops[3:] {
		all := sites(reflect.ValueOf(obj), nil) // a change can replace slices, so collect again
		if len(all) == 0 {
			break
		}
		change(all[int(binary.LittleEndian.Uint16(ops))%len(all)], ops[2])
	}
	return obj
}

// checkValue checks the encoding of a changed value, which MarshalSSZ gave.
// EthLib must accept it, and HashTreeRoot must give the EthLib root.
func checkValue(t *testing.T, obj codec, enc []byte, fork, name string) {
	v, want, msg := oracle.SszStatic(preset, fork, name, enc)
	signal(v)
	root, err := obj.HashTreeRoot()
	if v != oracle.Accept {
		differ(t, "%s/%s: MarshalSSZ gives bytes that EthLib rejects (HashTreeRoot error: %v): %s", fork, name, err, msg)
	}
	if err != nil || root != want {
		differ(t, "%s/%s: root of a changed value differs: methodical %x (error: %v), EthLib %x", fork, name, root, err, want)
	}
}

// site is a slice in a value: a list, a vector, a byte string or a bitfield.
type site struct {
	v     reflect.Value
	max   int   // ssz-max of this dimension, 0 if none
	size  int   // ssz-size of this dimension, 0 if none
	inner []int // ssz-size of the dimensions below, for new elements
}

// sites lists the slices in the struct that v points to, depth first.
func sites(v reflect.Value, out []site) []site {
	if v.Kind() != reflect.Pointer || v.IsNil() || v.Elem().Kind() != reflect.Struct {
		return out
	}
	s := v.Elem()
	for i := 0; i < s.NumField(); i++ {
		if f := s.Type().Field(i); f.IsExported() {
			out = sliceSites(s.Field(i), dims(f.Tag.Get("ssz-max")), dims(f.Tag.Get("ssz-size")), out)
		}
	}
	return out
}

func sliceSites(v reflect.Value, max, size []int, out []site) []site {
	if v.Kind() == reflect.Pointer {
		return sites(v, out)
	}
	if v.Kind() != reflect.Slice {
		return out
	}
	out = append(out, site{v, max[0], size[0], size[1:]})
	if k := v.Type().Elem().Kind(); k == reflect.Pointer || k == reflect.Slice {
		for i := 0; i < v.Len(); i++ {
			out = sliceSites(v.Index(i), append(max[1:], 0), append(size[1:], 0), out)
		}
	}
	return out
}

// dims reads an ssz-max or ssz-size tag. "?" and "" give 0.
func dims(tag string) []int {
	var d []int
	for _, s := range strings.Split(tag, ",") {
		n, _ := strconv.Atoi(s)
		d = append(d, n)
	}
	return d
}

// change sets a new length for the slice, chosen by a>>1 among lengths at the
// edges of its type. For a bitfield with a&1 set, it flips one bit instead,
// counted from the last bit, so that padding bits and the delimiter come first.
func change(s site, a byte) {
	v, n := s.v, s.v.Len()
	name := v.Type().Name()
	if strings.HasPrefix(name, "Bit") && a&1 == 1 && n > 0 {
		i := 8*n - 1 - int(a>>1)%(8*n)
		v.Index(i / 8).SetUint(v.Index(i/8).Uint() ^ 1<<(i%8))
		return
	}
	a >>= 1
	if name == "Bitlist" { // a new bit length, all bits clear
		length := 0
		if n > 0 && v.Index(n-1).Uint() != 0 {
			length = 8*(n-1) + bits.Len8(uint8(v.Index(n-1).Uint())) - 1
		}
		k := []int{0, 1, length - 1, length + 1, s.max - 1, s.max, s.max + 1, s.max + 7, s.max + 8}[int(a)%9]
		if k >= 0 {
			b := make([]byte, k/8+1)
			b[k/8] = 1 << (k % 8)
			v.SetBytes(b)
		}
		return
	}
	var lengths []int
	if s.max > 0 {
		lengths = []int{0, 1, n - 1, n + 1, s.max, s.max + 1}
	}
	if s.size > 0 {
		lengths = []int{0, s.size - 1, s.size + 1}
	}
	if lengths == nil {
		return
	}
	k := lengths[int(a)%len(lengths)]
	elem := int(v.Type().Elem().Size())
	for _, d := range s.inner {
		elem *= max(d, 1)
	}
	// ponytail: skip lengths above 16 MB, so huge limits (validators,
	// transactions, blobs) never reach max+1. The size of a struct element
	// counts as one pointer.
	if k < 0 || k*elem > 1<<24 {
		return
	}
	w := reflect.MakeSlice(v.Type(), k, k)
	reflect.Copy(w, v)
	for i := n; i < k; i++ {
		fillField(w.Index(i), s.inner)
	}
	v.Set(w)
}

func TestChange(t *testing.T) {
	a := new(eth.AttestationElectra)
	fill(reflect.ValueOf(a).Elem())
	bitlist := sites(reflect.ValueOf(a), nil)[0] // AggregationBits
	change(bitlist, 6<<1)                        // max+1 bits
	if n := bitlist.max + 1; len(a.AggregationBits) != n/8+1 || a.AggregationBits[n/8] != 1<<(n%8) {
		t.Fatalf("want a bitlist of %d bits, got %d bytes", n, len(a.AggregationBits))
	}
	change(sites(reflect.ValueOf(a), nil)[0], 6<<1|1) // flip bit 6 from the top: the delimiter
	if a.AggregationBits[len(a.AggregationBits)-1] != 0 {
		t.Fatal("the delimiter is still set")
	}
	i := new(eth.IndexedAttestationElectra)
	fill(reflect.ValueOf(i).Elem())
	list := sites(reflect.ValueOf(i), nil)[0] // AttestingIndices
	change(list, 5<<1)                        // max+1 elements
	if len(i.AttestingIndices) != list.max+1 {
		t.Fatalf("want %d elements, got %d", list.max+1, len(i.AttestingIndices))
	}
}
