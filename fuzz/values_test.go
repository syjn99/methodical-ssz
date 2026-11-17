package fuzz

import (
	"encoding/binary"
	"fmt"
	"math/bits"
	"reflect"
	"runtime"
	"slices"
	"strconv"
	"strings"
	"testing"

	"github.com/OffchainLabs/methodical-ssz/fuzz/oracle"
	eth "github.com/OffchainLabs/prysm/v7/proto/prysm/v1alpha1"
)

// A fuzz input that starts with valuePrefix also tells how to change a value:
// decode base number data[0], apply the changes in data[1:], encode the value
// with MarshalSSZ and give the bytes to EthLib. The harness checks the input as
// SSZ bytes first, like every other input.
// This tests MarshalSSZ and HashTreeRoot on values that no decode gives.
var valuePrefix = []byte("value:")

// mutated decodes the base that ops[0] selects and applies the changes in
// ops[1:]. Each change takes 3 bytes: the site (uint16, little endian, modulo
// the number of sites) and the argument of change. It also returns
// "; changed: " and the paths of the fields that it changed, for messages.
func mutated[T any, P interface {
	*T
	codec
}](bases [][]byte, ops []byte) (P, string) {
	if len(ops) == 0 {
		ops = []byte{0}
	}
	obj := P(new(T))
	if err := obj.UnmarshalSSZ(bases[int(ops[0])%len(bases)]); err != nil {
		panic(err) // run keeps only the bases that decode
	}
	var changed []string
	for ops = ops[1:]; len(ops) >= 3; ops = ops[3:] {
		all := sites(reflect.ValueOf(obj), "", nil) // a change can replace slices, so collect again
		if len(all) == 0 {
			break
		}
		s := all[int(binary.LittleEndian.Uint16(ops))%len(all)]
		if change(s, ops[2]) && !slices.Contains(changed, s.path) {
			changed = append(changed, s.path)
		}
	}
	if changed == nil {
		changed = []string{"nothing"}
	}
	return obj, "; changed: " + strings.Join(changed, ", ")
}

// checkValue checks the encoding of a changed value, which MarshalSSZ gave.
// EthLib must accept it, and HashTreeRoot must give the EthLib root.
// HashTreeRoot must refuse a value whose encoding EthLib rejects.
func checkValue(t *testing.T, obj codec, changed string, enc []byte, fork, name string) {
	v, want, msg := oracle.SszStatic(preset, fork, name, enc)
	signal(v)
	root, err := hashTreeRoot(t, obj, changed)
	if v != oracle.Accept {
		// The value is not valid, so HashTreeRoot must refuse it too.
		also := ""
		if err == nil {
			also = ", and HashTreeRoot gives a root"
		}
		differ(t, "%s/%s: MarshalSSZ gives bytes that EthLib rejects%s: %s%s", fork, name, also, msg, changed)
	}
	if err != nil || root != want {
		differ(t, "%s/%s: root of a changed value differs: methodical %x (error: %v), EthLib %x%s", fork, name, root, err, want, changed)
	}
}

// checkRefused checks a value that MarshalSSZ refuses. It has no valid
// encoding, so HashTreeRoot must refuse it too.
func checkRefused(t *testing.T, obj codec, changed string, marshalErr error) {
	if _, err := hashTreeRoot(t, obj, changed); err == nil {
		differ(t, "%T: MarshalSSZ refuses the value (%v), but HashTreeRoot gives a root%s", obj, marshalErr, changed)
	}
}

// hashTreeRoot calls HashTreeRoot. A panic is a difference of its own. Its
// message names the first function of the ssz runtime on the panicking stack.
func hashTreeRoot(t *testing.T, obj codec, changed string) (root [32]byte, err error) {
	defer func() {
		if p := recover(); p != nil {
			differ(t, "%T: HashTreeRoot panics in %s: %v%s", obj, panicSite(), p, changed)
		}
	}()
	return obj.HashTreeRoot()
}

// panicSite is the first function of the ssz runtime on the stack of the
// panic that the caller recovers, for example "ssz.parseBitlistProgressive".
func panicSite() string {
	pcs := make([]uintptr, 64)
	frames := runtime.CallersFrames(pcs[:runtime.Callers(1, pcs)])
	for {
		f, more := frames.Next()
		if fn, ok := strings.CutPrefix(f.Function, "github.com/OffchainLabs/methodical-ssz/ssz."); ok {
			return "ssz." + fn
		}
		if !more {
			return "no ssz function"
		}
	}
}

// site is a slice in a value: a list, a vector, a byte string or a bitfield.
type site struct {
	v     reflect.Value
	path  string // for example Body.Attestations[0].AggregationBits
	max   int    // ssz-max of this dimension, 0 if none
	size  int    // ssz-size of this dimension, 0 if none
	inner []int  // ssz-size of the dimensions below, for new elements
}

// sites lists the slices in the struct that v points to, depth first.
func sites(v reflect.Value, path string, out []site) []site {
	if v.Kind() != reflect.Pointer || v.IsNil() || v.Elem().Kind() != reflect.Struct {
		return out
	}
	if path != "" {
		path += "."
	}
	s := v.Elem()
	for i := 0; i < s.NumField(); i++ {
		if f := s.Type().Field(i); f.IsExported() {
			out = sliceSites(s.Field(i), path+f.Name, dims(f.Tag.Get("ssz-max")), dims(f.Tag.Get("ssz-size")), out)
		}
	}
	return out
}

func sliceSites(v reflect.Value, path string, max, size []int, out []site) []site {
	if v.Kind() == reflect.Pointer {
		return sites(v, path, out)
	}
	if v.Kind() != reflect.Slice {
		return out
	}
	out = append(out, site{v, path, max[0], size[0], size[1:]})
	if k := v.Type().Elem().Kind(); k == reflect.Pointer || k == reflect.Slice {
		for i := 0; i < v.Len(); i++ {
			out = sliceSites(v.Index(i), fmt.Sprintf("%s[%d]", path, i), append(max[1:], 0), append(size[1:], 0), out)
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
// It reports whether it changed the slice.
func change(s site, a byte) bool {
	v, n := s.v, s.v.Len()
	name := v.Type().Name()
	if strings.HasPrefix(name, "Bit") && a&1 == 1 && n > 0 {
		i := 8*n - 1 - int(a>>1)%(8*n)
		v.Index(i / 8).SetUint(v.Index(i/8).Uint() ^ 1<<(i%8))
		return true
	}
	a >>= 1
	if name == "Bitlist" { // a new bit length, all bits clear
		length := 0
		if n > 0 && v.Index(n-1).Uint() != 0 {
			length = 8*(n-1) + bits.Len8(uint8(v.Index(n-1).Uint())) - 1
		}
		k := []int{0, 1, length - 1, length + 1, s.max - 1, s.max, s.max + 1, s.max + 7, s.max + 8}[int(a)%9]
		if k < 0 || !inBudget(k/8+1, 1) {
			return false
		}
		b := make([]byte, k/8+1)
		b[k/8] = 1 << (k % 8)
		v.SetBytes(b)
		return true
	}
	var lengths []int
	if s.max > 0 {
		lengths = []int{0, 1, n - 1, n + 1, s.max, s.max + 1}
	}
	if s.size > 0 {
		lengths = []int{0, s.size - 1, s.size + 1}
	}
	if lengths == nil {
		return false
	}
	k := lengths[int(a)%len(lengths)]
	if k < 0 || !inBudget(k-n, storage(v.Type().Elem(), s.inner)) {
		return false
	}
	w := reflect.MakeSlice(v.Type(), k, k)
	reflect.Copy(w, v)
	for i := n; i < k; i++ {
		fillField(w.Index(i), s.inner)
	}
	v.Set(w)
	return true
}

// The mutation budget of one change: the new elements that it adds, and the
// storage that it allocates for them. Huge limits (validators, transactions,
// blobs) then never reach max+1. It bounds one change, not a whole value.
const (
	budgetElements = 1 << 18
	budgetBytes    = 1 << 22
)

// inBudget reports whether n new elements of the given storage each fit the
// mutation budget. Division keeps the product from overflowing.
func inBudget(n, each int) bool {
	return n <= budgetElements && n <= budgetBytes/max(each, 1)
}

// storage is the number of bytes that fillField allocates for one element of
// type t, whose dimensions below have the ssz-size values in sizes.
func storage(t reflect.Type, sizes []int) int {
	switch {
	case t.Kind() == reflect.Pointer && t.Elem().Kind() == reflect.Struct:
		n := int(t.Size() + t.Elem().Size())
		for i := 0; i < t.Elem().NumField(); i++ {
			if f := t.Elem().Field(i); f.IsExported() {
				// The struct holds the field. storage counts what the field adds.
				n += storage(f.Type, dims(f.Tag.Get("ssz-size"))) - int(f.Type.Size())
			}
		}
		return n
	case t.Kind() == reflect.Slice && len(sizes) > 0 && sizes[0] > 0:
		return int(t.Size()) + sizes[0]*storage(t.Elem(), sizes[1:])
	case t.Kind() == reflect.Slice && strings.Contains(t.Name(), "Bitlist"):
		return int(t.Size()) + 1
	}
	return int(t.Size())
}

func TestChange(t *testing.T) {
	a := new(eth.AttestationElectra)
	fill(reflect.ValueOf(a).Elem())
	bitlist := sites(reflect.ValueOf(a), "", nil)[0] // AggregationBits
	change(bitlist, 6<<1)                            // max+1 bits
	if n := bitlist.max + 1; len(a.AggregationBits) != n/8+1 || a.AggregationBits[n/8] != 1<<(n%8) {
		t.Fatalf("want a bitlist of %d bits, got %d bytes", n, len(a.AggregationBits))
	}
	change(sites(reflect.ValueOf(a), "", nil)[0], 6<<1|1) // flip bit 6 from the top: the delimiter
	if a.AggregationBits[len(a.AggregationBits)-1] != 0 {
		t.Fatal("the delimiter is still set")
	}
	i := new(eth.IndexedAttestationElectra)
	fill(reflect.ValueOf(i).Elem())
	list := sites(reflect.ValueOf(i), "", nil)[0] // AttestingIndices
	change(list, 5<<1)                            // max+1 elements
	if len(i.AttestingIndices) != list.max+1 {
		t.Fatalf("want %d elements, got %d", list.max+1, len(i.AttestingIndices))
	}
}

// TestBudget checks the mutation budget on the case that it exists for: a
// list of 2^20 builder withdrawals must not grow to its limit plus one.
func TestBudget(t *testing.T) {
	st := new(eth.BeaconStateGloas)
	fill(reflect.ValueOf(st).Elem())
	for _, s := range sites(reflect.ValueOf(st), "", nil) {
		if s.path == "BuilderPendingWithdrawals" {
			if change(s, 5<<1) { // max+1 elements
				t.Fatalf("grew to %d elements", len(st.BuilderPendingWithdrawals))
			}
			if each := storage(s.v.Type().Elem(), s.inner); each < 8+36 {
				t.Fatalf("storage %d bytes for a 36-byte element", each)
			}
			return
		}
	}
	t.Fatal("no site BuilderPendingWithdrawals")
}

// TestKnownIsNarrow checks that known.txt does not skip differences of other
// classes: the counterexamples of the PR 2 review, and Checkpoint examples.
func TestKnownIsNarrow(t *testing.T) {
	if known == nil {
		t.Skip("STRICT=1 turns known.txt off")
	}
	for _, msg := range []string{
		// A bounded list (EthLib: SszList, NUMBER_OF_COLUMNS) with a wrong decoder limit.
		"glamsterdam/DataColumnsByRootIdentifier: EthLib accepts, methodical rejects: ssz-max exceeded: c.Columns has 65 elements, ssz-max is 64: list length is higher than max value",
		// A list, not a bitlist, with the limit of the recorded bitlist.
		"fusaka/IndexedAttestation: MarshalSSZ gives bytes that EthLib rejects, and HashTreeRoot gives a root: input rejected: EthLib.Serialization.Ssz.Err.overLimit 131072 131073; changed: AttestingIndices",
		// A panic in a type with no bitlist.
		"*eth.Checkpoint: HashTreeRoot panics in ssz.parseBitlistProgressive: runtime error: slice bounds out of range [:33] with capacity 32; changed: Root",
		"*eth.Checkpoint: HashTreeRoot panics in no ssz function: runtime error: slice bounds out of range [:33] with capacity 32; changed: Root",
		// A listed field name with a limit that no line lists.
		"glamsterdam/ExecutionPayload: EthLib accepts, methodical rejects: ssz-max exceeded: c.Withdrawals has 18 elements, ssz-max is 17: list length is higher than max value",
		// A byte vector of the wrong length.
		"*eth.Checkpoint: MarshalSSZ refuses the value (Root: unexpected number of bytes, got 31 but found 32: list length is higher than max value), but HashTreeRoot gives a root; changed: Root",
	} {
		if known.MatchString(msg) {
			t.Errorf("known.txt skips %q", msg)
		}
	}
	saved := "glamsterdam/ExecutionRequests: EthLib accepts, methodical rejects: ssz-max exceeded: c.BuilderExits has 17 elements, ssz-max is 16: list length is higher than max value"
	if !known.MatchString(saved) {
		t.Errorf("known.txt does not skip the saved input: %q", saved)
	}
}
