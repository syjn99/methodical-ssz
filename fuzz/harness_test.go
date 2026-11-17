package fuzz

import (
	"bytes"
	"fmt"
	"os"
	"path/filepath"
	"reflect"
	"regexp"
	"strconv"
	"strings"
	"testing"

	"github.com/OffchainLabs/methodical-ssz/fuzz/oracle"
	"github.com/golang/snappy"
)

// EthLib names forks after the network upgrade. Each maps to its directory
// in consensus-spec-tests.
const (
	fulu  = "fusaka"
	gloas = "glamsterdam"
)

var specDir = map[string]string{fulu: "fulu", gloas: "gloas"}

type codec interface {
	UnmarshalSSZ([]byte) error
	MarshalSSZ() ([]byte, error)
	HashTreeRoot() ([32]byte, error)
}

// run fuzzes the generated code of T against the EthLib container `name`,
// at every fork where Prysm uses T for that container.
func run[T any, P interface {
	*T
	codec
}](f *testing.F, name string, forks ...string) {
	if _, err := os.Stat(".seeds/complete"); err != nil {
		f.Fatal("no seed vectors: run ./seeds.sh")
	}
	var corpus [][]byte
	for _, fork := range forks {
		// EthLib answers code 0 when it holds no such container. That is no
		// verdict on the bytes, so the type cannot be tested.
		if v, _, msg := oracle.SszStatic(preset, fork, name, nil); v == oracle.Unsupported {
			f.Skipf("EthLib: %s", msg)
		}
		seeds, _ := filepath.Glob(filepath.Join(".seeds", preset, specDir[fork], "ssz_static", name, "*", "*", "serialized.ssz_snappy"))
		for _, path := range seeds {
			raw, err := os.ReadFile(path)
			if err != nil {
				f.Fatal(err)
			}
			data, err := snappy.Decode(nil, raw)
			if err != nil {
				f.Fatal(err)
			}
			corpus = append(corpus, data)
		}
	}
	// The zero value is a seed that both sides must accept. It gives the
	// targets without vectors one valid input.
	obj := new(T)
	fill(reflect.ValueOf(obj).Elem())
	zero, err := P(obj).MarshalSSZ()
	if err != nil {
		f.Fatalf("MarshalSSZ of the zero value: %v", err)
	}
	for _, fork := range forks {
		if v, _, msg := oracle.SszStatic(preset, fork, name, zero); v != oracle.Accept {
			f.Fatalf("%s/%s: EthLib rejects the zero value: %s", fork, name, msg)
		}
	}
	corpus = append(corpus, zero, []byte{})
	var bases [][]byte // the inputs that a value input can start from
	for _, data := range corpus {
		if P(new(T)).UnmarshalSSZ(data) == nil {
			bases = append(bases, data)
		}
	}
	if *codes {
		table[T, P](f, name, forks, corpus, bases)
	}
	for _, data := range corpus {
		f.Add(data)
	}
	for i := range min(len(bases), 256) {
		f.Add(append(bytes.Clone(valuePrefix), byte(i)))
	}
	f.Fuzz(func(t *testing.T, data []byte) {
		// Every input is SSZ bytes first, also one that starts with valuePrefix.
		for _, fork := range forks {
			check(t, P(new(T)), fork, name, data)
		}
		if ops, ok := bytes.CutPrefix(data, valuePrefix); ok {
			obj := mutated[T, P](bases, ops)
			enc, err := obj.MarshalSSZ()
			if err != nil {
				checkRefused(t, obj, err)
				return
			}
			for _, fork := range forks {
				checkValue(t, obj, enc, fork, name)
				check(t, P(new(T)), fork, name, enc)
			}
		}
	})
}

// fill gives the fields of a zero struct the lengths that their `ssz-size`
// tags fix, so that the struct encodes. Lists stay empty.
func fill(v reflect.Value) {
	for i := 0; i < v.NumField(); i++ {
		f := v.Field(i)
		if !f.CanSet() {
			continue
		}
		var dims []int
		for _, d := range strings.Split(v.Type().Field(i).Tag.Get("ssz-size"), ",") {
			n, _ := strconv.Atoi(d) // "?" and "" give 0: a list
			dims = append(dims, n)
		}
		fillField(f, dims)
	}
}

func fillField(f reflect.Value, dims []int) {
	switch {
	case f.Kind() == reflect.Pointer && f.Type().Elem().Kind() == reflect.Struct:
		f.Set(reflect.New(f.Type().Elem()))
		fill(f.Elem())
	case f.Kind() == reflect.Slice && strings.Contains(f.Type().Name(), "Bitlist"):
		f.SetBytes([]byte{1}) // the empty bitlist is its delimiter bit
	case f.Kind() == reflect.Slice && len(dims) > 0:
		f.Set(reflect.MakeSlice(f.Type(), dims[0], dims[0]))
		for i := 0; i < dims[0]; i++ {
			fillField(f.Index(i), dims[1:])
		}
	}
}

// known.txt holds one regular expression per line. A difference whose message
// matches one skips the input, so that a recorded class of findings does not
// stop the target. With STRICT=1 every difference fails.
var known = func() *regexp.Regexp {
	if os.Getenv("STRICT") == "1" {
		return nil
	}
	raw, err := os.ReadFile("known.txt")
	if err != nil {
		panic(err)
	}
	var lines []string
	for _, l := range strings.Split(string(raw), "\n") {
		if l = strings.TrimSpace(l); l != "" && !strings.HasPrefix(l, "#") {
			lines = append(lines, "(?:"+l+")")
		}
	}
	if len(lines) == 0 {
		return nil
	}
	return regexp.MustCompile(strings.Join(lines, "|"))
}()

func differ(t *testing.T, format string, args ...any) {
	msg := fmt.Sprintf(format, args...)
	if known != nil && known.MatchString(msg) {
		t.Skip(msg)
	}
	t.Fatal(msg)
}

func check(t *testing.T, obj codec, fork, name string, data []byte) {
	verdict, wantRoot, out := oracle.SszStatic(preset, fork, name, data)
	if verdict == oracle.Unsupported {
		t.Fatalf("%s/%s: EthLib gave no verdict: %s", fork, name, out)
	}
	signal(verdict)
	err := obj.UnmarshalSSZ(data)
	if err == nil && verdict != oracle.Accept {
		differ(t, "%s/%s: methodical accepts, EthLib rejects: %s", fork, name, out)
	}
	if err != nil && verdict == oracle.Accept {
		differ(t, "%s/%s: EthLib accepts, methodical rejects: %v", fork, name, err)
	}
	if err != nil {
		return
	}
	enc, err := obj.MarshalSSZ()
	if err != nil {
		differ(t, "%s/%s: MarshalSSZ fails on a decoded value: %v", fork, name, err)
	}
	if !bytes.Equal(enc, out) {
		differ(t, "%s/%s: encoding differs:\nmethodical %x\nEthLib     %x", fork, name, enc, out)
	}
	root, err := obj.HashTreeRoot()
	if err != nil {
		differ(t, "%s/%s: HashTreeRoot fails on a decoded value: %v", fork, name, err)
	}
	if root != wantRoot {
		differ(t, "%s/%s: root differs: methodical %x, EthLib %x", fork, name, root, wantRoot)
	}
}
