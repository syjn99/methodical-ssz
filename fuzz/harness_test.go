package fuzz

import (
	"bytes"
	"os"
	"path/filepath"
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
			f.Add(data)
		}
	}
	f.Add([]byte{})
	f.Fuzz(func(t *testing.T, data []byte) {
		for _, fork := range forks {
			check(t, P(new(T)), fork, name, data)
		}
	})
}

func check(t *testing.T, obj codec, fork, name string, data []byte) {
	verdict, wantRoot, out := oracle.SszStatic(preset, fork, name, data)
	if verdict == oracle.Unsupported {
		t.Fatalf("%s/%s: EthLib gave no verdict: %s", fork, name, out)
	}
	err := obj.UnmarshalSSZ(data)
	if (err == nil) != (verdict == oracle.Accept) {
		t.Fatalf("%s/%s: accept/reject differs: UnmarshalSSZ error = %v, EthLib: %s",
			fork, name, err, map[bool]any{true: "accepted", false: string(out)}[verdict == oracle.Accept])
	}
	if err != nil {
		return
	}
	enc, err := obj.MarshalSSZ()
	if err != nil {
		t.Fatalf("%s/%s: MarshalSSZ fails on a decoded value: %v", fork, name, err)
	}
	if !bytes.Equal(enc, out) {
		t.Fatalf("%s/%s: encoding differs:\nmethodical %x\nEthLib     %x", fork, name, enc, out)
	}
	root, err := obj.HashTreeRoot()
	if err != nil {
		t.Fatalf("%s/%s: HashTreeRoot fails on a decoded value: %v", fork, name, err)
	}
	if root != wantRoot {
		t.Fatalf("%s/%s: root differs: methodical %x, EthLib %x", fork, name, root, wantRoot)
	}
}
