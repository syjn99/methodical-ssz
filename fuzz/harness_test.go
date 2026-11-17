package fuzz

import (
	"bytes"
	"fmt"
	"os"
	"path/filepath"
	"regexp"
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

// KNOWN is a regular expression. A difference whose message matches it skips
// the input, so that a recorded class of findings does not stop the target.
// Without KNOWN every difference fails.
var known = func() *regexp.Regexp {
	if e := os.Getenv("KNOWN"); e != "" {
		return regexp.MustCompile(e)
	}
	return nil
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
	err := obj.UnmarshalSSZ(data)
	if err == nil && verdict == oracle.Reject {
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
