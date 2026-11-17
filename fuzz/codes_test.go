package fuzz

import (
	"bytes"
	"flag"
	"fmt"
	"maps"
	"os"
	"os/exec"
	"path/filepath"
	"slices"
	"strconv"
	"strings"
	"testing"

	"github.com/OffchainLabs/methodical-ssz/fuzz/oracle"
)

// reasons names the verdicts that signal tells apart, for the table.
var reasons = [...]string{"accept", "WRONG_TYPE", "LIMIT", "SCOPE", "SCOPE_TOO_SMALL", "SCOPE_UNDIVIDED",
	"SCOPE_WIDTHLESS", "FIRST_OFFSET", "OFFSET_UNORDERED", "OFFSET_PAST_SCOPE", "OFFSET_UNALIGNED",
	"OFFSET_BELOW_TABLE", "TRUNCATED", "NOT_A_BIT", "COUNT", "PADDING_BITS", "EMPTY_ENCODING", "NO_DELIMITER",
	"TRAILING_ZEROS", "NO_SELECTOR", "UNKNOWN_SELECTOR"}

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

var codes = flag.Bool("codes", false, "print the EthLib verdicts that the corpus of each target reaches, then skip the target")

// table prints one line for each fork of a target. entries counts the corpus
// entries: the seed corpus of run, testdata/fuzz and the fuzz cache (the
// -test.fuzzcachedir flag, or else the default cache of `go test -fuzz`).
// Identical entries from two sources count twice. The verdicts count EthLib
// calls, as the fuzz function makes them: one for the bytes of each entry, and
// one more for the encoding of each value entry that MarshalSSZ encodes.
// both-accept counts the calls where UnmarshalSSZ accepts too.
func table[T any, P interface {
	*T
	codec
}](f *testing.F, name string, forks []string, corpus, bases [][]byte) {
	cache := flag.Lookup("test.fuzzcachedir").Value.String()
	if cache == "" {
		out, err := exec.Command("go", "env", "GOCACHE").Output()
		if err != nil {
			f.Fatal(err)
		}
		cache = filepath.Join(strings.TrimSpace(string(out)), "fuzz", "github.com/OffchainLabs/methodical-ssz/fuzz")
	}
	for _, dir := range []string{"testdata/fuzz", cache} {
		files, _ := filepath.Glob(filepath.Join(dir, f.Name(), "*"))
		for _, path := range files {
			raw, err := os.ReadFile(path)
			if err != nil {
				f.Fatal(err)
			}
			lit, ok := strings.CutPrefix(strings.TrimSpace(string(raw)), "go test fuzz v1\n[]byte(")
			data, err := strconv.Unquote(strings.TrimSuffix(lit, ")"))
			if !ok || err != nil {
				f.Fatalf("%s: not one []byte in the Go corpus format", path)
			}
			corpus = append(corpus, []byte(data))
		}
	}
	calls, values, refused := corpus, 0, 0
	for _, data := range corpus {
		if ops, ok := bytes.CutPrefix(data, valuePrefix); ok {
			values++
			obj, _ := mutated[T, P](bases, ops)
			if enc, err := obj.MarshalSSZ(); err != nil {
				refused++
			} else {
				calls = append(calls, enc)
			}
		}
	}
	for _, fork := range forks {
		count := map[oracle.Verdict]int{}
		both := 0
		for _, data := range calls {
			v, _, _ := oracle.SszStatic(preset, fork, name, data)
			count[v]++
			if v == oracle.Accept && P(new(T)).UnmarshalSSZ(data) == nil {
				both++
			}
		}
		line := fmt.Sprintf("%s %s entries=%d value-entries=%d marshal-refused=%d calls=%d both-accept=%d",
			f.Name(), fork, len(corpus), values, refused, len(calls), both)
		for _, v := range slices.Sorted(maps.Keys(count)) {
			reason := fmt.Sprintf("code%d", v)
			if int(v) < len(reasons) {
				reason = reasons[v]
			}
			line += fmt.Sprintf(" %s=%d", reason, count[v])
		}
		fmt.Println(line)
	}
	f.SkipNow()
}
