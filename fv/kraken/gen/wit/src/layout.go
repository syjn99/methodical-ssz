//go:build ignore

// layout prints, as JSON, the Go object layout of the target types for
// GOOS=linux GOARCH=amd64: for every struct type of fv/kraken/target and
// fv/kraken/target/prysm, unsafe.Sizeof, unsafe.Alignof and, per field,
// unsafe.Offsetof, the field size and its kind. The values are the constant
// values of those unsafe expressions as the gc type checker computes them
// with the amd64 size rules (types.SizesFor("gc", "amd64")), so no amd64
// binary has to run on the host (re-proof fix 2, X3; astra reprove-fix 3).
// Run from the repository root:
//
//	go run fv/kraken/lean/tools/wit/layout.go > fv/kraken/lean/tools/wit/layout.json
package main

import (
	"encoding/json"
	"fmt"
	"go/ast"
	"go/constant"
	"go/importer"
	"go/parser"
	"go/token"
	"go/types"
	"os"
	"sort"
	"strings"
)

const mod = "github.com/OffchainLabs/methodical-ssz/fv/kraken/"

type field struct {
	Name   string `json:"name"`
	Offset int64  `json:"offset"`
	Size   int64  `json:"size"`
	Kind   string `json:"kind"` // bool, uint, ptr, slice, array
	Elem   string `json:"elem,omitempty"`
	Esz    int64  `json:"esz,omitempty"`
}

type typ struct {
	Size   int64   `json:"size"`
	Align  int64   `json:"align"`
	Fields []field `json:"fields"`
}

func main() {
	fset := token.NewFileSet()
	sizes := types.SizesFor("gc", "amd64")
	imp := importer.ForCompiler(fset, "source", nil)
	// One synthetic file: a constant per unsafe expression, type-checked with
	// the amd64 sizes. The constants are the values the compiler would fold.
	pkgs := map[string]string{"target": mod + "target", "prysm": mod + "target/prysm"}
	var src strings.Builder
	src.WriteString("package p\nimport (\n\t\"unsafe\"\n")
	for n, p := range pkgs {
		fmt.Fprintf(&src, "\t%s %q\n", n, p)
	}
	src.WriteString(")\n")
	out := map[string]*typ{}
	type q struct{ key, expr string }
	var qs []q
	for n, p := range pkgs {
		pkg, err := imp.Import(p)
		if err != nil {
			panic(err)
		}
		for _, name := range pkg.Scope().Names() {
			tn, ok := pkg.Scope().Lookup(name).(*types.TypeName)
			if !ok {
				continue
			}
			st, ok := tn.Type().Underlying().(*types.Struct)
			if !ok {
				continue
			}
			key := name
			if n == "prysm" {
				key = "Prysm" + name
			}
			t := &typ{}
			out[key] = t
			v := fmt.Sprintf("%s.%s{}", n, name)
			qs = append(qs, q{key + ".size", "unsafe.Sizeof(" + v + ")"}, q{key + ".align", "unsafe.Alignof(" + v + ")"})
			for i := 0; i < st.NumFields(); i++ {
				f := st.Field(i)
				fl := field{Name: f.Name()}
				switch u := f.Type().Underlying().(type) {
				case *types.Basic:
					fl.Kind = "uint"
					if u.Kind() == types.Bool {
						fl.Kind = "bool"
					}
				case *types.Pointer:
					fl.Kind, fl.Elem = "ptr", elemName(u.Elem())
				case *types.Slice:
					fl.Kind, fl.Esz = "slice", sizes.Sizeof(u.Elem())
					if p, ok := u.Elem().(*types.Pointer); ok {
						fl.Elem = elemName(p.Elem())
					}
				case *types.Array:
					fl.Kind = "array"
				default:
					panic(fmt.Sprintf("%s.%s: %T", name, f.Name(), u))
				}
				t.Fields = append(t.Fields, fl)
				qs = append(qs, q{fmt.Sprintf("%s.%d.offset", key, i), "unsafe.Offsetof(" + v + "." + f.Name() + ")"},
					q{fmt.Sprintf("%s.%d.size", key, i), "unsafe.Sizeof(" + v + "." + f.Name() + ")"})
			}
		}
	}
	sort.Slice(qs, func(i, j int) bool { return qs[i].key < qs[j].key })
	for i, x := range qs {
		fmt.Fprintf(&src, "const c%d = %s\n", i, x.expr)
	}
	f, err := parser.ParseFile(fset, "p.go", src.String(), 0)
	if err != nil {
		panic(err)
	}
	conf := types.Config{Importer: imp, Sizes: sizes}
	pkg, err := conf.Check("p", fset, []*ast.File{f}, nil)
	if err != nil {
		panic(err)
	}
	for i, x := range qs {
		v, _ := constant.Int64Val(pkg.Scope().Lookup(fmt.Sprintf("c%d", i)).(*types.Const).Val())
		parts := strings.Split(x.key, ".")
		t := out[parts[0]]
		switch {
		case parts[1] == "size":
			t.Size = v
		case parts[1] == "align":
			t.Align = v
		default:
			var k int
			fmt.Sscan(parts[1], &k)
			if parts[2] == "offset" {
				t.Fields[k].Offset = v
			} else {
				t.Fields[k].Size = v
			}
		}
	}
	e := json.NewEncoder(os.Stdout)
	e.SetIndent("", " ")
	if err := e.Encode(map[string]any{"goos": "linux", "goarch": "amd64", "sizes": "gc", "types": out}); err != nil {
		panic(err)
	}
}

func elemName(t types.Type) string {
	n, ok := t.(*types.Named)
	if !ok {
		return t.String()
	}
	if strings.HasSuffix(n.Obj().Pkg().Path(), "/prysm") {
		return "Prysm" + n.Obj().Name()
	}
	return n.Obj().Name()
}
