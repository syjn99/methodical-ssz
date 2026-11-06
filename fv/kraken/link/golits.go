//go:build ignore

// golits prints, as JSON, the first-argument string literal of every
// fmt.Errorf call in the Go files given on the command line:
// {"<file>": [{"line": n, "value": "<unquoted literal>"}, ...]}.
// It reads the syntax tree (go/parser), so comments and strings that only
// look like a call are not calls (astra reprove-fix finding 2).
// Run: go run fv/kraken/link/golits.go -- <file.go> ... (`--` ends the source list)
package main

import (
	"encoding/json"
	"go/ast"
	"go/parser"
	"go/token"
	"os"
	"strconv"
)

type lit struct {
	Line  int    `json:"line"`
	Value string `json:"value"`
}

func main() {
	out := map[string][]lit{}
	for _, path := range os.Args[1:] {
		if path == "--" {
			continue
		}
		fset := token.NewFileSet()
		f, err := parser.ParseFile(fset, path, nil, 0)
		if err != nil {
			panic(err)
		}
		lits := []lit{}
		ast.Inspect(f, func(n ast.Node) bool {
			call, ok := n.(*ast.CallExpr)
			if !ok || len(call.Args) == 0 {
				return true
			}
			sel, ok := call.Fun.(*ast.SelectorExpr)
			if !ok || sel.Sel.Name != "Errorf" {
				return true
			}
			if id, ok := sel.X.(*ast.Ident); !ok || id.Name != "fmt" {
				return true
			}
			b, ok := call.Args[0].(*ast.BasicLit)
			if !ok || b.Kind != token.STRING {
				return true
			}
			v, err := strconv.Unquote(b.Value)
			if err != nil {
				panic(err)
			}
			lits = append(lits, lit{fset.Position(b.Pos()).Line, v})
			return true
		})
		out[path] = lits
	}
	if err := json.NewEncoder(os.Stdout).Encode(out); err != nil {
		panic(err)
	}
}
