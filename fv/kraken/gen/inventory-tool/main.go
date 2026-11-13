// inventory-tool dumps the sszgen 698c202 intermediate representation (IR) of every
// type in one or more generator configs as JSON. It is read-only over its
// inputs and calls the generator's own front end (config parser, TypeDefs,
// ParseTypeDef, delegation interface set), so the IR is the one the renderer
// sees.
//
// It must be built inside the module that owns the configured packages (the
// temporary Prysm tree, which replaces methodical-ssz with the 698c202 tree).
// It has its own go.mod here only so that the methodical-ssz root module does
// not compile it. Usage:
//
//	inventory-tool -tags <comma tags or empty> -out <file.json> <config.yaml>...
package main

import (
	"crypto/sha256"
	"encoding/hex"
	"encoding/json"
	"flag"
	"fmt"
	"go/types"
	"os"
	"path/filepath"
	"sort"
	"strings"

	"github.com/OffchainLabs/methodical-ssz/sszgen"
	"github.com/OffchainLabs/methodical-ssz/sszgen/config"
	"github.com/OffchainLabs/methodical-ssz/sszgen/interfaces"
	gentypes "github.com/OffchainLabs/methodical-ssz/sszgen/types"
)

type deleg struct {
	Marshaler   bool `json:"marshaler"`
	Unmarshaler bool `json:"unmarshaler"`
	Sizer       bool `json:"sizer"`
}

type field struct {
	Key   string `json:"key"`
	Value *node  `json:"v"`
}

// node is one IR value. Only the members of its kind are set.
type node struct {
	Kind         string   `json:"k"`
	GoType       string   `json:"go_type"`
	Name         string   `json:"name,omitempty"`
	Pkg          string   `json:"pkg,omitempty"`
	FixedSize    *int     `json:"fixed_size"`
	Variable     *bool    `json:"variable"`
	Deleg        *deleg   `json:"deleg,omitempty"`
	Fields       []field  `json:"fields,omitempty"`
	ActiveFields []bool   `json:"active_fields,omitempty"`
	Elem         *node    `json:"elem,omitempty"`
	Max          *int     `json:"max,omitempty"`
	Progressive  bool     `json:"progressive,omitempty"`
	Size         *int     `json:"size,omitempty"`
	IsArray      bool     `json:"is_array,omitempty"`
	Bits         int      `json:"bits,omitempty"`
	Bitfield     bool     `json:"bitfield,omitempty"`
	Underlying   *node    `json:"underlying,omitempty"`
	Referent     *node    `json:"referent,omitempty"`
	Notes        []string `json:"notes,omitempty"`
}

type goField struct {
	Name     string `json:"name"`
	Type     string `json:"type"`
	Tag      string `json:"tag"`
	Exported bool   `json:"exported"`
	Offset   int64  `json:"offset_gc_amd64"`
	Size     int64  `json:"size_gc_amd64"`
}

type typeOut struct {
	Name         string                        `json:"name"`
	Package      string                        `json:"package"`
	GoFile       string                        `json:"go_file"`
	GoFileKind   string                        `json:"go_file_kind"`
	IsStruct     bool                          `json:"is_struct"`
	Progressive  *config.ProgressiveConfig     `json:"progressive_config"`
	FieldConfigs map[string]config.FieldConfig `json:"field_configs"`
	GoSize       int64                         `json:"go_size_gc_amd64"`
	GoAlign      int64                         `json:"go_align_gc_amd64"`
	GoFields     []goField                     `json:"go_fields"`
	IR           *node                         `json:"ir"`
	ParseError   string                        `json:"parse_error,omitempty"`
	MethodsInPkg []string                      `json:"ssz_methods_in_loaded_pkg"`
}

type configOut struct {
	File    string    `json:"file"`
	Sha256  string    `json:"sha256"`
	Package string    `json:"package"`
	Error   string    `json:"error,omitempty"`
	Types   []typeOut `json:"types"`
}

type out struct {
	Schema  string      `json:"schema"`
	Tags    string      `json:"tags"`
	Configs []configOut `json:"configs"`
}

var set *interfaces.Set

func intp(i int) *int    { return &i }
func boolp(b bool) *bool { return &b }

func delegOf(v gentypes.ValRep) *deleg {
	return &deleg{
		Marshaler:   v.SatisfiesInterface(set.Marshaler),
		Unmarshaler: v.SatisfiesInterface(set.Unmarshaler),
		Sizer:       v.SatisfiesInterface(set.Sizer),
	}
}

func sizes(v gentypes.ValRep, n *node) {
	defer func() {
		if r := recover(); r != nil {
			n.Notes = append(n.Notes, fmt.Sprintf("size panic: %v", r))
		}
	}()
	n.Variable = boolp(v.IsVariableSized())
	n.FixedSize = intp(v.FixedSize())
}

func conv(v gentypes.ValRep) *node {
	n := &node{GoType: v.TypeName()}
	switch x := v.(type) {
	case *gentypes.ValueContainer:
		n.Kind, n.Name, n.Pkg = "container", x.Name, x.Package
		n.Deleg = delegOf(v)
		n.ActiveFields = x.ActiveFields
		for _, c := range x.Contents {
			n.Fields = append(n.Fields, field{Key: c.Key, Value: conv(c.Value)})
		}
	case *gentypes.ValueList:
		n.Kind = "list"
		n.Elem, n.Max, n.Progressive = conv(x.ElementValue), intp(x.MaxSize), x.Progressive
	case *gentypes.ValueVector:
		n.Kind = "vector"
		n.Elem, n.Size, n.IsArray = conv(x.ElementValue), intp(x.Size), x.IsArray
	case *gentypes.ValueUint:
		n.Kind, n.Name, n.Pkg, n.Bits = "uint", x.Name, x.Package, int(x.Size)
	case *gentypes.ValueBool:
		n.Kind, n.Name = "bool", x.Name
	case *gentypes.ValueByte:
		n.Kind, n.Name = "byte", x.Name
	case *gentypes.ValueOverlay:
		n.Kind, n.Name, n.Pkg, n.Bitfield = "overlay", x.Name, x.Package, x.IsBitfield()
		n.Deleg = delegOf(v)
		n.Underlying = conv(x.Underlying)
	case *gentypes.ValuePointer:
		n.Kind = "pointer"
		n.Deleg = delegOf(v)
		n.Referent = conv(x.Referent)
	case *gentypes.ValueUnion:
		n.Kind, n.Name = "union", x.Name
		n.Notes = append(n.Notes, "union: generator ValueUnion has no size")
		return n
	default:
		n.Kind = fmt.Sprintf("unknown:%T", v)
		return n
	}
	sizes(v, n)
	return n
}

func die(err error) {
	fmt.Fprintln(os.Stderr, "ERROR:", err)
	os.Exit(1)
}

func main() {
	tags := flag.String("tags", "", "comma-separated build tags used to load the package")
	outPath := flag.String("out", "", "output JSON file")
	flag.Parse()
	if *outPath == "" || flag.NArg() == 0 {
		die(fmt.Errorf("usage: inventory-tool -tags T -out F config.yaml..."))
	}
	var err error
	if set, err = interfaces.DefaultSet(); err != nil {
		die(err)
	}
	var buildTags []string
	if *tags != "" {
		buildTags = strings.Split(*tags, ",")
	}
	sz := types.SizesFor("gc", "amd64")
	res := out{Schema: "fvphase1c.ir/1", Tags: *tags}
	for _, cfgPath := range flag.Args() {
		b, err := os.ReadFile(cfgPath)
		if err != nil {
			die(err)
		}
		h := sha256.Sum256(b)
		gc, err := config.ParseGeneratorConfig(b)
		if err != nil {
			die(fmt.Errorf("%s: %w", cfgPath, err))
		}
		co := configOut{File: cfgPath, Sha256: hex.EncodeToString(h[:]), Package: gc.Package}
		ps, err := sszgen.NewGoPathScoper(gc.Package, gc, buildTags...)
		if err != nil {
			co.Error = "load: " + err.Error()
			res.Configs = append(res.Configs, co)
			continue
		}
		// A second load of the same package, only for source positions
		// (GoPathScoper does not expose its FileSet).
		posPkg, err := sszgen.NewImporter(buildTags...).Load(gc.Package)
		if err != nil {
			co.Error = "load for positions: " + err.Error()
			res.Configs = append(res.Configs, co)
			continue
		}
		defs, err := sszgen.TypeDefs(ps, gc.TypeNames()...)
		if err != nil {
			co.Error = "TypeDefs: " + err.Error()
			res.Configs = append(res.Configs, co)
			continue
		}
		for _, d := range defs {
			tc := gc.TypeConfig(d.Name)
			to := typeOut{Name: d.Name, Package: d.PackageName, IsStruct: d.IsStruct,
				Progressive: tc.Progressive, FieldConfigs: tc.Fields}
			obj := ps.Scope().Lookup(d.Name)
			if obj != nil {
				// The base name of the defining file tells protobuf (.pb.go)
				// types from native Go types.
				if pobj := posPkg.Types.Scope().Lookup(d.Name); pobj != nil {
					to.GoFile = filepath.Base(posPkg.Fset.Position(pobj.Pos()).Filename)
				}
				switch {
				case strings.HasSuffix(to.GoFile, ".pb.go"):
					to.GoFileKind = "protobuf"
				case to.GoFile == "" || to.GoFile == "-":
					to.GoFileKind = "unknown"
				default:
					to.GoFileKind = "native"
				}
				t := obj.Type()
				to.GoSize, to.GoAlign = sz.Sizeof(t), sz.Alignof(t)
				if st, ok := t.Underlying().(*types.Struct); ok {
					fs := make([]*types.Var, st.NumFields())
					for i := range fs {
						fs[i] = st.Field(i)
					}
					offs := sz.Offsetsof(fs)
					for i, f := range fs {
						to.GoFields = append(to.GoFields, goField{Name: f.Name(), Type: types.TypeString(f.Type(), nil),
							Tag: st.Tag(i), Exported: f.Exported(), Offset: offs[i], Size: sz.Sizeof(f.Type())})
					}
				}
				ms := types.NewMethodSet(types.NewPointer(t))
				for i := 0; i < ms.Len(); i++ {
					name := ms.At(i).Obj().Name()
					if strings.HasSuffix(name, "SSZ") || strings.HasPrefix(name, "HashTreeRoot") || name == "MarshalSSZTo" {
						to.MethodsInPkg = append(to.MethodsInPkg, name)
					}
				}
				sort.Strings(to.MethodsInPkg)
			}
			vr, err := sszgen.ParseTypeDef(d)
			if err != nil {
				to.ParseError = err.Error()
			} else {
				to.IR = conv(vr)
			}
			co.Types = append(co.Types, to)
		}
		res.Configs = append(res.Configs, co)
		fmt.Fprintf(os.Stderr, "%s: %d types\n", cfgPath, len(co.Types))
	}
	f, err := os.Create(*outPath)
	if err != nil {
		die(err)
	}
	enc := json.NewEncoder(f)
	enc.SetIndent("", " ")
	if err := enc.Encode(res); err != nil {
		die(err)
	}
	if err := f.Close(); err != nil {
		die(err)
	}
}
