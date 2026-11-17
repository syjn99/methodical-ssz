# prysm: the Prysm target and its evidence files

This directory holds the Prysm target: the type inventory, the generator IR, the generated Go and the link set.
It also holds the Go differential cases and the check records.
Paths in sections 1 and 3 are relative to this directory.
Paths in the table of section 2 are relative to `go1.26.10/`.
A path that starts with `gen/` or `lean/` is relative to `fv/kraken/`.
How to build the target ELF again is in `../README.md` section 3.
`../README.md` section 7 gives the writer, the command and the check of each kind of file here.

## 1. Content

| Path | Content | Written by |
| --- | --- | --- |
| `ir/ir-mainnet.json`, `ir/ir-minimal.json` | The reduced generator IR (intermediate representation) of each type, with the Go field layout `go_fields` | `gen/type_inventory.py reduce` |
| `inventory.json` | The type inventory: every generated type, its fields and its delegations | `gen/type_inventory.py build` |
| `TYPES.md` | The type list of the inventory | `gen/type_list_document.py` |
| `proof-inventory.md`, `proof-inventory.json` | The per-method table of theorems, witnesses and paths not proved | `gen/tools/proof_inventory.py run` (with the outputs of `inventory_decls.lean` and of an axioms gate run on the built tree) |
| `_generated/` | The Go files that the pinned generator wrote for Prysm, and their `SHA256SUMS` | `gen/prysm-gen.sh` (no tool writes `SHA256SUMS`) |
| `diff/` | A classification of the differences between these files and the Prysm files | `gen/generated_go_diff.py` |
| `differential-cases/` | The Go differential cases, one file `<package>.<Type>.json` per Go type | `gen/checks/differential.py cases` |
| `go1.26.10/` | The target namespace of the Go 1.26.10 ELF (section 2) | |

## 2. The target namespace `go1.26.10/`

All files here belong to one ELF.
Do not mix them with the files of another ELF.

| Path | Content |
| --- | --- |
| `build-ids.txt` | The Go version, the build flags and the sha256 of the ELF, its disassembly and its symbol listing |
| `prysm-target-main.go.txt`, `prysm-go.mod.diff` | The `main` package of the binary (`gen/keepalive.py`) and the `go.mod` change in the Prysm tree (hand) |
| `ssz-methods.json` | Every SSZ method of the ELF. It is the denominator of the inventory |
| `functions.json`, `parser-result.json` | The functions with a converted `.S` file, and which of them the Kraken parser reads. `gen/kraken-parser/summarize_parser_log.py` writes `parser-result.json` from a parser log that is not tracked (`../README.md` section 3) |
| `link-set.tsv` | The item table of the link set: one row per function and per data item, with its Go type and what it is |
| `link-set/` | The one link set of the proved functions: `target.objdump`, `norm/*.S`, `norm/all.S`, `data/*.data` and `RESULT`. `gen/checks/link_set.py` writes it from `link-set.tsv`, and `link/check.py` writes `RESULT` |
| `evidence/` | The `Desc` files `<package>.<Type>.desc.json` that the `Desc` checker accepted. The headers of `lean/Prysm/*/SpecChecker.lean` name this directory |

## 3. Files that are inputs of checks

Do not edit these files by hand.
Make them again with their generator.

- The `.S` and `.data` files of the link set.
  Lean includes them, and the link check compares them with the ELF.
- `ir/*.json` and `inventory.json`.
  The generators and the `Desc` checker read them.
- The `*.desc.json` files.
  The `Desc` checker accepted them, and the header of each `*SpecChecker.lean` gives their sha256.
- The case files of `differential-cases/`.
  `gen/checks/differential.py cases` writes them again, and the Go program reads them.
- `go1.26.10/build-ids.txt` and `go1.26.10/ssz-methods.json`.
  `gen/tools/proof_inventory.py` reads them.
  It checks the symbol listing against the sha256 in `build-ids.txt`.

`go1.26.10/link-set.tsv` is a hand table.
`gen/checks/link_set.py` reads it and checks each data row against the converted code.

`go1.26.10/parser-result.json` is also an input: `gen/type_list_document.py` reads it.
Do not edit it by hand either.

The other JSON files and `go1.26.10/link-set/RESULT` are outputs of tool runs.
A new run writes them again.
Do not edit them to change a result.
