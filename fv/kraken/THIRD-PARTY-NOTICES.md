# Third-party notices: source attribution of derived evidence files

This repository's `LICENSE` is Apache-2.0.
Some files under `fv/kraken/` are derived from other projects.
This file names those files, the tool that makes them, and the upstream project and licence name.
Paths are relative to `fv/kraken/`.
Scope: the path lists come from text scans of the tracked files (section "Files that only name upstream symbols").
The lists can be incomplete.
Other files can quote short fragments of generated code or upstream identifiers.

## Machine code compiled in a Prysm tree (Go 1.26.10)

- Paths: `prysm/go1.26.10/**/norm/*.S`, `prysm/go1.26.10/**/target.objdump`, `prysm/go1.26.10/**/data/*`, `prysm/go1.26.10/**/link*/RESULT`.
- What: normalised disassembly (`.S`), filtered `go tool objdump -gnu` output, byte extracts of ELF data symbols, and link-check tables.
- The `.S` files hold functions of the Prysm packages `proto/prysm/v1alpha1`, `proto/engine/v1` and `consensus-types/primitives`.
- Before the build, the generated Prysm Go replaces the `*.ssz.go` files of the tree (`README.md` section 3, step 3).
  So the `proto/*` method bodies come from this repository's generator.
  `consensus-types/primitives` is Prysm source.
- The data extracts and tables also name or hold Go runtime and standard-library symbols (for example `runtime.memmove`, type descriptors).
- Produced by: `link/convert_objdump.py --norm` and `link/check.py` on an ELF cross-compiled by Go 1.26.10 (`GOOS=linux GOARCH=amd64 GOAMD64=v1 CGO_ENABLED=0 -tags purego -trimpath`).
- The file `prysm/go1.26.10/build-ids.txt` records the ELF sha256.
- The ELF is not committed.
- Upstream: Prysm, <https://github.com/OffchainLabs/prysm>, at the Prysm source commit of `README.md` section 2.
  Licence: GNU General Public License version 3 (root `LICENSE.md`).
- Upstream: Go, <https://go.dev/>, <https://github.com/golang/go>. Licence: BSD-3-Clause (Go 1.26.10 `LICENSE`).

## Generator output for Prysm type definitions

- Paths: `prysm/_generated/**` (the generated `*.ssz.go` files and `SHA256SUMS`).
- What: output of this repository's generator (`sszgen/`, `ssz/` at the generator commit of `README.md` section 2).
  The inputs are the Prysm type definitions at the Prysm commit of the Prysm machine code.
- The input specs are the configs that `gen/prysm-gen.sh` names.
  Upstream and licence of the inputs: Prysm, as for the Prysm machine code.

## Diffs against Prysm's committed generated files

- Paths: `prysm/diff/**` (`generated-go-diff.json`).
  The `*.ssz.go.diff` files are not tracked.
  `generated-go-diff.json` holds file names, counts and commit titles only.
- What: unified diffs between the `*.ssz.go` files in the Prysm tree and the generated Prysm Go.
  The removed lines are Prysm text.
- Upstream: Prysm, as for the Prysm machine code.

## Driver sources that import Prysm

- Paths: `prysm/go1.26.10/**/*-main.go.txt`.
- What: copies of the scratch `main` packages used to build or check the Prysm ELF.
  They import Prysm packages.
- Written for this project.
  Upstream of the imported packages: Prysm, as for the Prysm machine code.

## Prysm type records and other text derived from Prysm files

- `prysm/ir/ir-mainnet.json`, `prysm/ir/ir-minimal.json`: the generator IR of the Prysm types, with Go field names, types, tags and gc amd64 offsets.
  Produced by `gen/inventory-tool` (front end of the generator at the generator commit of `README.md` section 2) in the Prysm tree, via `gen/prysm-gen.sh`, then `gen/type_inventory.py reduce`.
- `prysm/inventory.json`, `prysm/TYPES.md` and `prysm/go1.26.10/evidence/*.desc.json`: type sets, counts and SSZ descriptors made from the IR
  by `gen/type_inventory.py build`, `gen/type_list_document.py` and `gen/desc/producer.py`.
- `prysm/go1.26.10/prysm-go.mod.diff`: a diff of Prysm `go.mod`; its context lines are Prysm text.
- Upstream: Prysm, as for the Prysm machine code.

## Files that only name upstream symbols

- Other tracked files under `fv/kraken/` can name Prysm or Go packages, types, functions, tests or ELF addresses.
  They can quote short instruction fragments of the Prysm machine code.
  Examples: `prysm/go1.26.10/functions.json`, `prysm/go1.26.10/parser-result.json` and the negative-test case files `gen/checks/negative-cases/*.json`.
- A program scan of these files for Go source fragments (`func `, `return `, `{ return`, `inline call to`, `can inline`) found these quotes:
  - doc comments quote short excerpts of generated Prysm Go methods and of Prysm `consensus-types/primitives`.
    Examples are `lean/Prysm/Epoch/DecodeRejectSize.lean` line 14 and `lean/Codec/Uint64Decoder.lean` lines 7-8.
- The other hits are this project's own tool code or prose.
- The scans match these patterns only: Go `if … {`, `return `, `func (`, `dst = append`, `binary.LittleEndian`, `ssz.Err`, `fmt.Errorf(`, `for … := range`.
  They also match AT&T and objdump instruction lines and `-m` lines.
  Short one-line quotes can also occur in other files.
- `lean/**/*.S` are stubs written for this project under Go runtime and `ssz` symbol names.
  They are not disassembly.

## Lean dependencies and skill material

- Kraken, EthLib and their dependencies are fetched by Lake at the revisions in `lean/lake-manifest.json`.
  They are not committed (`**/.lake/` is ignored).
- Lean files such as `lean/Prysm/Checkpoint/Code.lean` include `.S` files of the Prysm machine code by path.
  They do not copy them.
- `gen/checks/decl_dump.lean` and `gen/checks/decl_drift.py` use an idea of the `maintaining-lean-projects` skill of ethpandaops/panda (MIT, pull request 396).
  The idea is a comparison of each declaration with a reviewed base.
  No text is copied.

## Per-directory licence files in the Prysm tree

- At the pinned Prysm commit, the Prysm tree tracks `LICENSE.md` (GPL-3.0) and other subdirectory licence files.
  None of them is in a package of the Prysm machine code.
- `proto/eth/LICENSE` is Apache-2.0.
  `proto/eth` is not a package of the Prysm machine code.
- `encoding/ssz/equality/deep_equal.go` has a Go Authors copyright header.
  No `encoding/ssz` function is in the Prysm machine code.

## What this file is not

- It is a source attribution only.
  It makes no statement on licence compatibility or on what redistribution requires.
- The upstream licence texts are not reproduced here.
  They are at the upstream URLs at the pinned commits and versions.
- Anyone who redistributes these files should review the upstream terms.
