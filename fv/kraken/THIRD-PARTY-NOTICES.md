# Third-party notices: source attribution of derived evidence files

This repository's `LICENSE` is Apache-2.0. Some files under `fv/kraken/` are derived from other projects. This file names those files, how they were produced, and the upstream project and licence name.
Counts are `git ls-files` counts. Paths are relative to `fv/kraken/`.
Scope: the path lists come from program scans of the tracked files for Go source, generated Go, disassembly, `-m` and diff lines (section H). They are best-effort, not a guarantee of completeness; other files may quote short fragments of generated code or upstream identifiers.

## A. Machine code compiled in a Prysm tree (Go 1.26.10)

- Paths: `prysm/go1.26.10/**/norm/*.S` (268), `prysm/go1.26.10/**/target.objdump` (17), `prysm/go1.26.10/**/data/*` (162), `prysm/go1.26.10/**/link*/RESULT` (18). Total 465.
- What: normalised disassembly (`.S`), filtered `go tool objdump -gnu` output, byte extracts of ELF data symbols, and link-check tables.
- The `.S` files hold functions of the Prysm packages `proto/prysm/v1alpha1`, `proto/engine/v1` and `consensus-types/primitives`.
- Before the build, the 16 `*.ssz.go` files of the tree were replaced by family B output (`README.md` section 3, step 3).
  So the `proto/*` method bodies come from this repository's generator. `consensus-types/primitives` is Prysm source.
- The data extracts and tables also name or hold Go runtime and standard-library symbols (for example `runtime.memmove`, type descriptors).
- Produced by: `link/conv.py --norm` and `link/check.py` on an ELF cross-compiled by Go 1.26.10 (`GOOS=linux GOARCH=amd64 GOAMD64=v1 CGO_ENABLED=0 -tags purego -trimpath`).
- ELF sha256 `c6403c02a110ffd6fe6d31a3c89cd395ac457b5d62e60e2e611b8ab9a8dd911e` (`prysm/go1.26.10/build-ids.txt`).
- `opt-r1/` uses ELF sha256 `3ef7ac890ba1a797fb90877b84ad1a6ffe0ac283f77c10b09ffb2c8cd7b7f602` (`prysm/go1.26.10/opt-r1/build-ids.txt`). It used generator `ca191bb`, not `698c202`. The ELFs are not committed.
- Upstream: Prysm, <https://github.com/OffchainLabs/prysm>, commit `ab15ff70c72a568c870b2de662474685a95de294` (`README.md` section 2). Licence: GNU General Public License version 3 (root `LICENSE.md`).
- Upstream: Go, <https://go.dev/>, <https://github.com/golang/go>. Licence: BSD-3-Clause (Go 1.26.10 `LICENSE`).

## B. Generator output for Prysm type definitions

- Paths: `prysm/_generated/**` (17: 16 `*.ssz.go`, `SHA256SUMS`).
- What: output of this repository's generator (`sszgen/`, `ssz/` at `698c2025a73a296b55b95744a8408f3b03b2546b`) applied to Prysm type definitions at the commit of family A.
- The input specs are the configs that `gen/prysm-gen.sh` names. Upstream and licence of the inputs: Prysm, as in family A.

## C. Diffs against Prysm's committed generated files

- Paths: `prysm/diff/**` (1: `gendiff.json`). The 16 `*.ssz.go.diff` files are not tracked. `gendiff.json` holds file names, counts and commit titles only.
- What: unified diffs between the `*.ssz.go` files in the Prysm tree and family B. The removed lines are Prysm text.
- Upstream: Prysm, as in family A.

## D. Driver sources that import Prysm

- Paths: `prysm/go1.26.10/**/*-main.go.txt` (13), `prysm/go1.26.10/opt-r1/bench/bench_test.go.txt` (1). Total 14.
- What: copies of the scratch `main` and benchmark packages used to build, check or benchmark the family A ELFs. They import Prysm packages.
- Written for this project. Upstream of the imported packages: Prysm, as in family A.

## E. Go 1.26.3 ELF of this repository's own target

- Paths: `link/out/p1bin-amd64`, `link/out/p1bin-amd64.nm`, `link/out/target.objdump`, `link/out/RESULT`, `link/out/build-ids.txt`, `link/out/norm/*` (30), `link/out/data/*` (23). Total 58.
- What: the ELF built from `cmd/p1bin`, `target/` and `ssz/` by Go 1.26.3 (`link/build.sh`), its symbol table, filtered disassembly, link tables, `.S` and data extracts.
- ELF sha256 `9c850c97066b9d33d6e4c5ef0a385dcbe2c984ae774a527cdedd18d2b72ac501` (`link/out/build-ids.txt`).
- Besides this repository's code, `p1bin-amd64.nm` shows linked code of the Go runtime and standard library,
  `github.com/prysmaticlabs/gohashtree`, `github.com/minio/sha256-simd` and `github.com/klauspost/cpuid/v2` (versions in the root `go.mod`).
- The `.S` files in `link/out/norm/` hold only `ssz.*`, `target.*` and `target_prysm.*` functions.
- Upstream: Go, as in family A (the BSD-3-Clause name was read from the Go 1.26.10 tree, not from a Go 1.26.3 tree).
- The ELF build info also lists `github.com/OffchainLabs/go-bitfield`. `p1bin-amd64.nm` has no symbol of it. The licences of gohashtree, sha256-simd, cpuid and go-bitfield were not read for this file.

## F. Prysm field definitions in the target package

- Paths: `target/prysm/types.go`, `target/prysm/types.ssz.go` (2).
- What: the SSZ fields of `Checkpoint` and `AttestationData`, copied from Prysm v7.1.8 (`51b5a75ebbadf05af22bd2601b5baf7a9e99b66d`) per the header of `types.go`, and the generator output for them.
- Upstream: Prysm, as in family A. `LICENSE.md` at `51b5a75` is also GNU General Public License version 3.

## G. Prysm type records and other text derived from Prysm files

- `prysm/ir/ir-mainnet.json`, `prysm/ir/ir-minimal.json` (2): the generator IR of the Prysm types, with Go field names, types, tags and gc amd64 offsets.
  Produced by `gen/invtool` (front end of generator `698c202`) in the Prysm tree, via `gen/prysm-gen.sh`, then `gen/type_inventory.py reduce`.
- `prysm/inventory.json`, `prysm/TYPES.md` (2) and `prysm/go1.26.10/e2e/**/*.desc.json` (24): type sets, counts and SSZ descriptors made from the IR
  by `gen/type_inventory.py build`, `gen/type_list_document.py` and `gen/desc/producer.py`.
- `prysm/go1.26.10/e2e/gcflags-m2.txt` (1): Go 1.26.10 `-gcflags=-m=2` output on the Prysm tree. It prints inlined Prysm function bodies.
- `prysm/go1.26.10/prysm-go.mod.diff` (1): a diff of Prysm `go.mod`; its context lines are Prysm text.
- `gen/frozen/THEOREMS.json` (1): obligation lists written by `gen/frozen/build_lists.py` with the site enumerator `gen/obligations.py`. Its 2752 `prysm.obligations` records
  quote a `guard` and a `ret` line of family B `mainnet/*.ssz.go` (132 types, 523 distinct pairs). Its `hand_case` records quote lines of `target/**/*.ssz.go`.
- `prysm/go1.26.10/e2e/negative/result.json` (1): negative-test records; their `diff` fields hold unified diffs of family A `.S` lines. Total 32. Upstream: Prysm, as in family A.

## H. Files that only name upstream symbols

- Other files under `fv/kraken/` (850 tracked files outside sections A to G) may name Prysm or Go packages, types, functions, tests or ELF addresses, or quote short instruction fragments of families A and E.
  Examples: `prysm/go1.26.10/functions.json`, `prysm/go1.26.10/kparse*` (4) and the negative-test case files `**/negcases*.json` (33).
- A program scan of these files for Go source fragments (`func `, `return `, `{ return`, `inline call to`, `can inline`) found these quotes:
  - doc comments in `lean/Prysm/` quote short excerpts of family B methods and of Prysm `consensus-types/primitives` (`lean/Prysm/Epoch/DecodeAccept.lean` lines 9-11, `lean/Codec/Uint64Decoder.lean` lines 7-8);
- The other hits are this project's own tool code or prose. The `.py`, `.go` and `.sh` hits were not each read. The files were not each read in full.
- The scans matched these patterns only: Go `if … {`, `return `, `func (`, `dst = append`, `binary.LittleEndian`, `ssz.Err`, `fmt.Errorf(`, `for … := range`, AT&T/objdump instruction lines and `-m` lines. Short one-line quotes can also occur in other files.
- `lean/**/*.S` (13) are stubs written for this project under Go runtime and `ssz` symbol names. They are not disassembly.

## I. Lean dependencies and skill material

- Kraken, EthLib and their dependencies are fetched by Lake at the revisions in `lean/lake-manifest.json`. They are not committed (`**/.lake/` is ignored).
- Lean files such as `lean/Prysm/Checkpoint/Code.lean` include family A and E `.S` files by path. They do not copy them.
- Text adapted from third-party agent-skill material is attributed in `.claude/skills/maintaining-methodical-fv/references/ATTRIBUTION.md`.

## Per-directory licence files in the Prysm tree

- At `ab15ff70`, the Prysm tree tracks `LICENSE.md` (GPL-3.0) and seven subdirectory licence files, none in the packages of family A.
- `proto/eth/LICENSE` is Apache-2.0. `proto/eth` is not a family A package.
- `encoding/ssz/equality/deep_equal.go` has a Go Authors copyright header. No `encoding/ssz` function is in family A.

## What this file is not

- It is a source attribution only. It makes no statement on licence compatibility or on what redistribution requires.
- The upstream licence texts are not reproduced here. They are at the upstream URLs at the pinned commits and versions.
- Anyone who redistributes these files should review the upstream terms.
