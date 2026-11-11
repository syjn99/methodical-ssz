# Third-party notices: source attribution of derived evidence files

This repository's `LICENSE` is Apache-2.0. Some files under `fv/kraken/` are derived from other projects. This file names those files, how they were produced, and the upstream project and licence name.
Counts are `git ls-files` counts. Paths are relative to `fv/kraken/`.

## A. Machine code compiled from Prysm source (Go 1.26.10)

- Paths: `prysm/go1.26.10/**/norm/*.S` (176), `prysm/go1.26.10/**/target.objdump` (6), `prysm/go1.26.10/**/data/*` (33), `prysm/go1.26.10/**/link/RESULT` (6). Total 221.
- What: normalised disassembly (`.S`), filtered `go tool objdump -gnu` output, byte extracts of ELF data symbols, and link-check tables.
- The `.S` files hold functions of the Prysm packages `proto/prysm/v1alpha1`, `proto/engine/v1` and `consensus-types/primitives`.
- The data extracts and tables also name or hold Go runtime and standard-library symbols (for example `runtime.memmove`, type descriptors).
- Produced by: `link/conv.py --norm` and `link/check.py` on an ELF cross-compiled by Go 1.26.10 (`GOOS=linux GOARCH=amd64 GOAMD64=v1 CGO_ENABLED=0 -tags purego -trimpath`).
- ELF sha256 `c6403c02a110ffd6fe6d31a3c89cd395ac457b5d62e60e2e611b8ab9a8dd911e` (`prysm/go1.26.10/build-ids.txt`).
- `opt-r1/` uses ELF sha256 `3ef7ac890ba1a797fb90877b84ad1a6ffe0ac283f77c10b09ffb2c8cd7b7f602` (`prysm/go1.26.10/opt-r1/build-ids.txt`). The ELFs are not committed.
- Upstream: Prysm, <https://github.com/OffchainLabs/prysm>, commit `ab15ff70c72a568c870b2de662474685a95de294` (`prysm/go1.26.10/MANIFEST.md`). Licence: GNU General Public License version 3 (root `LICENSE.md`).
- Upstream: Go, <https://go.dev/>, <https://github.com/golang/go>. Licence: BSD-3-Clause (Go 1.26.10 `LICENSE`).

## B. Generator output for Prysm type definitions

- Paths: `prysm/_generated/**` (18: 16 `*.ssz.go`, `GEN_RC`, `SHA256SUMS`).
- What: output of this repository's generator (`sszgen/`, `ssz/` at `698c2025a73a296b55b95744a8408f3b03b2546b`) applied to Prysm type definitions at the commit of family A.
- The input specs are listed in `prysm/_generated/GEN_RC`. Upstream and licence of the inputs: Prysm, as in family A.

## C. Diffs against Prysm's committed generated files

- Paths: `prysm/diff/**` (17: 16 `*.ssz.go.diff`, `gendiff.json`).
- What: unified diffs between the `*.ssz.go` files in the Prysm tree and family B. The removed lines are Prysm text.
- Upstream: Prysm, as in family A.

## D. Driver sources that import Prysm

- Paths: `prysm/go1.26.10/**/*-main.go.txt` (7).
- What: copies of the scratch `main` packages used to build or check the family A ELFs. They import Prysm packages.
- Written for this project. Upstream of the imported packages: Prysm, as in family A.

## E. Go 1.26.3 ELF of this repository's own target

- Paths: `link/out/p1bin-amd64`, `link/out/p1bin-amd64.nm`, `link/out/target.objdump`, `link/out/RESULT`, `link/out/build-ids.txt`, `link/out/norm/*` (30), `link/out/data/*` (23). Total 58.
- What: the ELF built from `cmd/p1bin`, `target/` and `ssz/` by Go 1.26.3 (`link/build.sh`), its symbol table, filtered disassembly, link tables, `.S` and data extracts.
- ELF sha256 `9c850c97066b9d33d6e4c5ef0a385dcbe2c984ae774a527cdedd18d2b72ac501` (`link/out/build-ids.txt`).
- Besides this repository's code, `p1bin-amd64.nm` shows linked code of the Go runtime and standard library,
  `github.com/prysmaticlabs/gohashtree`, `github.com/minio/sha256-simd` and `github.com/klauspost/cpuid/v2` (versions in the root `go.mod`).
- The `.S` files in `link/out/norm/` hold only `ssz.*`, `target.*` and `target_prysm.*` functions.
- Upstream: Go, as in family A (the BSD-3-Clause name was read from the Go 1.26.10 tree, not from a Go 1.26.3 tree).
- The licences of gohashtree, sha256-simd and cpuid were not read for this file.

## F. Prysm field definitions in the target package

- Paths: `target/prysm/types.go`, `target/prysm/types.ssz.go` (2).
- What: the SSZ fields of `Checkpoint` and `AttestationData`, copied from Prysm v7.1.8 (`51b5a75ebbadf05af22bd2601b5baf7a9e99b66d`) per the header of `types.go`, and the generator output for them.
- Upstream: Prysm, as in family A. The licence name was read at `ab15ff70`, not at `51b5a75`.

## G. Lean dependencies and skill material

- Kraken, EthLib and their dependencies are fetched by Lake at the revisions in `lean/lake-manifest.json`. They are not committed (`**/.lake/` is ignored).
- Lean files such as `lean/E2e/Code.lean` include family A and E `.S` files by path. They do not copy them.
- Text adapted from third-party agent-skill material is attributed in `.claude/skills/maintaining-methodical-fv/references/ATTRIBUTION.md`.

## Per-directory licence files in the Prysm tree

- At `ab15ff70`, the Prysm tree tracks `LICENSE.md` (GPL-3.0) and seven subdirectory licence files, none in the packages of family A.
- `proto/eth/LICENSE` is Apache-2.0. `proto/eth` is not a family A package.
- `encoding/ssz/equality/deep_equal.go` has a Go Authors copyright header. No `encoding/ssz` function is in family A.

## What this file is not

- It is a source attribution only.
- It makes no statement on licence compatibility or on what redistribution requires.
- The upstream licence texts are not reproduced here. They are at the upstream URLs at the pinned commits and versions.
- Anyone who redistributes these files should review the upstream terms.
