# TOOLS: fixed versions and commands

## Fixed versions

| Item | Value | Where it is fixed |
| --- | --- | --- |
| Generator | Source (`sszgen/`, `ssz/`) = `syjn99/ssz-gen-fixes` `698c202`. Merge base `2d0150b` | `git rev-parse HEAD:ssz`, `link/out/build-ids.txt` |
| Go | 1.26.3, `GOOS=linux GOARCH=amd64 GOAMD64=v1 CGO_ENABLED=0 -tags purego -trimpath`, standard runtime | `link/build.sh`, `link/out/build-ids.txt` |
| ELF | sha256 `9c850c97…c501` | `link/out/build-ids.txt` |
| Kraken | `6064eecbb730a1152aa6ed891a155d3a92a4f298` (AeneasVerif/kraken main) | `lean/lakefile.toml` `rev`, `lean/lake-manifest.json` |
| Lean | `leanprover/lean4:nightly-2026-09-21` | `lean/lean-toolchain` |
| EthLib | `862185680cf23ccf54d44eb25b63b26c5020597b` | `lean/lakefile.toml` `rev` |
| Source of the reduced Prysm types | v7.1.8 `51b5a75ebbadf05af22bd2601b5baf7a9e99b66d`, Checkpoint and AttestationData schemas | `target/prysm/types.go` |
| gohashtree, go-bitfield | `v0.0.5-beta`, `v0.0.0-20260504143531-5cbb6d0f5f2e` | `go.mod` |
| objdump, LLVM, clang | `go tool objdump -gnu`, `llvm-objdump` (independent decoding), `clang --target=x86_64-linux-gnu` (reassembly) | `tool()` in `link/check.py` |
| 1c Prysm source | `ab15ff70c72a568c870b2de662474685a95de294` (slice + `ssz-size`), generation only in temporary trees. Replaced history: `5ac1d028f5`/`45394e5` | `prysm/go1.26.10/MANIFEST.md` |
| 1c Go (experiment baseline) | 1.26.10, cross-compiled for linux/amd64 on a linux/arm64 host, `GOAMD64=v1 CGO_ENABLED=0 -tags purego -trimpath`. The Go 1.26.3 theorems do not transfer | `prysm/go1.26.10/build-ids.txt` |
| 1c ELF | sha256 `c6403c02…911e` (not committed, the rebuild command is in MANIFEST). Link table `prysm/go1.26.10/link/RESULT` | `prysm/go1.26.10/build-ids.txt` |
| Third-party notices | Sources of derived evidence files, upstream projects, license names | `THIRD-PARTY-NOTICES.md` |

## Target generation

Run from the repository root.

```sh
P=github.com/OffchainLabs/methodical-ssz/fv/kraken/target
go run ./cmd/ssz gen --package $P --output=fv/kraken/target/types.ssz.go --type-names=Scalars,FixedVec,ListU64
go run ./cmd/ssz gen --package $P --output=fv/kraken/target/types1b.ssz.go --type-names=BitVec,Nested,ListC,BitL
go run ./cmd/ssz gen --package $P/prysm --output=fv/kraken/target/prysm/types.ssz.go --type-names=Checkpoint,AttestationData
fv/kraken/link/build.sh          # ELF, objdump, nm, norm/*.S, data/*.data, build-ids.txt
```

## Tools

| Tool | Role | Run |
| --- | --- | --- |
| `link/check.py` | ELF ↔ objdump ↔ `.S` ↔ Host labels and global addresses (a)–(e), data files = ELF (f), `link/out/RESULT` | `python3 -B fv/kraken/link/check.py fv/kraken/link/out [--selftest]` |
| `link/data.py` | ELF data items to `link/out/data/<id>.data` | `python3 -B fv/kraken/link/data.py fv/kraken/link/out` |

Run `go run` and `go test` with `GOROOT=$(go env GOROOT)`.

On 2026-11-12, commit `84a4747` removed these tools: `lean/tools/axioms.sh` (`AXIOMS.txt`, `AXIOMS-ALL.txt`), `lean/tools/wit/` (`layout.go`, `goval.py`, witness generator) and `lean/tools/RegressFix2.lean`.
It also removed `negative/run.sh`, `gen/x4/`, `gen/x5/`, `semtest/` and the vcgen evaluation `vcgen/` (sgraf812/kraken `a4cce2e`, not adopted).
Tag `archive/fv-before-workflow` holds them and their table rows.

## ELF data include (fix 3, interface v1)

The rodata and runtime data that the theorems read are definitions that include ELF bytes, not hand constants.
This is the same structure as the code include (`Fk/Code.lean`, `include_x64_rt`).

- Extractor: `link/data.py`. It reads the bytes of the item table (id, label, offset, length) from the ELF and `p1bin-amd64.nm`.
- Data files: `link/out/data/<id>.data`. One file for each item. They are text.
- Lean: the command `data_include <id>` in `Fk/Include.lean` reads `../link/out/data/<id>.data`. `Fk/Data.lean` calls it with one line for each item.
- Definitions: `Fk.Data.<id> : List UInt8` (bytes), `Fk.Data.<id>_addr : BitVec 64` (= `(label "<label>" + <offset>).toBitVec`). An item with only an address has only `_addr`.
- The bytes of an item with pointer words (itab, type descriptor) depend on `[Host]`. A word is `Int.toBytes 8 (label "<s>" + <o>).toBitVec.toInt`.
- The premise form of the theorems stays `Eq (bytes.At addr)`. Kraken data memory is separate from code (con-agua DESIGN `ldc`).

Data file syntax (one directive per line, a line that starts with `#` is a comment):

| Directive | Meaning |
| --- | --- |
| `at <label> <offset>` | First directive. Address of the item = label + offset. The label is the name that `conv.py` cleaned |
| `bytes <hex> ...` | Raw bytes (two hexadecimal digits, separated by spaces) |
| `word <label> <offset>` | 8-byte little-endian absolute address = label + offset (relocation word) |

Check: `link/check.py` compares all data files with the ELF. `python3 -B link/data.py --check link/out` checks that the regenerated result is equal to the tracked files (if not, exit 1).
Line and token rules (shared by the two readers, `bytes` are lowercase two-digit hexadecimal, offsets are decimal digits only): lines are split at `\n`. All other characters are printable ASCII. If a `\r`, a tab or a control character occurs, both `check.py` (f) and `data_include` reject the file.
`bytes` must be equal to the file bytes of that range, and `word` must be equal to the 8-byte value at that location = symbol address + offset. The sha256 of the files goes into the same hash binding as (a).
Rebuild: register `link/out/norm`, `link/out/data` and `lean/Fk/*.S` as inputs in the `needs` of the `Fk` library in `lean/lakefile.toml`.

Item table (v1). The offsets are the values for this ELF (`9c850c97…c501`).

The last column names the modules that had the hand constants at fix 3. Most of these modules were removed on 2026-11-12. `Fk/Data.lean` still includes all items.

| id | Label + offset | Length | Kind | What it replaces |
| --- | --- | --- | --- | --- |
| `blFmtB` | `go_string._` + 526 | 5 | rodata string `B: %w` | `BlMarshal.lean blFmtB` |
| `bvFmtJ` | `go_string._` + 511 | 5 | rodata string `J: %w` | `BvSpec.lean bvFmtJ` |
| `vbvFmt` | `go_string._` + 27706 | 35 | rodata string (ValidateBitvector) | `Vbv.lean vbvFmt`, `bvRO` |
| `lcFmtZero` | `go_string._` + 39370 | 53 | rodata string | `LcReject.lean lcFmtZero` |
| `lcFmtShort` | `go_string._` + 42000 | 63 | rodata string | `LcReject.lean lcFmtShort` |
| `lcFmtOrder` | `go_string._` + 42579 | 67 | rodata string `offset %d is not greater …` | New item (fix 3, offset order reject step X5) |
| `vblMsgE` | `go_string._` + 33605 | 42 | rodata string (ValidateBitlist) | `Vbl.lean vblMsgE`, `vblRO` |
| `vblMsgZ` | `go_string._` + 13272 | 21 | rodata string | `Vbl.lean vblMsgZ` |
| `vblMsgB` | `go_string._` + 5743 | 13 | rodata string | `Vbl.lean vblMsgB` |
| `luFmtTooBig` | `go_string._` + 40290 | 56 | rodata string | `LuRejectCall.lean luFmtTooBig` |
| `luFmtMis` | `go_string._` + 42646 | 68 | rodata string | `LuRejectCall.lean luFmtMis` |
| `lcFmtItems` | `go_string._` + 2158 | 9 | rodata string `Items: %w` | New item (fix 3 review M4, element error propagation) |
| `errorStringItab` | `go_itab._errors.errorString_error` + 0 | 32 | Full itab (3 words: inter, Type, Fun[0]) | The itab check of the old (h) |
| `errorStringPtrType` | `type__` + 68096 | 56 | abi.PtrType of `*errors.errorString` (abi.Type 48 + Elem) | The pointer kind check of the old (h), the zero descriptor of the witnesses |
| `intType` | `type__` + 49184 | 48 | abi.Type of `int` | `LuRejectCall.lean luTW`, the old (h) |
| `uint64Type` | `type__` + 49120 | 48 | abi.Type of `uint64` | New item (fix 3, offset order reject step X5, `%d` uint64 argument) |
| `staticuint64s` | `runtime.staticuint64s` + 0 | 2048 | uint64 0..255 table | `Contracts.lean StaticBox`, the old (h) |
| `ErrSize` and the other error globals, 6 in total | `ssz.Err*` + 0 | 0 | Address only (the value comes from runtime initialization) | Global initialization premise of the witnesses (fix 3, error globals step X3) |

Trust limits (fix 3 review M3):
- The check tools do not read the Lean sources. We read from the theorem statement whether a theorem uses these definitions. No tool confirms it.
- Check (f) examines only "file = ELF bytes at that address". For items that the proved code accesses with `lea` (format strings, `int` and `uint64` type words), the proofs bind the id ↔ address. For the four items that only contracts use (`vblMsgE/Z/B`, `staticuint64s`), the contract hypotheses bound them. The contracts that used `vblMsgE/Z/B` (`Fk/Vbl.lean`) were removed on 2026-11-12. No kept module except `Fk/Data.lean` names these three items.
- Whether the content and verb form of a format string agree with the contracts (`FmtErrorfWC`, `DWC`, `DDC`) is a contract hypothesis. Lean binds only the length and the absence of `%`.

Error global ids: `ErrSize`, `ErrInvalidSerialization`, `ErrInvalidVariableOffset`, `ErrListTooBig`, `ErrBytesLength`, `ErrIncorrectListSize`.
The theorems use `label "ssz.Err*"` directly, as now. This is a symbol, not a hand number.

## Known violations (root `AGENTS.md`: no absolute paths, session ids or run-directory names)

Item S4 of the first review of the audit fixes. The files below break the rule. They are generated records or earlier files, so we did not fix them all at one time.
New records use only repository-relative paths and gate job numbers. `negative.py` writes the work directory of the results as `<work>` (from commit `094e51e`).

- `prysm/go1.26.10/e2e/negative/result.json`, `prysm/go1.26.10/e2e/scal/negative-result.json`: the `first_error` and `later_resource_error` of earlier rows contain absolute paths of run directories.
- `prysm/go1.26.10/e2e/COST.json`, `prysm/go1.26.10/e2e/scal/TEMPLATE-COST.json`, `prysm/go1.26.10/e2e/scal/BASELINE.json`: the `records`, `logs` and `events` of `source` are absolute paths of run directories.
- `lean/lakefile.toml` lines 57 and 75: the comments contain run names. Line 88 and earlier records (past checkpoint lines in `REPORT.md`, `HISTORY.md` and `prysm/FINDINGS.md`) contain session numbers.
- Section 7 of `prysm/FINDINGS.md`: one line contains an absolute path of a controller file.
- Other earlier files. The output of the check command below is the full list. (`gen/x5/x5run.py` and the `memopt/` records were in this list. They were removed on 2026-11-12.)
- Two Python bytecode files that exist only in git history (items S1, S2 of the review of the H3 and OPT-R1 integrations). Both are `gen/e2e/__pycache__/negative.cpython-311.pyc`.
  `094e51e` added the first and `ae1ea1a` deleted it. `ff81bc7` added the second and `a70492c` deleted it.
  They are not in the current tree. They cannot be deleted without a history rewrite, and the policy prohibits rewrites.
  They contain no secrets (regular expression check of that review). The two files contain container paths of the work tree.
  The user decides how to treat them before publication (item S1 of that review). `fv/kraken/.gitignore` now ignores `__pycache__/` and `*.pyc`.

Check command: `git grep -nE "/workspace|fve2e-" -- fv/kraken ':!fv/kraken/lean/.lake'`.
