# MANIFEST: phase 1c experimental baseline Go 1.26.10

This directory is the target-binary record of phase 1c. It is a separate namespace.
Do not mix it with the Go 1.26.3 ELF (`9c850c97…c501`) or with its theorems, tables and data files.

## 1. Decisions (user decision 2026-11-09, run `fvpar-20261109T150658Z-f1d44da4` DECISIONS D1)

- The Prysm source is `ab15ff70c72a568c870b2de662474685a95de294`. The layout is slice + `ssz-size`.
- We do not claim that this source is the same as the old fixed-array pin `5ac1d028f5` (pin branch `45394e5`). The old pin is superseded history (that commit is not available from `syjn99/prysm`).
- The 1c compiler is Go 1.26.10 (`/workspace/tooling/go1.26.10`). It is a new experimental baseline.
- The old 1c compiler value Go 1.26.3 is superseded only in 1c. fix3 continues to use the Go 1.26.3 ELF.
- We did not lower the Prysm `go` directive. We did not make a type-extraction workaround.
- The generator and runtime are `698c2025a73a296b55b95744a8408f3b03b2546b`. We did not change the generator.
- **The 55 theorems of the Go 1.26.3 machine code do not carry over to this ELF.** New machine code needs a new table and a new proof correspondence. A successful compile proves nothing.

## 2. Target

| Item | Value |
| --- | --- |
| Host | linux/arm64, `go version go1.26.10 linux/arm64`. No x86-64 hardware |
| Generation | host native (arm64). Generator binary sha256 `e962d9b6b863a20f958bbb10f42867fc278c67274ce174db29887fb49bdf87d4` (Go 1.26.10, `-trimpath`, built from the 698c202 tree) |
| Target | cross-compile `GOOS=linux GOARCH=amd64 GOAMD64=v1 CGO_ENABLED=0 go build -p 2 -tags purego -trimpath` |
| Package | `github.com/OffchainLabs/prysm/v7/fvphase1c/p1cbin` (scratch `main` of the temporary tree, copy `p1cbin-main.go.txt`) |
| ELF sha256 | `c6403c02a110ffd6fe6d31a3c89cd395ac457b5d62e60e2e611b8ab9a8dd911e` |
| ELF size | 23486009 bytes. It is larger than 5 MB, so it is not committed. Copy: run directory `streams/phase1c/artifacts/elf/p1cbin-amd64` |
| Go build ID | `vvezRAx2XfNAzHGIedKc/LVz05eLSmRibjKM02M9g/vTUc8QDCGkwQyqjmLKtu/siAyhYgBvYBhMpoLOoxx` |
| Reproducibility | The second build used an empty GOCACHE. The sha256 and the build ID are the same (`build-ids.txt`) |
| objdump / nm | sha256 `580b0da9…4a47` / `88ee8b9a…40ac` (`build-ids.txt`). Not committed (17 MB / 2 MB) |

## 3. Source pin

| Item | Value |
| --- | --- |
| Prysm tree | `/workspace/worktrees/prysm/fv-phase1c`, HEAD `ab15ff70…`, 0 commits |
| `replace` | `replace github.com/OffchainLabs/methodical-ssz => /workspace/worktrees/methodical-ssz/fv-pin-smoke-generator` (`prysm-go.mod.diff`) |
| Generator tree | `/workspace/worktrees/methodical-ssz/fv-pin-smoke-generator`, `698c202`, read-only, `git status --porcelain --ignored` 0 lines |
| Tree status | `prysm-tree-status.txt`: `go.mod`, 16 generated files, two files in scratch `fvphase1c/` |
| Generated files | `../_generated/` (sha256 `../_generated/SHA256SUMS`). These files overwrote the files with the same names in the temporary tree |
| Modules | Go proxy only (`GOPROXY=https://proxy.golang.org`, `GOTOOLCHAIN=local`) |

## 4. Rebuild

Use the environment files of the run directory `$S` (= `/workspace/agent-runs/methodical-fv-parallel/streams/phase1c`). All steps run inside the gate.

```sh
. $S/env-go12610.sh
# 1. Add one replace line to a clean ab15ff70 tree (prysm-go.mod.diff).
# 2. Generation and IR
sh fv/kraken/gen/prysm-gen.sh <prysm-tree> <ssz-698c202 binary> <out>
# 3. Put the generated files in the tree (<out>/gen/{mainnet,minimal}/* -> proto/prysm/v1alpha1, proto/engine/v1)
python3 -I fv/kraken/gen/inventory.py reduce <out>/ir-mainnet.json fv/kraken/prysm/ir/ir-mainnet.json   # the same for minimal
python3 -I fv/kraken/gen/inventory.py build fv/kraken/prysm
python3 -I fv/kraken/gen/keepalive.py fv/kraken/prysm/inventory.json <prysm-tree>/fvphase1c/p1cbin/main.go
sh fv/kraken/gen/prysm-elf.sh <prysm-tree> <elf-out> <empty GOCACHE directory>
python3 -I fv/kraken/gen/mnemonics.py <elf-out>/p1cbin-amd64.objdump fv/kraken/lean/.lake/packages/Kraken/Kraken/X64/Parser/Basic.lean fv/kraken/link/conv.py fv/kraken/prysm/inventory.json fv/kraken/prysm/go1.26.10/functions.json
python3 -I fv/kraken/link/conv.py <elf-out>/p1cbin-amd64.objdump <elf-out>/p1cbin-amd64.nm <norm-out> --norm
(. $S/env-lean.sh; cd fv/kraken/lean && KPARSE_LIST=<.S list> lake env lean ../gen/kparse/KParse.lean)
python3 -I fv/kraken/gen/kparse/summ.py <kparse log> fv/kraken/prysm/go1.26.10/functions.json fv/kraken/prysm/go1.26.10/kparse.json
python3 -I fv/kraken/gen/types_md.py fv/kraken/prysm
```

Run logs of this session: `$S/logs/01` (generator build), `02` (go list), `03` (generation), `04` (IR), `05` (ELF ×2, objdump), `06`·`07` (parser), `08` (`%riz` diagnosis).

## 5. Trust limits

- Nothing ran on x86-64 hardware. There is no comparison of Kraken with a real CPU.
- `layout` and the Go layout are the gc amd64 rules of `go/types` (`ir/*.json` `go_fields`). An amd64 run did not check them.
- There is no theorem about this ELF yet. The table is a classification.
- The runtime contracts are abstract models only. The contracts come from a reading of the Go 1.26.3 runtime source. Nobody read the Go 1.26.10 runtime again for them. In this namespace they are unchecked assumptions (`gen/frozen/ASSUMPTIONS.json` revision 2).
- This ELF has no link check (a)–(h). The instruction statistics and `.S` are the output of one disassembler (`go tool objdump -gnu`) and `link/conv.py`. No cross-check with an independent decoder was done.
- The hand-written primitives SSZ methods (5 types in `consensus-types/primitives`, 24 functions, called by 52 generated types) have no specification and no proof.
- `fvphase1c/invtool/main.go` in the temporary Prysm tree is a pre-gofmt copy of the committed `gen/invtool/main.go`. The difference is whitespace only (struct tag alignment). The IR came from this copy.
