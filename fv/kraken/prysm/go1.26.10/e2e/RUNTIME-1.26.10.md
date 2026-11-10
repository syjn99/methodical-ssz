# RUNTIME-1.26.10: Go runtime contracts re-read against Go 1.26.10 (prysm-e2e E1.4)

The table comes from `runtime-diff.json` (`gen/e2e/runtime_diff.py /workspace/tooling/fv/go1.26.3 /workspace/tooling/go1.26.10`).
The script compares the function bodies each contract rests on, and whole files for assembly and the ABI document.

## 1. Verdict per contract

| Contract or excluded path | Sources compared | Go 1.26.3 → 1.26.10 | Effect on the contract |
| --- | --- | --- | --- |
| `MakesliceC Heap ty 1 S` | `slice.go` `makeslice`, `malloc.go` `mallocgc` | unchanged | none |
| `GrowsliceC Heap ty 1 S` | `slice.go` `growslice`, `nextslicecap`; `malloc.go` `mallocgc`; `msize.go` `roundupsize` | unchanged | none |
| `MemmoveC S` | `memmove_amd64.s` | unchanged | none |
| `NewobjectC` (only on the excluded nil-result branch) | `malloc.go` `newobject`, `mallocgc` | unchanged | none |
| `ConvT64C` (Epoch reject) | `iface.go` `convT64`, `malloc.go` `mallocgc` | unchanged | none |
| `FmtErrorfWC`, `FmtErrorfDDC` | `fmt/errors.go`, `fmt/print.go`, `fmt/format.go`, `errors/errors.go` | unchanged | none |
| `writeBarrier = 0` premise | `mbarrier.go`, `mwbbuf.go`, `asm_amd64.s` | unchanged | none |
| stack-guard premise (`morestack` excluded) | `asm_amd64.s`, `stack.go` `newstack` | unchanged | none |
| Go ABIInternal amd64 | `cmd/compile/abi-internal.md`, `internal/abi/abi_amd64.go`, `internal/abi/type.go` | unchanged | none |

Changed functions in these files, and why no contract rests on them:

| Changed function | Change | Used by a contract here? |
| --- | --- | --- |
| `slice.go` `moveSliceNoCap` | allocates `(capmem / et.Size_) * et.Size_` and returns `cap = capmem / et.Size_` | No. It is not `growslice`. No function of this set calls it (CALLGRAPH.md). |
| `iface.go` `itabInit` | `//go:nowritebarrier`, code pointers stored as `uintptr` | No. `convT64` is unchanged. The itab `go_itab._errors.errorString_error` is static data in the ELF. |
| `stack.go` `adjustframe` | arm64 injected-call frame pointer adjustment; on amd64 the dead-frame return (`continpc == 0`) moves after the saved frame pointer adjustment (review e2e-r1 S5) | No. It is on the `morestack` path, which the stack-guard premise excludes. |
| `mgcmark.go`, `traceback.go` (other runtime files) | GC stack scanning of injected frames | No. GC during a call is outside every contract (CONTRACTS.md §3 trust table). |

Correction to PROOF-PLAN.md §1: the plan says that `growslice` changed.
The change is in `moveSliceNoCap`; `growslice` and `nextslicecap` are byte-identical in the two versions.

## 2. Instances used in this namespace

| Contract | Instance | New form? | Model (abstract, Kraken) |
| --- | --- | --- | --- |
| `MakesliceC` | `ty = E2e.Data.e2eU8Type_addr` (`type__+387072`, uint8, Size_ 1), esz 1, cnt 32 | no | `bump_makeslice1` |
| `MemmoveC` | n = 32 (decoder and encoder) | no | `rt_memmove` |
| `GrowsliceC` | `ty = e2eU8Type_addr`, esz 1 (encoder, capacity too small) | no | `rt_growslice` |
| `ConvT64C` | Epoch reject, v = len(buf) | no | `rt_convT64` |
| `FmtErrorfDDC` | `fs = E2e.Data.e2eEpFmt` (40 bytes), `tw = E2e.Data.e2eIntType_addr` (`type:int`, `type__+387520`) | no (same form, new format and type word) | `rt_errorf_dd` |
| `FmtErrorfWC` | `fs = E2e.Data.e2eCpFmtW` ("Epoch: %w") | no | `rt_errorf_w` (only the unreachable Checkpoint path; no theorem uses it) |

`StaticBox` (the existing form in `Fk/Contracts.lean`, used by `ep_unmarshal_reject_len_main` and its witness `WitEpR`) reads the table `Fk.Data.staticuint64s` at `Fk.Data.staticuint64s_addr`, which are names in the Fk.Data (Go 1.26.3) namespace. Two kernel-checked lemmas tie them to the Go 1.26.10 include: `E2e.ep_static_table` (`e2eStaticuint64s = Fk.Data.staticuint64s`, the 2048 bytes; link check (f) compares `e2eStaticuint64s.data` with the Go 1.26.10 ELF) and `E2e.ep_static_addr` (`e2eStaticuint64s_addr = Fk.Data.staticuint64s_addr`; both are `(label "runtime.staticuint64s").toBitVec`). No Go 1.26.3 fact is used: the bytes and the address are those of the new ELF (review e2e-r2 N3).

## 3. What this does not show

No Go 1.26.3 refinement proof exists (CONTRACTS.md §3: the Go machine code of the runtime is not proved to satisfy any contract), and none is transferred.
The re-reading compares source text only. It shows that the reasons written in CONTRACTS.md for each contract hold for Go 1.26.10 as much as for Go 1.26.3.
Every contract stays a conditional assumption of the theorems (trusted), with the same trust items as CONTRACTS.md §3.
The compiled runtime machine code in the ELF is not compared with the source.
