# FINDINGS: cumulative ledger (generator, generated code, proofs and tools)

Stable IDs. Old items keep their IDs and discovery dates; their full text stays in `GENERATOR-FINDINGS.md` (unchanged).
Each entry: discovery checkpoint, affected pin / type / function, repro and evidence, consequence, status, independent review.

## 1. Generator defects (sszgen `698c202`)

| ID | Found | Affected | Repro / evidence | Consequence | Status | Review |
| --- | --- | --- | --- | --- | --- | --- |
| D1 | 2026-11-09, `846982c` (phase1c) | generator IR: nested container field keys | `GENERATOR-FINDINGS.md` §1 | IR key is the container name, not the field name | open (generator not changed, rule) | phase1c reviews r1–r8 |

## 2. Generated SSZ code defects

None confirmed. Candidate C-1 is in §5.

## 3. Proof, checker and tooling defects

| ID | Found | Affected | Repro / evidence | Consequence | Status | Review |
| --- | --- | --- | --- | --- | --- | --- |
| K1 | 2026-11-09 (phase1c) | Kraken runtime parser: `%riz` index | `GENERATOR-FINDINGS.md` §4 | 13 generated functions did not parse | normalised by `link/conv.py --norm` (`f17f9c8`) | phase1c r8 |
| K2 | 2026-11-09 (phase1c) | Kraken parser: `bsr` | `GENERATOR-FINDINGS.md` §4 | `ssz.ValidateBitlist` not included | open (Kraken request) | phase1c r8 |
| T-1 | 2026-11-10, run fve2e, before `fd8a561` | Lean closing tactics on register goals with symbolic BitVec (`trivial`/`rfl` inside `first`) | prysm-e2e jobs 27, 28, 33, 34 (memcap kill at 6 GiB per process, oom_kill 5 → 5); probes 34, 35, 37 isolate the final register goals | one Lean process above 6 GiB; build killed | fixed: decoder proof split at `L_b4` (`cp_e2e_accept_tail`), closing by `exact trivial` / `with_reducible rfl` / `toBitVec_inj` + `eaddr` | pending (Fable review of this run) |
| T-2 | 2026-11-10, run fve2e, before `fd8a561` | `ecancel` final AC step | job 44: all 26 chunks match textually but `ecancel` fails; job 43 shows two atoms sorted differently (same print, different elaboration) | composition of `cp_e2e_accept_main` with its tail failed | worked around: `rw [show a = a from rfl] at Hm2` re-elaborates the two atoms (log 45) | pending |
| T-3 | 2026-11-10, run fve2e, `61eec5e` | `Fk/Include.lean` keeps the data reader private to its module | `lean/E2e/Include.lean` | a second data directory needs a copy of the reader | copy with a textual check (`gen/e2e/check_include.py`: SAME ×4) | pending |
| T-4 | 2026-11-10, run fve2e, before `fd8a561` | `kaddr` (Fk.Step) does not reduce `Width.W64.bits` | job 21 (omega atoms `2 ^ Width.W64.bits`) | address goals after a callee return fail | local macro `eaddr` (E2e.CpAccept) with `Width.bits` | pending |
| R-1 | review e2e-r1 at `9bad532` (M1) | `E2e.cp_e2e_unmarshal_then_marshal`, REPORT §11 E5 row | the theorem starts at the encoder entry, runs no decoder code and does not use `cp_e2e_accept_main`; no single witness host | E5 (compose_hupd, compose_witness) was reported as done | fixed: renamed `cp_e2e_marshal_decoded_receiver` (`fcb4f7e`); the real composition `E2e.cp_e2e_unmarshal_then_marshal` (`E2e/CpCompose.lean`, decoder entry → `cp_e2e_accept_main` → hupd → `cp_e2e_marshal_main`) with the one-Host witness `E2e.WitCpC.cp_compose_runs` and 11 negatives (`cpx-*`, logs 104–110) | found by review; fix pending re-review |

## 4. Known issues (not defects)

| ID | Found | Affected | Evidence | Note | Status |
| --- | --- | --- | --- | --- | --- |
| O1 | 2026-11-09 (phase1c) | generator log | `GENERATOR-FINDINGS.md` §1 observations | empty package name in a log line | unchanged |
| O2 | 2026-11-09 (phase1c) | Prysm hand-written `primitives` SSZ methods | `GENERATOR-FINDINGS.md` §1 observations | not generated; need their own proofs | `(*Epoch).UnmarshalSSZ` accept path proved as function spec `EpUAccC` (`37fdcf9`), length reject proved (`e5b68c9`); the other 23 methods not |
| N-1 | 2026-11-10, run fve2e, `e10b146` | `Checkpoint.UnmarshalSSZ` → `fmt.Errorf("Epoch: %w")` | `cp_e2e_epoch_err_unreachable` | unreachable with `len = 40` (unreachable_mc column, not reject coverage) | proved |
| N-2 | 2026-11-10, run fve2e, `61eec5e` | `Checkpoint.MarshalSSZTo` → `fmt.Errorf("Epoch: %w")` | `CALLGRAPH.md`, `-m=2` log | removed by the compiler (inlined `Epoch.MarshalSSZTo` cannot fail) | recorded |
| G-2 | 2026-11-09 (pin smoke, before phase1c) | Prysm `consensus-types/blocks` error-text tests (`TestMarshalPartsMetadata/available_too_large`, `/requests_too_large`, `TestPartialDataColumn_PartsMetadata/marshal_error_due_max_bitlist_size`) | `GENERATOR-FINDINGS.md` §2 | generator change `280b752` checks the Bitlist by bits (`ssz.ValidateBitlist(x, 4096)`); too large input still rejected, only the error text differs from the test | reference row (review e2e-r1 S9); compatibility issue, not a generator defect; unchanged |
| G-3 | 2026-11-09 (pin smoke, before phase1c) | `-tags minimal`: `consensus-types/blocks` test build, `encoding/ssz/detect` `TestByState` | `GENERATOR-FINDINGS.md` §3 | fails on the committed baseline too; unrelated to generated code | reference row (review e2e-r1 S9); baseline failure; unchanged |

## 5. Unconfirmed candidates

| ID | Found | Affected | Repro / evidence | Consequence | Status | Review |
| --- | --- | --- | --- | --- | --- | --- |
| C-1 | 2026-11-10, run fve2e (orchestrator observation, PROOF-PLAN §1; confirmed in the code `5a3ca92`) | `(*v1alpha1.Checkpoint).MarshalSSZTo`, Go 1.26.10 ELF | `.S` directive 35 stores the 8 epoch bytes at `dst[len:len+8]` before directives 37–38 test `len(Root) = 32`; Go source order (`phase0.ssz.go:1963` before `1967`); differential cases `enc-rootlen0/31/33` return `(nil, ssz.ErrBytesLength)` | on the error return the caller's backing array beyond `len(dst)` holds 8 new bytes (when `cap ≥ len + 8`); `dst` itself is not returned; no SSZ rule covers an invalid Go value | confirmed as machine behaviour and stated exactly by `cp_e2e_marshal_reject_main` (after `9bad532`): with `cap ≥ len + 8`, `dst[len:len+8]` = epoch bytes, rest of `dst` unchanged, result `(nil, ErrBytesLength)`; statement mutant "dst unchanged" fails (negative `cpmr-stmt-dst-unchanged`). Classified: known behaviour, not a spec violation (SSZ has no rule for a Go value with `len(Root) ≠ 32`); not a generator defect | pending |

## 6. False positives

| ID | Found | Claim | Resolution |
| --- | --- | --- | --- |
| FP-1 | 2026-11-10, run fve2e (PROOF-PLAN §1) | Go 1.26.10 changed `growslice` | the `slice.go` hunk is in `moveSliceNoCap`; `growslice`, `nextslicecap` are byte-identical (`go1.26.10/e2e/runtime-diff.json`); orchestrator erratum (INBOX 002) |

## Checkpoint deltas

(T-5 is recorded in the delta below; status: worked around; review pending.)

- 2026-11-10 `02b0e89` (prysm-e2e E6): new T-1, T-2, T-3, T-4, N-1, N-2, C-1, FP-1; O2 updated (Epoch decoder accept proved). No new generator defect.
- 2026-11-10 `507da34`+ (INBOX 004): C-1 confirmed and stated by `cp_e2e_marshal_reject_main` (classified known behaviour); O2 updated (Epoch reject proved). New tooling note T-5: `ecancel` bounded unfolding times out on `uintBytes` of a symbolic epoch (job 84/85); worked around by `generalize` (job 86). No new generator or generated-code defect.
- 2026-11-10 session 2 (M1 fix): R-1 fixed by the real machine composition and its witness (pending re-review). No new generator or generated-code defect.
