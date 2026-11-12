# REPORT: list/vector hand proofs

**Verdict: conditional.**

Conditions:

1. Runtime calls are contract hypotheses (`MakesliceC`, `MemmoveC`. IndexedAttestation also uses `NewobjectC`, `ConvT64C`, `FmtErrorfDWC`). There is no refinement proof of the Go runtime machine code.
2. The premises `writeBarrier = 0` and `guard < rsp` fix the path. The write-barrier path and the morestack path are not proved.
3. Review r4 approved the `IndexedAttestation` decoder and the `conv.py` fix (`93b3f2a`). The changes after it did not get a review.
4. The IndexedAttestation alignment reject and overflow reject are not proved with the frozen statements. No counterexample model was made. Only the `_nz` statements, which add the premise `e0 ≠ 0`, are K.
5. The Go differential test and the x86-64 execution comparison were not run.
6. Section 9 gives the independent review results.

## 1. Environment and pins

| Item | Value |
| --- | --- |
| Repository remote | `syjn99/methodical-ssz` is the remote name `my` in this worktree. `origin` is `OffchainLabs/methodical-ssz`. Nothing was written to a remote |
| Base commit | `6a78c591e8bcd698b7b9313b1c09cb25f3986911` (remote head of `syjn99/ssz-fv-reuse-milestone`) |
| Branch | `claude/ssz-fv-list-vector-20261112` |
| ELF sha256 | `c6403c02a110ffd6fe6d31a3c89cd395ac457b5d62e60e2e611b8ab9a8dd911e` |
| ELF rebuild | linux/arm64 container, Go 1.26.10 (official tarball sha256 `3f4227ce…9797`), Prysm `ab15ff70`, generator `698c202`, no `.git`. The sha256, build ID, objdump sha256 and nm sha256 are the same as in `build-ids.txt` |
| Kraken | `6064eecbb730a1152aa6ed891a155d3a92a4f298` |
| EthLib | `862185680cf23ccf54d44eb25b63b26c5020597b` |
| Lean | `4.36.0-nightly-2026-09-21`, Lake 5.0.0. Same as `lean-toolchain` |
| Host | darwin/arm64, 18 cores, RAM 48 GiB, Apple LLVM 21.0.0 (`xcrun`) |
| `.lake` | Not present at the start. First build `lake build E2e E2eAd E2eScal`: exit 0, 982 jobs, 1215 s, sampled RSS max 19.2 GiB (upper-bound estimate) |
| Heavy jobs | `heavy.py` outside the repository (a tool of the earlier ARM task), cap 40960 MB. `gen/tools/memcap.py` needs `/proc`, so it does not run on macOS |
| Models | Planning and selection `claude-fable-5-2`, proofs `claude-opus-5-5` |
| Deadline | Assumed to follow the campaign deadline (new proofs 2026-11-13T12:00Z). The user did not confirm it |

`SELECTION.md` gives the selection table and the reasons.

## 2. Coverage (K kernel-checked, X executed only, N not proved)

| Type | Path | Kind | Theorem |
| --- | --- | --- | --- |
| SyncAggregate | size reject | K | `sa_e2e_reject_size_main` |
| SyncAggregate | accept | K | `sa_e2e_accept_main` |
| SyncAggregate | accept, specification | K | `sa_e2e_accept_spec_k` |
| SyncAggregate | size reject, specification | K | `sa_e2e_reject_size_spec` |
| SyncAggregate | reject completeness | K | `sa_e2e_reject_complete` |
| SyncAggregate | hand `Desc` = producer `Desc` | K | `prysmSaDesc_deserialize_checker` |
| SyncAggregate | witness | K | `WitSaA.sa_accept_runs` |
| SyncCommittee | size reject | K | `sc_e2e_reject_size_main` |
| SyncCommittee | one iteration (bounds check does not branch) | K | `sc_iter` |
| SyncCommittee | 512-iteration loop | K | `sc_loop`, `sc_exit` |
| SyncCommittee | accept | K | `sc_e2e_accept_main` |
| SyncCommittee | accept, specification | K | `sc_e2e_accept_spec_k` |
| SyncCommittee | size reject, specification | K | `sc_e2e_reject_size_spec` |
| SyncCommittee | reject completeness | K | `sc_e2e_reject_complete` |
| SyncCommittee | hand `Desc` = producer `Desc` | K | `prysmScDesc_deserialize_checker` |
| SyncCommittee | witness | K | `WitScA.sc_accept_runs`, `bump_makeslice_t24`, `bump_makeslice_t1` |
| SyncAggregate, SyncCommittee | link check | X | `lv/link/RESULT` |
| SyncAggregate, SyncCommittee | negative test | X | `lv/negative-lv.json` |
| IndexedAttestation | size reject | K | `ia_e2e_reject_size_main`, `ia_e2e_reject_size_spec` |
| IndexedAttestation | offset reject | K | `ia_e2e_reject_offset_main`, `ia_e2e_reject_offset_spec` |
| IndexedAttestation | accept, all n ≤ 2048 | K | `ia_iter`, `ia_exit`, `ia_loop`, `ia_e2e_accept_main` |
| IndexedAttestation | accept, specification | K | `ia_e2e_accept_spec` |
| IndexedAttestation | alignment reject, frozen statement | N | `ia_reject_misaligned_stmt` and its specification pair. Not proved. There is no counterexample model |
| IndexedAttestation | alignment reject, `e0 ≠ 0` | K | `ia_e2e_reject_misaligned_nz`, `ia_e2e_reject_misaligned_spec_nz` |
| IndexedAttestation | overflow reject, frozen statement | N | `ia_reject_toobig_stmt` and its specification pair. Same reason |
| IndexedAttestation | overflow reject, `e0 ≠ 0` | K | `ia_e2e_reject_toobig_nz`, `ia_e2e_reject_toobig_spec_nz` |
| IndexedAttestation | delegate error | N | Recorded as an unreachable path. There is no separate theorem |
| IndexedAttestation | EthLib reject cases | K | `ia_e2e_reject_cases` (not a machine theorem) |
| IndexedAttestation | hand `Desc` = producer `Desc` | K | `prysmIaDesc_deserialize_checker` |
| IndexedAttestation | witness | K | `WitIaA.ia_accept_runs` (all n ≤ 2048, examples 0, 1, 2048), `WitIaR.ia_misaligned_runs`, `WitIaR.ia_toobig_runs`, `WitIaR2.ia_size_runs`, `WitIaR2.ia_offset_runs` (after review r4, `d3f4856`) |
| IndexedAttestation | link check | X | `lv/link-t3/RESULT` |
| IndexedAttestation | negative test | X | `lv/negative-lv-t3.json` |
| SyncAggregate, SyncCommittee, IndexedAttestation | MarshalSSZTo, SizeSSZ, HashTreeRoot | N | out of scope |
| SyncAggregate, SyncCommittee | morestack, write barrier | N | the premises block them |

The SyncAggregate and SyncCommittee main theorems have the frozen statement defs of `dfc8b93` as their types.
The IndexedAttestation main theorems have the frozen statement defs of `e13053a` (`StmtIa.lean`) and `714989f` (`StmtIaNz.lean`) as their types.
For the error value, the IndexedAttestation alignment reject and overflow reject state only `rax ≠ 0`.
Review r4 (`9e2272b`) checked the IndexedAttestation rows.
The IndexedAttestation size reject and offset reject witnesses were added after review r4 (S1). They use their own Host. The Host of `WitIaR` has no `ssz.ErrSize` label.
Review r5 approved the changes after review r4 (`d3f4856`, `e0bbac7`, `c478e87`) (`REVIEW-R5.md`).
The axioms are in the gate results `lv/axioms-gate-lv.json` and `lv/axioms-gate-lv-t3-r4.json`.

## 3. Blocked obligations

| Obligation | Cause class | Fact |
| --- | --- | --- |
| IndexedAttestation alignment reject and overflow reject, frozen statements | statement defect | If the errorString itab label `e0` is 0, `test %rcx,%rcx; je` skips the type-word read. The statement has no `e0 ≠ 0`. In that case `je` cannot be refuted, and the proof method fails. The planner missed this at approval. The user approved the `_nz` statements |
| IndexedAttestation witness, strategies 1 and 2 | proof size | A verbatim copy of the WitScA text times out in `whnf` at 64000000 heartbeats (log 192, 1471 s). Strategy 3 (a rewrite that removes `ib` first) closed it |

The `conv.py` fix resolved finding LV-1, the wrapped negative displacement (`FINDINGS-CANDIDATES.md`).

No obligation in SyncAggregate and SyncCommittee reached the attempt limit (`ATTEMPTS.md`).
Compile iterations in one proof strategy counted as one attempt. This is the interpretation of the implementer.

## 4. Time and memory

Method: `heavy.py` records, one run (n = 1), sampled RSS is the group sum (upper-bound estimate).

| Module | Module time | Wall clock | RSS |
| --- | --- | --- | --- |
| SaReject | 4.3 s | 6.3 s | 1.93 GiB |
| Seg | 3.6 s | 6.3 s | 2.17 GiB |
| SaAccept | 4.7 s | 7.3 s | 2.15 GiB |
| SaSpec / SaSpecK / SaDescEq | 3.2 s each | 5.2–8.3 s | 0.86 GiB or less |
| WitSaA | 12 s | 17.7 s | 2.04 GiB |
| ScReject | 3.8 s | 6.3 s | 1.98 GiB |
| ScLemmas | 3.4 s | 5.2 s | 0.86 GiB |
| ScLoop | 6.3 s | 8.3 s | 2.22 GiB |
| ScAccept | 6.6 s | 9.4 s | 2.12 GiB |
| ScSpec / ScSpecK / ScDescEq | 3.2–3.5 s | 5.2–8.4 s | 1.93 GiB or less |
| BumpT | 1.7 s | 4.2 s | 1.97 GiB |
| WitScA | 16 s | 18.8 s | 2.06 GiB |

`maxHeartbeats` is only on the two witnesses: `WitSaA.sa_accept_runs` 2000000, `WitScA.sc_accept_runs` 4000000.
Cause: `simp` AC sorting (log 27, 7.03 s + 2.08 s).
Without the setting, `whnf` times out (logs 26, 65).
Measurement of reviewer r2: 400000 fails for both. WitSaA passes at 1000000. WitScA fails at 1000000 and passes at 2000000.
`E2eList` has no `maxRecDepth` setting (review r2 M1, `69f1a70`).
The two `example`s in `WitScA.lean` use term proofs (`List.length_replicate`, `List.eq_of_mem_replicate`) instead of `by simp`.
The WitSaA and WitScA values in the table above are the values after that fix (logs 96, 97).
The logs are only local. `ATTEMPTS.md` has excerpts.

IndexedAttestation options (the cause and the threshold are next to each option. These are measurements of the implementer):

- `maxRecDepth 1024`: `ia_e2e_reject_size_main`, `ia_e2e_reject_offset_main` (logs 123, 124), `ia_iter`, `ia_exit`, `ia_e2e_accept_main`, the two `_nz` proofs. Without it, the first `kat` stops (logs 136, 139, 184, 233).
- `maxHeartbeats 1600000`: `ia_e2e_accept_main`. 400000 fails and 800000 passes (log 185).
- `WitIaA`: `maxRecDepth` per declaration (review r4 S3, `e0bbac7`). `hk288` has 1024, `P_len` and `hk531`…`hk869` have 2048 (1024 fails, logs 261, 262). `ia_accept_runs` has `maxHeartbeats 10000000` (4000000 fails and 5000000 passes, log 211).
- `WitIaR`: `maxRecDepth 1024` only on `P_len` and `hk284` (without it, only those two fail, log 260). `WitIaR2`: 1024 only on `P_len` (log 259).
- `lake build E2eList`: 765 jobs, 100 s, sampled RSS 7.71 GiB (log 252).

## 5. Reuse and new items

Reuse: `dechead_seg`, `decepi_seg`, `bytesdec_tail_seg`, `bytesdec_seg` (48), `bump_makeslice1`, `rt_memmove`, `Fv1.deserialize_enc`, `accepted_is_enc`, EthLib `packBits_unpackBits`, `unpackBits_packBits`, `headOf_inline`, `bodiesOf_inline`, `concatParts_size`, `concat_fixed_slices`.

New Lean (lines): Code 22, Include 85, Data 23, Desc 31, Defs 59, StmtSa 207, StmtSc 229, SaReject 94, ScReject 94, Seg 370, SaAccept 181, ScLemmas 122, ScLoop 313, ScAccept 270, SaSpec 96, ScSpec 173, SaSpecK 41, ScSpecK 46, Sa/ScSpecChecker 13 each, Sa/ScDescEq 54 each, BumpT 148 (+ `.S` 16), WitSaA 126, WitScA 136 (at `69f1a70`).

New scripts: `lvlink.py`, `lvcheck_include.py`, `lvdescterm.py`, `lvaxioms_gate.py`, `AxiomsLv.lean`, `lvnegative.py`.
The existing scripts did not change.

## 6. Added trust items

- `MakesliceC … lvSliceType_addr 24 S` is used as an instance of the existing form (planner verdict). The contract does not read the type descriptor.
- This element type has pointers. Thus "no GC during the call" is more important here.
- A trusted reader `lv_data_include` was added. Its text is the same as `E2e/Include.lean` (4 SAME).
- `BumpAllocT` is a non-vacuity model. It compares the type word and removes 24·cnt or cnt. Go `makeslice` reads `et.Size_`.
- After review r1, `BumpAllocT.S` was registered as a Lake `input_dir` (`lv_lean_S`).
- The equality of the hand `Desc` and consensus-specs is a judgment. The equality with the producer `Desc` is K.
- The author's base-side drift dump used a copied `.lake`. Reviewer r2 built the base tree separately. That dump is byte-for-byte the same as the author's dump.

- IndexedAttestation: `ia_accept_stmt` uses `len ≤ cap` and `cap < 2^63` as premises. Without `cap < 2^63`, the conclusion is false (`DESIGN-T3.md`).
- IndexedAttestation: The machine-side reject completeness holds for the alignment reject and the overflow reject only under `e0 ≠ 0`. The witness uses `e0 = 0x1012b`.
- IndexedAttestation: Witness-only runtime models `BumpAllocT3` (makeslice, esz 8 or 1) and `BumpNewT3` (newobject, 96 or 72) were added.
- IndexedAttestation: Two Lake `input_dir`s (`lv_t3_norm_S`, `lv_t3_data`) were appended to the lakefile (`e13053a`).
- `link/conv.py` changed (`93b3f2a`, user approval). `check.py` does not put the hash of `conv.py` in the RESULT bundle.

## 7. Verification

`STEPS.tsv` has the commands, exit codes and logs.

| Check | Result |
| --- | --- |
| `lake build E2eList` | exit 0 (683 jobs after the review r2 fixes, log 98) |
| `--no-build E2e E2eAd E2eScal E2eList` | exit 0, 1036 jobs (log 99) |
| axioms gate | PASS, 5632 declarations, nonstandard 0, sorryAx 0 (`axioms-gate-lv.json`, after review r1 `axioms-gate-lv-r1.json`. After the review r2 fixes `axioms-gate-lv-r2.json`, log 100) |
| gate control (planted `sorry`) | FAIL (as expected) (`axioms-gate-lv-plant.json`) |
| declaration drift (base `6a78c591`, roots E2e/E2eAd/E2eScal) | 0 (`decl-drift-lv.txt`. 0 again after the review r2 fixes, log 102) |
| drift control | CHANGED (as expected), reverted |
| link SyncAggregate, SyncCommittee | PASS all |
| negative test | 25 of 26 passed (control_pass 7, inside 18). `lv-sa-bitslen63` is outside (the error is in `sa_bits_seg`). The case that aims the same mutation at `sa_bits_seg` is inside. This includes the `Desc` mutations and the SyncCommittee size reject mutations (log 94). The `Desc` mutation files are cut from the target. They go only up to `prysmS*Desc_fixedSize` or `ps*_toValue_fits`. No `Desc` mutation tests `*_spec_k`. The author did not run it again after the review r2 fixes. Reviewer r3 ran it again, and the per-case results are the same |
| stale check | flagged 0 |
| IndexedAttestation `lake build E2eList` | exit 0, 765 jobs (log 252) |
| IndexedAttestation `--no-build` four libraries | exit 0, 1080 jobs (log 254) |
| IndexedAttestation axioms gate | PASS, 6402 declarations, theorems 5341, nonstandard 0, sorryAx 0 (`axioms-gate-lv-t3.json`, log 255) |
| IndexedAttestation declaration drift | 0, 5007 = 5007 (`decl-drift-lv-t3.txt`, log 250) |
| IndexedAttestation link | PASS all (`lv/link-t3/RESULT`). Not run again in the IndexedAttestation verification unit |
| IndexedAttestation negative test | all 8 passed: control 2, inside 6 (`negative-lv-t3.json`, log 253) |
| IndexedAttestation, after the review r4 fixes | build exit 0 (log 265), `--no-build` exit 0, 1082 jobs (log 266), gate PASS 6451 declarations (`axioms-gate-lv-t3-r4.json`, log 267), drift 0 (log 268), negative test all 14 passed: control 5, inside 9 (log 264). After review r5, all 16 passed: control 5, inside 11 (`64974ac`, log 270, before review) |
| IndexedAttestation gate control, drift control, stale check | not run |
| Go differential test | not run |
| hardware comparison | not run. The host is arm64 |

## 8. Lessons for full codec verification

- For each fixed byte field with a new size, the proof text of the segment lemma was copied one more time (`Seg.lean` 370 lines). The `hn` of `SegN` is a limit of the proof method.
- The 512-iteration loop closed with a one-iteration theorem and induction. The `ScLoop` build is 6.3 s. The loop was not unrolled.
- Invariant form: array = first i headers ++ 0, element = pair of a pointer and an input slice, heap = avail − 48·i, receiver len slot.
- The bounds check reads len from the receiver in each iteration. Thus the invariant had to have that slot to block `panicBounds`.
- The Vector[Bytes48, 512] specification closed with general list lemmas and EthLib theorems. `decide` does not close it.
- A call to the same runtime function with a different esz needed a model that branches on the type in one Host witness.
- Tool gaps: `Width.bits` of `kaddr` (existing finding T-4), `ecancel` failure from a proof-term difference in `pks[i]` (avoided with `generalize`), LV-1.
- The statement def form did not match `negative.py`. A runner that unfolds the statement module was necessary.
- Automation candidates: head, tail and field segments, the step sequence of a one-iteration proof. These come from the two types of this task. Other types were not tested.
- Items that needed a hand: the memory form of the invariant and slice split and join (`scA_split`, `scA_join`, `scIn_split`).
- IndexedAttestation: Two kernel traps occurred. With `simp [BitVec.toNat_add]; omega` on `c + -228`, the kernel stops with "deep recursion" after 235–309 s (16–20 GiB). `decide` on 64-bit `sshiftRight` is the same. Explicit lemmas avoided them.
- IndexedAttestation: The memory goal of the witness did not close with `ecancel` (56 internal PANICs, logs 204–208). AC `simp` closed it.
- IndexedAttestation: A frozen statement must have, as a premise, the zero status of each label that a branch reads. The alignment reject and the overflow reject are examples.
- Correction: the statement "the `Deposit_Data` decoder specification is not in the repo" in `SELECTION.md` is wrong. `dd_e2e_accept_spec_k` exists. `SELECTION.md` is a frozen file, so the correction is here.
- Next candidate: `HistoricalBatch` has the same form. Whether this proof transfers was not tested. A function with a negative displacement must resolve LV-1 first.

## 9. Finding candidates and reviews

- LV-1 (fixed `93b3f2a`, review r4 approval, X, tool gap). The SIB form without a base and the segment form are not handled (0 in this objdump, review r4 S9). See `FINDINGS-CANDIDATES.md`.
- There is no new production defect candidate.
- Independent review r1 (`fbf729a`): REQUEST_CHANGES, 1 required fix (M1). M1: a `maxRecDepth` setting without a recorded cause. See `REVIEW-R1.md`. The fixes are `463ec97`, `3bb6cc1`, `4a18079`, `ec75cd5`.
- Independent review r2 (`d169e4b`): REQUEST_CHANGES, 2 required fixes (M1, M2). M1: a `maxRecDepth` value wider than necessary. M2: a wrong statement about the objdump functions in `FINDINGS-CANDIDATES.md`. See `REVIEW-R2.md`. The fixes are `1ba8b41`, `69f1a70`, `252380f` and the commit of this file.
- Independent review r3 (`650b1f5`): APPROVE, no required fix. See `REVIEW-R3.md`. The documentation commits after it did not get a review. These commits are the records for review r3 items N1 (two values of section 4) and N2 (`negative-lv.json`), and `REVIEW-R3.md`.
- Independent review r4 (`9e2272b`, scope: the `conv.py` fix and IndexedAttestation): APPROVE, no required fix, 9 suggested fixes. See `REVIEW-R4.md`.
- Independent review r5 (`4d42634`, scope: the r4 suggested fixes): APPROVE. The same review gave REQUEST_CHANGES for the branch `syjn99/ssz-fv-hb` (`a1c5191`). See `REVIEW-R5.md`.
- Items that need user confirmation:
  - The esz 24 `MakesliceC` instance (review r1 S7).
  - The deadline.
  - The Go differential test.
  - The lakefile change of `3bb6cc1` (`input_dir` addition). The root `AGENTS.md` requires approval for a lakefile change.
  - The remaining path for LV-1 (`check.py` range check, Kraken request). The user approved the `conv.py` fix.
  - The lakefile change of `e13053a` (two `input_dir` additions).
  - The interpretation of the attempt count (section 3).
  - The remote name. `origin` is OffchainLabs.
