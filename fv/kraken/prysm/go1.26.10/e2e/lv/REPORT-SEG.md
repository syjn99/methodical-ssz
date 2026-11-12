# REPORT-SEG: segment lemma generalization and the Deposit port

**Verdict: conditional.**

Conditions:

1. No independent review was done. Each K below is a kernel-check result of the author's build.
2. The element loop has two code forms: the 32-byte form (`v32_*`) and the `3·2^k` form (`vtri_*`, w ∈ {24, 48, 96}). Other forms are not generalized (section 4).
3. The w = 24 and 96 instances of `vtri_*` are proved only for the template. This ELF has no real code of those sizes, so the equality of the template and real code is not checked.
4. Runtime calls are contract hypotheses. There is no new contract form and no new instance form. The new instance value is `NewobjectC … depDataType_addr 120`.

`CHECKS-HB.md` has the first work (part 1): declaration drift 0, negative tests 10/10, the cause of the HbLoop2 time.
Sections 3, 1, 2 and 7 include the second work (Deposit completion, SyncCommittee loop generalization, element size parameter).

## 1. Generalized items (K)

| File | Theorem | Variables | Premises |
| --- | --- | --- | --- |
| `E2eSeg/ListG.lean` | `flat_len`, `in_split`, `arr_split`, `arr_join` | element width w, count n | `w * n ≤ 2^64`, `24 * n ≤ 2^64` |
| `E2eSeg/SegG.lean` | `bytesdec_seg_g`, `bytesdec_seg_z_g`, `bytesdec_seg_nop_g` | fixed byte field size n | `n < 2^31` |
| `E2eSeg/V32.lean`, `V32Loop.lean` | `v32_iter`, `v32_exit`, `v32_loop` | count n, five stack slots, two receiver offsets, labels, source offset, four `nop` positions | `n < 2^31`, element 32 bytes |
| `E2eSeg/RejG.lean` | `rej_size_g` | frame size F, size sz, label, one `nop` | `F < 2^31`, `sz < 2^31` |
| `E2eSeg/VTri.lean`, `VTriLoop.lean` | `vtri_iter`, `vtri_exit`, `vtri_loop` | count n, five stack slots, two receiver offsets, labels, source offset, gaps, element size (k, w) | `n < 2^31`, `TriSize k w` (w = 3·2^k, k ∈ {3, 4, 5}) |
| `E2eSeg/SpecG.lean` | `vN_flatten_length`, `vN_serialize`, `vN_of_bytes` | n of `Vector[Bytes32, n]` | `32 * n < 2^32` |

- The `hn : n = 32 ∨ 48 ∨ 96` of SegN was a limit of the proof method. Three positions computed a literal size.
- Those three were changed to lemmas: the makeslice count, the memmove count (32-bit immediate), the stored len and cap words (64-bit immediate).
- The loop body is divided into six blocks and gaps. `Glue` states that a gap is empty or one `nop`. `GlueSrc` states that it is empty or `lea src(%rbx),%rbx`.
- The block templates are the Kraken terms of `lv/link-hb` directives 36–77. Only the operands that change were made parameters.
- `ListG`, `SegG`, `V32`, `V32Loop`, `RejG`, `SpecG` build without settings. SegN needed `maxHeartbeats` 16000000.
- `vtri_iter` of `VTriLoop` has `maxHeartbeats` 800000 (section 5.1 has the option list).

### 1.1 Fixed instances derived again (K)

| Hand lemma (not changed) | New name | Proof |
| --- | --- | --- |
| `E2eScal.bytesdec_seg`, `bytesdec_seg_z` (n ∈ {32, 48, 96}) | `bytesdec_seg_inst`, `bytesdec_seg_z_inst` | one line (`type_of%`) |
| `E2eList.bytesdec_seg_z64`, `bytes96dec_seg_nop` | `bytesdec_seg_z64_inst`, `bytes96dec_seg_nop_inst` | one line |
| `E2eScal.H4.bytes32dec_seg_nop` | `bytes32dec_seg_nop_inst` | one line |
| `E2eList.scIn_split`, `scA_split`, `scA_join` | `scIn_split'`, `scA_split'`, `scA_join'` | one line, and `rfl` checks that the statement is the same |
| `E2eHb.hbIn_split`, `hbA_split`, `hbA_join` | `hbIn_split'`, `hbA_split'`, `hbA_join'` | one line, `rfl` check |
| `E2eHb.hb_loop1` | `hb_loop1_g` | about 70 lines: block and gap fact reads, labels, one exit-label step |
| `E2eHb.hb_loop2` | `hb_loop2_g` | about 65 lines |
| frozen statement `sc_reject_size_stmt` (SyncCommittee) | `sc_reject_size_g` | one application of `rej_size_g` |
| `E2eList.sc_loop` (SyncCommittee) | `sc_loop_g` | application of `vtri_loop` (k = 4, w = 48), about 80 lines, passed on the first build |
| `E2eHb.v32_serialize`, `v32_flatten_length`, `v32_of_bytes` | three `example`s | one line (`SpecG`) |
| frozen statement `hb_reject_size_stmt` | `hb_reject_size_g` | one application of `rej_size_g` |

- Why a loop instance is not one line: the positions of six blocks and five gaps must be read from the real program.
- `infix_sub` and `simp` close those facts. The line count does not increase with the directive count.
- The `hb_loop2_g` module is 6.2 s. The hand `HbLoop2` was 22.8 s (the constant 262144 problem of `CHECKS-HB.md` section 3 is not present).

## 2. Generated items (b) and element size

No generator was made. Generalization and literal families closed all the remaining repetition.

The 48-byte loop of SyncCommittee: one statement does not cover the two instruction sequences.
The 32-byte form has an overflow check (`jb`) and four local slots. The `3·2^k` form has no overflow check, stores `3i` and then does `shl $k`.
The blocks have different lengths and registers, so one template cannot cover them. Thus a second general loop (`vtri_*`) was written.
That loop derived `sc_loop` again (`sc_loop_g`, K).

The element size as a parameter: `kshl64` requires the two items below.

- The shift count must be a numeric literal. `decide` settles the `count == 0` branch.
- `decide` rewrites `(BitVec.extractLsb' 0 8 (k : BitVec 64)).toNat &&& 63 = k`.

Also, the size w goes into the steps as a number. The places: makeslice and memmove counts (`by rfl`), len and cap stored values (`decide`), source address `buf + w·i` (`omega`).
With variables k and w, nonlinear expressions of the form `i * 2^k` occur, and `omega` cannot close them. This was not tried (judgment).
Thus the `3·2^k` form uses one statement and one proof text (`vtri_iter_body`) with the literal family `TriSize` (w ∈ {24, 48, 96}).
The 32-byte form has only w = 32. All types of the same family in this ELF are 32 bytes.

## 3. Proof use: Deposit (c)

Selection: it is in the same family as `HistoricalBatch` (a `Vector[Bytes32, N]` field as `[][]byte`).
It is not a prohibited type, and it has no existing proof.
In the same family, only HistoricalBatch and SyncCommittee have no pointer field.
The pointer field of Deposit (Deposit_Data) already has a decoder proof (`E2eScal.H4.dd_e2e_accept_main`).

| Obligation | Kind | Theorem or file |
| --- | --- | --- |
| link (a)–(f) | X | `lv/link-dep/RESULT` PASS all, bundle `bd37b3f9…` (`gen/e2e/deplink.py`) |
| frozen statements | commit `57316a9` | `E2eDep/Stmt.lean`: `dep_reject_size_stmt`, `dep_accept_stmt` |
| size reject | K | `dep_e2e_reject_size_main`, one application of `rej_size_g`, passed on the first build |
| accept | K | `dep_e2e_accept_main`: the loop is `v32_loop` (n = 33), Deposit_Data is `dd_e2e_accept_main` |
| hand Desc, frozen specification statements | commit `bf2ebe7` | `E2eDep/SpecStmt.lean`: `prysmDepDesc` (written before the producer Desc output), `dep_accept_spec_stmt`, `dep_reject_size_spec_stmt`, `dep_reject_complete_stmt` |
| specification bridge | K | `dep_serialize`, `dep_roundtrip`, `dep_accepted_is_enc`, `dep_spec_accepts_iff` (`E2eDep/Spec.lean`) |
| specification pairs | K | `dep_e2e_accept_spec_k`, `dep_e2e_reject_size_spec`, `dep_e2e_reject_complete` |
| codec equality of the hand Desc and the producer Desc | K | `prysmDepDesc_deserialize_checker`: for all bs, v, `deserialize prysmDepDesc bs = .ok v ↔ deserialize depCheckerDesc bs = .ok v`. The two Descs differ only in field names (nested containers included). Producer file sha256 `cd4b71f0…` = checker record |
| witness | K | `WitR.dep_reject_runs` (lengths 1239, 1241, 0), `WitA.dep_accept_runs` (0, representative, 0xff). New witness model `BumpNew120` |
| negative test | X | `negcases-dep.json` 9/9: control 2, mutation 7 (statement and code size, loop bound, element size, Data offset and length, heap amount) |
| `depDataType_addr` check | X | `gen/e2e/depcheck_data.py`: SAME. The self-test (planted offset) differs as expected |

Settings of `WitA`: `maxRecDepth` 2000 (512 fails, 1000 passes), `maxHeartbeats` 4000000 (1000000 fails, 2000000 passes). The cause is `simp` sorting, 20.1 s (logs 115–122).
The loop and element size mutations fail at the block facts (`decide` of `infix_sub`). The loop proof is a general theorem, so it is not a mutation target.

The `maxHeartbeats` of the accept theorem is 800000. 200000 fails, 400000 and 800000 pass (logs 95–97).
Cause (log 98): the length of one declaration. Tactic execution 3.37 s, `simp` 1.11 s, kernel check 1.58 s.

### 3.1 Line counts (`gen/e2e/segreuse.py`, log 103)

| Deposit file | Source | verbatim | mechanical | new | comment |
| --- | --- | --- | --- | --- | --- |
| `E2eDep/Code.lean` | `E2eHb/Code.lean` | 2 | 2 | 4 | 11 |
| `E2eDep/Stmt.lean` | `E2eHb/StmtHb.lean` | 42 | 14 | 53 | 34 |
| `E2eDep/Reject.lean` | `E2eHb/HbReject.lean` | 2 | 4 | 16 | 2 |
| `E2eDep/Accept.lean` | `E2eHb/HbAccept.lean`, `E2eSeg/V32Hb.lean` | 141 | 86 | 154 | 25 |
| `gen/e2e/deplink.py` | `gen/e2e/hblink.py` | 54 | 4 | 9 | 18 |
| total | | 241 | 110 | 236 | 90 |

Scope: the table above compares the five Deposit files with the HistoricalBatch sources (rename HistoricalBatch → Deposit, `segreuse.py` part 1).
The 346 of `REPORT-HB.md` 3.2 has a different scope: it compares 16 HistoricalBatch files with the SyncCommittee sources (rename SyncCommittee → HistoricalBatch).
The counts with the same scope (the same file kinds) are below (`segreuse.py` part 3, log 151).

| Scope | HistoricalBatch new (reference SyncCommittee) | Deposit new (reference HistoricalBatch) |
| --- | --- | --- |
| code include | 1 | 4 |
| machine statement | 26 | 53 |
| size reject | 1 | 16 |
| loop 1 | 63 | 0 (general theorem, no file) |
| loop 2 | 67 | 0 (general theorem, no file) |
| accept | 34 | 154 |
| link script | 27 | 9 |
| total | 219 | 236 |

- The references and the rename tables are different. The two counts state only "lines not transferred from the previous type".
- The new loop lines became 0. HistoricalBatch had 130 lines for two loops. The loop use of Deposit (block facts and application, about 60 lines) is in the 154 accept lines.
- The size reject went from 1 HistoricalBatch line (a rename of an 80-line copy) to 16 Deposit lines (one application of a general theorem). The full reject proof went from 80 lines to 22 lines.
- The total of new lines in the same scope did not decrease (219 → 236). The increases are in accept (delegate call, about 120 lines) and statements (callee fields). HistoricalBatch did not have either item.

### 3.2 Lines that HistoricalBatch can remove

With the general theorems, the code lines of the hand files below are not necessary (`segreuse.py` part 2).

| Hand file | Code lines | Replacement |
| --- | --- | --- |
| `E2eHb/HbLemmas.lean` | 57 | `ListG` application, 0 lines |
| `E2eHb/HbLoop1.lean` | 302 | application of the `hb_loop1_g` form, about 70 lines |
| `E2eHb/HbLoop2.lean` | 308 | application of the `hb_loop2_g` form, about 65 lines |
| `E2eHb/HbReject.lean` | 80 | `rej_size_g` application, about 15 lines |
| total | 747 | about 150 |

The general files are 1097 code lines (ListG 65, SegG 494, V32 87, V32Loop 327, RejG 124). They are written only once.

## 4. Items left to the hand, and why

- The function head (array makeslice after the size check, header store) and tail. The instruction sequence differs with the field count and the receiver layout. The next candidate is a head template such as `rejHead` (not done).
- The delegate call and the layout of the callee frame (Deposit about 120 lines). This is the same work as IndexedAttestation. It is not generalized.
- Statements (`Stmt`). The slot list of the receiver and the frame differs for each type. We think that the IR and `.S` can produce them (judgment).
- The container assembly on the specification side (`dep_serialize`, `dep_toValue_surjective`). The field form differs for each type. `SpecG` generalizes the vector field part.
- Other element sizes of the 32-byte form, and loop forms outside the two forms (section 2).

## 5. Verification

| Check | Result |
| --- | --- |
| `lake build E2eHb E2eSeg E2eDep` | exit 0, 730 jobs (log 100) |
| `lake build --no-build E2e E2eAd E2eScal E2eList E2eHb E2eSeg E2eDep` | exit 0, `All targets up-to-date (1124 jobs)` (log 101) |
| axioms gate `gen/e2e/segaxioms_gate.py` | exit 0, PASS, declarations 6627, hand list 502, nonstandard 0, sorryAx 0 (log 102, `axioms-gate-seg.json`). `axioms-gate-seg2.json` and `axioms-gate-seg2-r5.json` after review r5 replace this json. The old file was not changed |
| gate control | Not run again with this script. The control of the same gate code is `axioms-gate-hb-plant.json` (FAIL, as expected) |
| prohibited words | `sorry`, `admit`, new `axiom`, `native_decide`, `bv_decide`: 0. Only four measured options are present (section 5.1) |
| home paths | 0 in new files |
| declaration drift (part 1) | base `6a78c591`, drift 0 (`decl-drift-hb.txt`). The commits after it did not change E2e, E2eAd and E2eScal |
| second work: `--no-build` 8 libraries (E2eDepW included) | exit 0, 1150 jobs (log 135) |
| second work: axioms gate `gen/e2e/seg2axioms_gate.py` | PASS, declarations 6851, hand list 517, nonstandard 0, sorryAx 0 (log 136, `axioms-gate-seg2.json`) |
| second work: gate control (planted `E2eDep.Planted`) | FAIL (as expected), sorryAx `E2eDep.Planted.planted_sorry` (log 138, `axioms-gate-seg2-plant.json`) |
| second work: declaration drift (base `6a78c591`, roots E2e, E2eAd, E2eScal) | drift 0. Control (one hash of a dump copy) drift 1 (logs 139–141, `decl-drift-seg.txt`) |
| Go differential test, hardware comparison | not run |

`STEPS-SEG.tsv` has the commands and exit codes. The logs are only local.

### 5.1 Measured options (all)

| Location | Option | Value | Measurement (fail / pass) | Cause |
| --- | --- | --- | --- | --- |
| `E2eDep/Accept.lean`, `dep_e2e_accept_main` | `maxHeartbeats` | 800000 | 200000 fails / 400000, 800000 pass (logs 95–97) | the length of one declaration: tactics 3.37 s, `simp` 1.11 s, kernel 1.58 s (log 98) |
| `E2eSeg/VTriLoop.lean`, `vtri_iter` | `maxHeartbeats` | 800000 | 200000 fails (third case) / 400000, 800000 pass (logs 130–132) | the case split runs the proof text once per size, three times in total |
| `E2eDepW/WitA.lean`, `dep_accept_runs` | `maxHeartbeats` | 4000000 | 200000, 1000000 fail / 2000000, 4000000 pass (logs 115, 120, 121) | `simp` AC sorting 20.1 s (log 122) |
| `E2eDepW/WitA.lean`, `P_len`, `hk308`, `hk324`, `hk330` | `maxRecDepth` | 2000 | 512 (default) fails / 1000, 2000, 5000, 20000 pass (logs 115, 117–119, measured with a whole-file setting) | list computation on a Host with 356 directives. After review r5 S2, it is set per declaration (log 145) |
| `E2eHb/WitHbA.lean`, `hb_accept_runs` (HistoricalBatch work) | `maxHeartbeats` | 2000000 | 200000, 400000 fail / 1000000 passes | `REPORT-HB.md` section 4 |

### 5.2 Attempt record (review r5 S5)

| Unit | Builds (fail / pass) | Strategy count | Fact |
| --- | --- | --- | --- |
| `SegG` + `ListG` | 3 / 2 (logs 48, 52–55) | 1 | nonlinear terms of `omega`, a remaining `rfl`, the instance binder of `type_of%` |
| `V32` | 2 / 1 (logs 56–58) | 1 | the `Directive` type name, `whnf` of the `nop` step |
| `V32Loop` | 1 / 2 (logs 59–61) | 1 | the flag expression at the exit |
| `V32Hb` | 3 / 2 (logs 62–66) | 2 | strategy 1: loop 1. Strategy 2: loop 2 (`lea` gap read, return slot value) |
| `RejG` | 4 / 1 (logs 68–72) | 1 | `open` error, an `OfNat` atom in the address expression, the last rsp expression |
| `E2eDep.Accept` | 11 / 1 (logs 83–94, 93 is a probe) | 1 | The proof grew step by step. The failures are a probe (`done`), a name collision, an argument count, an address expression |
| `VTriLoop` | 3 / 1 (logs 128–130, 133) + option measurement (131, 132) | 1 | the `OfNat` form of a stored value, `maxHeartbeats` |

- Two probe builds (logs 93, 129) changed a file for a short time to see the form of the goal. The probe of log 129 left two cases as `sorry`. That state was not committed, and it is not evidence for any claim. It was reverted immediately after the build.
- Compile iterations in one strategy counted as one attempt. This is the same interpretation as the list/vector work and the HistoricalBatch work.
- With this interpretation, no unit reached the 3-strategy limit. If the count is the build count, `RejG` and `E2eDep.Accept` are more than 3.

### 5.3 Record only (review r5 S3)

- The Lake `input_dir` `lv_dep_data` is declared, but no Lean file reads it. `depDataType_addr` is a hand definition (section 6).
- The object size 120 was set from a read of the data file (`Size_ = 0x78`). No Lean theorem ties this value to the data file. `NewobjectC … 120` is a hypothesis of the statement.

## 6. Trust items and limits

- `depDataType_addr` is a hand-written definition. Its value is the `at` line of `link-dep/data/depDataType.data`, and its form is the form of the list/vector work reader. The reason: the helper functions of the reader are not visible outside the module. `gen/e2e/depcheck_data.py` checks that the two are equal (SAME). `check.py` (f) compared that data file with the ELF.
- Each instance checks with `infix_sub` that the block templates are the same as the real code. The templates themselves are not trusted items.
- `lakefile.toml` only got appended items (`lean_lib` E2eSeg, two `input_dir`s, `lean_lib` E2eDep).
- The line classification is per line and ignores order (a limit of `hbreuse.py`).

## 7. Hand lines for the next type of the same family

The hand code lines used for Deposit were measured per part (`gen/e2e/segcost.py`, log 142). Comments and blank lines are excluded. The measurement is for one type.

| Part | Code lines |
| --- | --- |
| statements (machine) | 109 |
| statements (specification) + hand Desc | 113 |
| size reject proof | 22 |
| accept: helpers (scratch and object split) | 42 |
| accept: head steps (directives 0–40) | 113 |
| accept: loop use (block facts, `v32_loop` application) | 60 |
| accept: Data object, delegate call, end | 166 |
| specification bridge + pairs + Desc equality | 150 |
| witnesses (reject, accept) + newobject model | 201 |
| code include | 8 |
| link script | 85 |
| total | 1069 |

- The loop proof and the reject proof need about 60 and 22 lines. Before the general theorems, one loop was about 300 lines.
- The delegate call (166) and the witnesses (201) are the largest. Both write by hand the frame layout and memory layout that differ for each type.
- We think that the IR and `.S` can produce the statements (222) (judgment, not tested).
- The link script is a copy of the previous script (9 new lines of 85, section 3.1).

## 8. Items for the user

- Appended to `lakefile.toml`: four `lean_lib`s (E2eHb, E2eSeg, E2eDep, E2eDepW), four `input_dir`s (`lv_hb_norm_S`, `lv_dep_norm_S`, `lv_dep_data`, `lv_dep_lean_S`). The root `AGENTS.md` requires approval for a lakefile change.
- New instance value: `NewobjectC Heap depDataType_addr 120` (existing form). A witness model `BumpNew120` (`E2eDepW/BumpNew120.S`) was added.
- The base `1b5f524` of this branch is earlier than the review r4 fixes of the list/vector work branch. A merge is necessary before integration.
- The cost of the next type of the same family is the 1069 lines of section 7 (one-type measurement).

