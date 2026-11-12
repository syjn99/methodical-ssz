# REVIEW R4: list/vector work (`9e2272b`, changes `29683a8..9e2272b`, base `6a78c59`)

**Verdict: APPROVE.**
There is no required fix. There are 9 suggested fixes.
The scope is the `link/conv.py` fix (`93b3f2a`) and the `IndexedAttestation` decoder.
The reviewer model is `claude-fable-5-2`.
The reviewer is a new session that did not write the proofs. It is not the r1, r2 or r3 reviewer.
The reviewer checked in a scratch copy of `git archive 9e2272b`.
The planner wrote this file from the report of the reviewer. The review logs are only local.
The commit of this file and the application of the suggested fixes are changes after the review. Those changes did not get a review.

## 1. Suggested fixes

| ID | Content |
| --- | --- |
| S1 | The size reject and offset reject main theorems (`ia_e2e_reject_size_main`, `ia_e2e_reject_offset_main`) have no witness. `fv/AGENTS.md` requires a witness for each main theorem. The SyncAggregate and SyncCommittee size rejects also have no witness, and r1–r3 accepted that |
| S2 | The `maxRecDepth 1024` list in `REPORT.md` section 4 does not include the size reject and offset reject theorems (`IaReject.lean:28`, `:98`, logs 123, 124) |
| S3 | `WitIaR.lean:30` and `WitIaA.lean:33` set `maxRecDepth` for the whole file. In WitIaR, only `P_len` and `hk284` need the option |
| S4 | `negative-lv-t3.json` has two `prechecks` entries. The first is from the failed run (log 251). The 8 case rows are correct |
| S5 | The times in lines 105, 107, 108 of `STEPS.tsv` are wrong. The log mtimes are 22:48:35Z, 22:49:32Z, 22:50:02Z |
| S6 | "cannot be proved as written" is too strong. There is no counterexample model. What is confirmed: if the itab label is 0, `je` cannot be refuted, and the proof method fails there |
| S7 | Condition 1 of `REPORT.md` names only `MakesliceC` and `MemmoveC`. IndexedAttestation also uses `NewobjectC`, `ConvT64C`, `FmtErrorfDWC` |
| S8 | No negative case aims at the `_nz` theorems, the offset reject or the specification theorems |
| S9 | `conv.py` keeps as is the wrapped displacements of the SIB form without a base and the segment form without a base. This objdump has 0 of each. If a wrapped form remains, `conv.py` does not fail |

## 2. `conv.py` (`93b3f2a`)

Executed checks (runs of the reviewer, python only):

- `--norm` output of the old `conv.py` and the new `conv.py`: 641 function files, 104 changed files, 161 changed lines. Each changed line is the same as the two's complement rewrite of the reviewer. 0 other differences.
- Operand forms of the objdump: 161 wrapped disp32 with a base, 0 without a base, `%rip` 0, segment form 0.
- Constructed inputs: immediates, `%rip`, movabs, positive `0x7fffffff`, 7-digit and 9-digit numbers stay the same. Base+index, `*disp(%reg)`, `%fs:disp(%reg)` and AVX forms change correctly.
- Made again, byte-for-byte the same: the 7 bundles and `lv/link-t3` 41/41, `link/out` 30/30, `link/norm` 136/136.
- selftest passed.
- `check.py`: exit 0, PASS (a)–(f). The RESULT is byte-for-byte the same as the committed `lv/link-t3/RESULT`.

Reading judgment: in 64-bit mode, a disp32 with a base is always sign-extended. Thus this rewrite cannot change a correct operand.

## 3. IndexedAttestation

Kernel checks (build of the reviewer):

- `lake build E2e E2eAd E2eScal E2eList`: exit 0, 1080 jobs, 127.3 s, sampled RSS 7.72 GiB. The 45 E2eList modules were built from source. 270 jobs were replayed.
- Limit: E2e, E2eAd, E2eScal and the packages were replayed from the `.lake` of the worktree. Their sources are the same as the base.
- `--no-build`: exit 0, 1080 jobs.

Executed checks (runs of the reviewer):

- Axioms gate: PASS, declarations 6402, theorems 5341, hand list 485, nonstandard 0, `sorryAx` 0. Byte-for-byte the same as the committed `axioms-gate-lv-t3.json`.
- The declaration dump is byte-for-byte the same as the dump of the author. drift 0 (5007 = 5007).
- Compared with the gate dump of r3 (5632 lines): ADDED 770, CHANGED 0, REMOVED 0. The SyncAggregate and SyncCommittee declarations did not change after r3.
- All 8 IndexedAttestation negative tests passed (control 2, inside 6). Same as the committed file, except the seconds field.
- Threshold samples: `IaReject` fails without `maxRecDepth`. `IaAccept` fails at `maxHeartbeats 400000`.
- The frozen files such as `StmtIa.lean` have no difference after `e13053a`. `StmtIaNz.lean` has no difference after `714989f`. The `_nz` defs are the frozen defs with only `(he0nz : e0 ≠ 0)` and the names added.
- All 11 main theorems have the frozen defs as their types.
- The changes have no prohibited tokens, home paths, session ids or hold-out type names. The 18 commits are linear, and `29683a8` is an ancestor.

Reading judgments:

- The statements have meaning. The accept statement keeps the input, the receiver, `R`, the frame, rsp + 8, rbp, r14 and the heap `avail − (8n + 432)`. There is no `⋆ True` tail.
- The premises of `ia_accept_spec_stmt` are not vacuous (`pia_roundtrip`).
- The witnesses prove all premises. The 9 contract hypotheses come from models. The frame of `WitIaR` is `fun _ => True` (same as the precedent `WitLuMa`).
- The defect description is a fact. Directives 103–106 and 66–69 are `mov global,%rcx; test; je; mov 0x8(%rcx),%rcx`.
- `e0 ≠ 0` is fair. RESULT (b) ties `go_itab._errors.errorString_error = 0xd28520`.
- The delegate error is unreachable: the call at 187 always gets rcx = 0x80. The premises of the size reject, offset reject, accept, alignment reject and overflow reject cover all inputs.
- The contracts are only of existing forms. `Fk/Contracts.lean` did not change.
- `len ≤ cap` and `cap < 2^63` are recorded and necessary.

Not run: the base tree build, the source rebuild of E2e/E2eAd/E2eScal and the packages, the gate control, the drift control, `stale_olean.py`, the WitIaA threshold measurement, the Kraken probe, `opt-r1/link`, the ELF rebuild, the Go differential test, the hardware comparison.

## 4. Items for the user to decide (reviewer list)

- The `_nz` correction after the freeze. The reviewer cannot check the recorded user approval.
- The `conv.py` change. The same applies.
- The lakefile change of `e13053a`.
- The size reject and the offset reject without witnesses (S1).
- The attempt count of WitIaA.
