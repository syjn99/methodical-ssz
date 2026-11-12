# REVIEW R2: list/vector work (`d169e4b`, changes `fbf729a..d169e4b`, base `6a78c59`)

**Verdict: REQUEST_CHANGES.**
The reviewer model is `claude-fable-5-2`.
The reviewer is a new session that did not write the proofs. It is not the r1 reviewer.
The reviewer checked in a scratch copy of `git archive d169e4b`.
`.lake/packages` was copied from the worktree. `.lake/build` was not copied.
The planner wrote this file from the report of the reviewer. The review logs are only local.

## 1. Required fixes

| ID | Content |
| --- | --- |
| M1 | The two `set_option maxRecDepth 100000 in` (lines 126, 134) in `E2eList/WitScA.lean` are wider than the necessary value. 1024 fails and 2048 passes. The measured threshold is not in the records. If `(by simp) (by simp)` changes to term proofs (`List.length_replicate`, `List.eq_of_mem_replicate`), it compiles without the option. The line number 127 in the records must be 126 |
| M2 | "All functions of this objdump file are SSZ methods (… HashTreeRoot)" in `FINDINGS-CANDIDATES.md` is wrong. There are 641 TEXT functions: UnmarshalSSZ 211, MarshalSSZTo 211, SizeSSZ 211, MarshalSSZ 6, `ssz.ValidateBitvector` 1, `ssz.ValidateBitlist` 1. There are 0 HashTreeRoot. 153 and 104 are correct. The 104 are 67 UnmarshalSSZ and 37 MarshalSSZTo |

Closed part of r1 M1: the scope is only the two `example`s. The cause is recorded. `WitSaA.lean` has no `maxRecDepth`.

## 2. Suggested fixes

| ID | Content |
| --- | --- |
| S1 | `maxHeartbeats 16000000` (`WitSaA.lean:90`, `WitScA.lean:95`) is necessary. The default and 400000 fail in `whnf`. WitSaA passes at 1000000. WitScA fails at 1000000 and passes at 2000000. The threshold is not in the records |
| S2 | The line counts "WitSaA 126, WitScA 134" in `REPORT.md` section 5 are out of date. At `d169e4b` they are 125 and 139 |
| S3 | Count for finding LV-1 (wrapped negative displacement): the wide pattern `0x[89a-f][0-9a-f]{7}\(%` gives 161. The 8 added ones are `lea` of the form `0xffd6xxxx(%r..)`. All 161 are in the same 104 functions. The 222 committed `.S` files have neither form |
| S4 | `REPORT.md` section 7 states that the negative tests include Desc mutations. The Desc mutation files are cut from the target. They go only up to `prysmS*Desc_fixedSize` or `ps*_toValue_fits`. No Desc mutation tests `*_spec_k` |
| S5 | `WitSaA.lean:25-26` and `WitScA.lean:26-27` each have two blank lines |

## 3. Items for the user to decide (reviewer list)

- The esz 24 `MakesliceC` instance (r1 S7), the deadline, the Go differential test.
- The lakefile change of `3bb6cc1`. The root `AGENTS.md` requires user approval for a lakefile change. The task instruction permits new library additions. It does not name the `input_dir` addition.
- The handling path for LV-1 (`conv.py` signed displacement, `check.py` range check, Kraken request).
- The reading of the attempt count ("compile iterations in one strategy are one attempt", `REPORT.md` section 3).
- The remote name: `origin` is OffchainLabs. The record that the user accepted this state is only in `REVIEW-R1.md`. The reviewer cannot check it.

## 4. Items the reviewer checked again

Kernel checks (rebuild of the reviewer):

- `lake build E2e E2eAd E2eScal E2eList`: exit 0, 1036 jobs, 1176 s, sampled RSS max 24.4 GiB. `--no-build`: exit 0.
- Axioms gate: PASS, declarations 5632, theorems 4684, hand list 462, nonstandard 0, `sorryAx` 0. All fields are the same as the committed `axioms-gate-lv-r1.json`.
- The dump of the reviewer is byte-for-byte the same as the r1 dump of the author and the dump before the fixes. In `fbf729a..d169e4b`, the declaration types, def values and axiom sets did not change.
- Separate build of the base tree (`6a78c59`): 982 jobs, exit 0, 1153 s. The dump is byte-for-byte the same as the base dump of the author. drift 0 (5007 = 5007).

Executed checks (runs of the reviewer):

- Drift control: `112 + 0` was planted in `E2eScal.WitBhU.s0` of the base copy. exit 1, `CHANGED`. Reverted.
- All 26 negative tests: 25 passed (control 7, inside 18), 1 outside (`lv-sa-bitslen63`). All fields except the seconds field are the same as the committed `negative-lv.json`.
- The 8 new cases: the mutation files do not import `E2eList.Desc` and `E2eList.Defs`. The theorems see the mutated Desc.
- Lake input: if one comment line is added to `E2eList/BumpAllocT.S`, `--no-build E2eList` is exit 3. After the revert, it is exit 0.
- Counts: 625 new declarations, 0 deleted, 434 start with `E2eList.`, 623 contain `E2eList`.
- `lv/`, `E2eList/` and the 6 new scripts have no home paths, run directories or session ids.
- The log excerpts (08, 26, 27, 65, 66) in `ATTEMPTS.md` and the descriptions of logs 86–95 agree with the local logs.

Reading judgments:

- `git diff dfc8b93 d169e4b` is empty for `StmtSa`, `StmtSc`, `Defs`, `Desc`, `Code`, `Data`, `Include`, `lv/link/`. The types of the 10 main theorems are the frozen statement defs.
- Compared with the base, the lakefile has only appends. Compared with `fbf729a`, only the `needs` of the `E2eList` entry changed.
- The added files have no prohibited tokens.
- No path was found by which the inline method of `lvnegative.py` passes vacuously.
- Section 6a of `DESIGN.md` agrees with `Defs.lean` and `StmtSc.lean`.
- `REPORT.md` keeps K, X and N separate.

Not run: the link check (`lv/link` did not change after r1), the gate control, `stale_olean.py`, the script self-tests, the Go differential test, the hardware comparison, IndexedAttestation.

Mistake that the reviewer reported: a dump command overwrote one local scratch file of the author (outside the worktree).
The sha256 and size of the new content are the same as the base dump. They are also the same as the copy of the head dump of the r1 reviewer. It is unlikely that the content changed.
