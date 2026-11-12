# REVIEW R3: list/vector work (`650b1f5`, changes `d169e4b..650b1f5`, base `6a78c59`)

**Verdict: APPROVE.**
There is no required fix. There are 2 suggested fixes.
The reviewer model is `claude-fable-5-2`.
The reviewer is a new session that did not write the proofs. It is not the r1 or r2 reviewer.
The reviewer checked in a scratch copy of `git archive 650b1f5`.
`.lake/packages` was copied from the worktree. `.lake/build` was copied from the source build of the r2 reviewer (`d169e4b`).
The planner wrote this file from the report of the reviewer. The review logs are only local.
The commit of this file and the N1 and N2 fixes are documentation changes after the review. Those changes did not get a review.

## 1. Status of the r2 items

M1, M2, S1, S2, S3, S4, S5: all closed.

## 2. Suggested fixes

| ID | Content |
| --- | --- |
| N1 | `REPORT.md` section 4 states that the WitSaA and WitScA rows have the values after the fixes. Two fields differ from the logs. The WitSaA wall clock 15.7 s is 17.7 s in log 96. The WitScA RSS 2.07 GiB is 2.06 GiB in log 97 |
| N2 | `negative-lv.json` was not made again after the r2 fixes. This is acceptable. The negative cases do not use the Wit modules. The reviewer ran them again, and the results are the same |

## 3. Items the reviewer checked again

Kernel checks (build of the reviewer):

- `lake build E2e E2eAd E2eScal E2eList`: exit 0, 1036 jobs, 24.0 s. Built 2(`WitSaA` 14 s, `WitScA` 17 s), Replayed 284.
- `--no-build`: exit 0, 1036 jobs.
- `WitSaA` compiles with `maxHeartbeats 2000000`, and `WitScA` with 4000000. There is no `maxRecDepth` setting.
- Limit: the other modules were replayed from the build of the r2 reviewer. Their sources are byte-for-byte the same as the r2 tree.

Executed checks (runs of the reviewer):

- Axioms gate: PASS, declarations 5632, theorems 4684, hand list 462, nonstandard 0, `sorryAx` 0. Same as the committed `axioms-gate-lv-r2.json`.
- The declaration dump is byte-for-byte the same as the dump of the author. drift 0 (5007 = 5007).
- 26 negative tests: 25 passed (control 7, inside 18), 1 outside (`lv-sa-bitslen63`). Per case, all fields except the seconds field are the same as the committed `negative-lv.json`.
- `git diff d169e4b 650b1f5 -- fv/kraken/lean` is only `WitSaA.lean` and `WitScA.lean`. The theorem statements and defs did not change.
- `git diff dfc8b93 650b1f5` is empty for `StmtSa`, `StmtSc`, `Defs`, `Desc`, `Code`, `Data`, `Include`, `lv/link/`.
- The Lean of the changes has no prohibited tokens.
- History: `d169e4b` is an ancestor of `650b1f5`. There are only 4 new commits.
- The committed files have no home paths, run directories or session ids.
- objdump counts: 641 TEXT functions (UnmarshalSSZ 211, MarshalSSZTo 211, SizeSSZ 211, MarshalSSZ 6, ValidateBitvector 1, ValidateBitlist 1). 153 for the narrow pattern, 161 for the wide pattern, 104 functions (67 + 37). The 222 committed `.S` files have neither pattern.
- Lines 96–102 of `STEPS.tsv` agree with the `heavy.py` records and the logs.

Reading judgments:

- The two rewritten `example`s are real checks. Their type is the type of `sc_accept_runs` applied to the same arguments. They prove the premises. They do not assume them.
- An `example` makes no declaration. An equal dump is not evidence about the `example`s. The evidence is the build above.
- The `maxHeartbeats` values are two times the pass values that reviewer r2 measured. The cause and the threshold are next to each option. The thresholds are marked as reviewer measurements.
- The decision list in `REPORT.md` section 9 contains the five items of r2 and the three earlier items.

Not run: a full source rebuild of `650b1f5`, a base tree build, the drift control, the gate control, the `maxHeartbeats` threshold measurement, the link check (`lv/link` did not change after `dfc8b93`), `stale_olean.py`, the script self-tests, the Go differential test, the hardware comparison, IndexedAttestation.
