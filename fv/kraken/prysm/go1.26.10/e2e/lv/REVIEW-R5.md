# REVIEW R5: two targets

The reviewer model is `claude-fable-5-2`.
The reviewer is a new session that did not write the proofs. It is not an r1–r4 reviewer.
The reviewer checked in two scratch copies of `git archive`.
The planner wrote this file from the report of the reviewer. The review logs are only local.
The commit of this file is a documentation change after the review.

## Target 2: this branch, `9e2272b..4d42634` (review r4 suggested fixes)

**Verdict: APPROVE.** There is no required fix.

- The fixes S1–S9 are really applied. There are no other changes (13 files).
- Kernel checks (build of the reviewer): `lake build E2e E2eAd E2eScal E2eList` exit 0, 1082 jobs. `WitIaR2`, `WitIaR`, `WitIaA`, `WitSaA`, `WitScA` were built from source. The rest was replayed.
- Executed checks: axioms gate PASS, declarations 6451, nonstandard 0, `sorryAx` 0. Byte-for-byte the same as `axioms-gate-lv-t3-r4.json`.
- Compared with the dump of the r4 reviewer: ADDED 49, CHANGED 0, REMOVED 0.
- All 14 negative tests passed (control 5, inside 9).

Suggested fixes:

| ID | Content |
| --- | --- |
| T2-S1 | The case `lv-ia-nz-mis-no-he0nz` fails at `intro`. It fails when any binder is removed. It does not test that `e0 ≠ 0` is necessary |
| T2-S2 | No mutation aims directly at the offset reject machine theorem `ia_e2e_reject_offset_main` |
| T2-S3 | `REPORT.md` section 2 names `axioms-gate-lv-t3.json` as the gate result. The current one is `axioms-gate-lv-t3-r4.json` |

Not run: drift against the base, the link check, the gate and drift controls, `stale_olean.py`, the thresholds of the moved options, the Go differential test, the hardware comparison.

## Target 1: branch `syjn99/ssz-fv-hb`, `1b5f524..a1c5191` (HistoricalBatch, generalized lemmas, Deposit)

**Verdict: REQUEST_CHANGES.** No proof defect was found. There are 3 required fixes.
That branch is not merged into this branch. Its report is on that branch.

| ID | Content |
| --- | --- |
| M1 | Two records in `REPORT-SEG.md` are wrong. It states that the general files have no `maxHeartbeats`, but `VTriLoop.lean:214` has 800000. Section 5 names only one option |
| M2 | `REPORT-SEG.md` section 3.1 compares two counts with different scopes (HistoricalBatch 346 is 16 files, Deposit 236 is 5 files). The HistoricalBatch value for the same scope is 219 |
| M3 | `hb_e2e_reject_size_main` has no witness, and `REPORT-HB.md` does not record that |

Items the reviewer checked again (summary):

- Kernel checks: build of 8 libraries exit 0, 1150 jobs. The 38 new modules were built from source.
- Executed checks: two axioms gates, drift 0 (control 1), negative tests HistoricalBatch 10/10 and Deposit 9/9, `check.py` of the two link bundles, the reuse and cost scripts. All are the same as the committed results.
- Reading judgments: the 10 main theorems have the frozen defs as their types. The generalization is a real generalization. The `type_of%` re-derivation is sound. The contracts are only of existing forms.

The 10 suggested fixes and the user items were sent to the worker.
User items: the lakefile appends (`lean_lib` 4, `input_dir` 4), the new instance value `NewobjectC … 120`, the merge of the two branches.
