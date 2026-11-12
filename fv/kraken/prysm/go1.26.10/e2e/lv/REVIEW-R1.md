# REVIEW R1: list/vector work (`fbf729a`, base `6a78c59`)

**Verdict: REQUEST_CHANGES.**
The reviewer model is `claude-fable-5-2`.
The reviewer is a new session that did not write the proofs.
The reviewer checked in a scratch copy of `git archive fbf729a`.
`.lake/packages` was copied from the worktree. `.lake/build` was not copied.
The planner wrote this file from the report of the reviewer. The review logs are only local.

## 1. Required fixes

| ID | Content |
| --- | --- |
| M1 | The `set_option maxRecDepth 100000` in `E2eList/WitSaA.lean:26` and `E2eList/WitScA.lean:27` has no recorded cause. Without this line, `WitSaA` compiles with 0 errors. In `WitScA`, only the first and third `example` fail (`simp` on `List.replicate 512`, recursion depth). `sc_accept_runs` does not need this line |

## 2. Suggested fixes

| ID | Content |
| --- | --- |
| S1 | Lines 73 and 76 of `STEPS.tsv` have run directory paths |
| S2 | The logs 26, 27, 65, 66, 08 that the report cites are not committed. Their content agrees with the report |
| S3 | "622 `E2eList.` names" in `ATTEMPTS.md` is wrong. There are 625 new rows, 434 start with `E2eList.`, 623 contain `E2eList` |
| S4 | The negative tests have no specification (`Desc`) mutation and no SyncCommittee size reject case. The two kinds that the reviewer ran behaved as designed |
| S5 | `E2eList/BumpAllocT.S` is not a Lake input |
| S6 | If the two lists have different lengths, `lvElems` is `emp`. All current statements fix the length 512. A variable-length list needs a new definition with a length condition |
| S7 | The esz 24 `MakesliceC` instance is not in `CONTRACTS.md` and `RUNTIME-1.26.10.md`. The reviewer agrees with the judgment that it is an instance of the existing form. The element type has pointers, so user confirmation is necessary |
| S8 | Finding LV-1 (wrapped negative displacement): the full ELF objdump has 153 operands of the wrapped displacement form |
| S9 | Items for the user: the remote name, the deadline not confirmed, the Go differential test not run |

Check of the planner on the remotes of S9: the remotes of this worktree are `kasey`, `my` (syjn99), `origin` (OffchainLabs), `upstream` (OffchainLabs).
The user heard this state at the start and chose to run.

## 3. Items the reviewer checked again

Kernel checks (rebuild of the reviewer):

- `lake build E2e E2eAd E2eScal E2eList`: exit 0, 1035 jobs, 1147 s. `--no-build`: exit 0.
- Axioms gate: PASS, declarations 5632, theorems 4684, hand list 462, nonstandard 0, `sorryAx` 0. All fields are the same as the committed `axioms-gate-lv.json`.
- The types of the 10 main theorems are the frozen statement defs of `dfc8b93`. After it, `StmtSa`, `StmtSc`, `Defs`, `Desc`, `Code`, `Data`, `Include`, `lv/link/` did not change.
- For the SyncCommittee `panicBounds` branch, `sc_iter` proves that it is not taken. It is not a premise.
- The two witnesses satisfy all premises of the frozen statements. SyncCommittee gets two `MakesliceC` instances from one `runtime.makeslice`.

Executed checks (runs of the reviewer):

- Declaration drift 0 (5007 = 5007). The source-build dump of the reviewer is byte-for-byte the same as the base dump and the head dump of the author. A separate build of the base tree was not done.
- Link check PASS all, the same BUNDLE `5c166606…`. 96 + 124 instructions, 446 + 568 bytes are the same as the ELF bytes. The sha256 of the ELF, objdump and nm are the same as `build-ids.txt`.
- `lvSliceType`: from the ELF bytes, Size_ 24, PtrBytes 8, kind 23, the element type is uint8.
- Negative tests: the 8 committed cases and the 8 cases of the reviewer, 16/16 behave as designed. The 3 specification mutations break the specification lemmas.
- Gate controls: a planted `axiom` is FAIL, a row removed from the hand list is FAIL, a changed hash is drift 1.
- LV-1 reproduction: Kraken reads `lea 0xffffff1c(%rdi),%rdx` as `disp := ↑4294967068`. The disp32 of the ELF bytes is −228. The committed `.S` files have no wrapped displacement.
- No prohibited tokens. Compared with the base, the only change that is not an addition is the append to `lakefile.toml`.

Reading judgments:

- The strength of the statements is the same as the `E2eScal.H4.dd_accept_stmt` family. There is no `⋆ True`. No premise makes the goal vacuous.
- The hand `Desc` agrees with consensus-specs altair mainnet.
- There is no new contract form.
- Witness values: the addresses are not 8-aligned, and `guard = 0`, `ra = 0` (same as `WitDdA`).

Not run: the separate build of the base tree, `stale_olean.py`, the remaining 10 committed negative cases, the Go differential test, the hardware comparison, IndexedAttestation.
