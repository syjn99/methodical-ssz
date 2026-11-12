# CHECKS-HB: remaining HistoricalBatch checks (declaration drift, negative tests, HbLoop2 time)

These are the three checks that were N in `REPORT-HB.md`. No independent review was done.

## 1. Declaration drift (X)

- Base `6a78c591`, roots E2e, E2eAd, E2eScal. It is the same method as `decl-drift-lv-t3.txt` of IndexedAttestation.
- The base dump of the list/vector work was used again (sha256 `96f2fb34…`). It was not made again.
- Head dump: `decl_dump.lean`, 240 modules (E2eList, E2eHb included), exit 0, 83 s (log 38).
- Result: `SUMMARY base=5007 head=5007 drift=0 allowed=0` (log 39). File `decl-drift-hb.txt`.
- Control: one type hash in a copy of the head dump was changed. exit 1, `drift=1` (log 40).
- This control tests only the comparator. It does not test the dump generator.
- E2eList is not in the roots. `git diff 1b5f524 --diff-filter=M` shows only `lakefile.toml` as a changed existing file.

## 2. Negative tests (X)

- Cases `negcases-hb.json`, runner `gen/e2e/lvnegative.py` (not changed). exit 0, 56 s (log 41).
- Result `negative-hb.json`: 10 of 10 passed. control_pass 3, inside 7.

| Case | Kind | Target theorem | Result |
| --- | --- | --- | --- |
| `hb-control-reject`, `-iter1`, `-accept` | control | reject, one iteration, accept | control_pass |
| `hb-stmt-size524289` | statement size constant | `hb_e2e_reject_size_main` | inside |
| `hb-size524289` | code size constant | `hb_e2e_reject_size_main` | inside |
| `hb-loopbound8191` | loop bound | `hb_iter1` | inside |
| `hb-elem31` | element size (memmove count) | `hb_iter1` | inside |
| `hb-shl6` | element size (index shift) | `hb_iter1` | inside |
| `hb-stmt-heap` | heap amount of the accept postcondition | `hb_e2e_accept_main` | inside |
| `hb-stmt-len8191` | len slot of the accept postcondition | `hb_e2e_accept_main` | inside |

- A code mutation aims at the module that steps through that directive. The accept module imports the loop theorems, so it is not a target of code mutations.

## 3. Why HbLoop2 is slower than HbLoop1 (X, profile)

In the profiler (logs 42, 43), 12.9 s of the 13.4 s of HbLoop2 is the kernel type check.
That time is in the one declaration `hb_iter2` (log 44: 12.8 s in a copy with only that theorem).
The elaboration, `simp` and tactic execution times are similar in the two modules (about 0.7–0.9 s, 1.3 s).
Excluded candidates: label lookup (`klabel`, 82–155 ms at indexes 26–154, log 48), `List.drop` at high indexes (less than 10 ms, log 47), the `rfl` of `k + 132 + 1 = k + 133` (12.8 s also with `omega`, log 46).
Cause: the `laddr` (omega) proof that closes the source address expression `bf + (rax <<< 5) * 1 + 262144 = bf + 262144 + ofNat (32 * i)`.
The kernel check of a theorem with only that expression is 12.2 s. The same form without the constant 262144 is 15.6 ms (log 51).
It appears that the cost increases with a large constant when the kernel checks the proof term that `omega` made. The steps inside it were not measured.
