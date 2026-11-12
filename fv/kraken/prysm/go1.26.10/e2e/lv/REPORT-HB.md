# REPORT-HB: `HistoricalBatch.UnmarshalSSZ` hand proof and SyncCommittee reuse measurement

**Verdict: conditional.**

Conditions:

1. Runtime calls are contract hypotheses (two `MakesliceC`, `MemmoveC`). There is no refinement proof of the Go runtime machine code.
2. The premises `writeBarrier = 0` and `guard < rsp` fix the path. The write-barrier path and the morestack path are not proved.
3. The Go differential test and the x86-64 execution comparison were not run.
4. Each K below is a kernel-check result of the author's build. Independent review r5 reproduced the build and the checks and asked for fixes to the records and to one witness (REQUEST_CHANGES). This file gives the state after those fixes. The fixes did not get a new review.

## 1. Pins

| Item | Value |
| --- | --- |
| Branch | `syjn99/ssz-fv-hb` (base `1b5f524`, the head of `claude/ssz-fv-list-vector-20261112`) |
| ELF sha256 | `c6403c02a110ffd6fe6d31a3c89cd395ac457b5d62e60e2e611b8ab9a8dd911e` (same as SyncCommittee) |
| objdump sha256 | `580b0da9…` (same as `build-ids.txt`). It was not made again. The file of the list/vector work directory was used |
| Link bundle | `lv/link-hb/RESULT`: `PASS all`, BUNDLE `66e6154a…` |
| Kraken, EthLib, Lean | Same as section 1 of the list/vector work `REPORT.md`. `lake update` was not run |
| `.lake` | APFS clone from the parent worktree. First `lake build E2eList`: exit 0, 749 jobs, 51 s |
| Heavy jobs | `heavy.py` outside the repository, cap 40960 MB, one at a time |
| Model | Implementation `claude-opus-5-5` |

## 2. Coverage (K kernel-checked, X executed only, N not proved)

| Path | Kind | Theorem | File |
| --- | --- | --- | --- |
| link (a)–(f) | X | `lv/link-hb/RESULT` | `gen/e2e/hblink.py` |
| size reject | K | `hb_e2e_reject_size_main : hb_reject_size_stmt` | `E2eHb/HbReject.lean` |
| loop 1 one iteration (the two bounds checks do not branch) | K | `hb_iter1` | `E2eHb/HbLoop1.lean` |
| loop 1 8192 iterations | K | `hb_loop1`, `hb_exit1` | `E2eHb/HbLoop1.lean` |
| loop 2 one iteration | K | `hb_iter2` | `E2eHb/HbLoop2.lean` |
| loop 2 8192 iterations | K | `hb_loop2`, `hb_exit2` | `E2eHb/HbLoop2.lean` |
| accept | K | `hb_e2e_accept_main : hb_accept_stmt` | `E2eHb/HbAccept.lean` |
| specification bridge | K | `phb_serialize`, `phb_roundtrip`, `phb_accepted_is_enc`, `phb_spec_accepts_iff` | `E2eHb/HbSpec.lean` |
| accept, specification | K | `hb_e2e_accept_spec_k : hb_accept_spec_stmt` | `E2eHb/HbSpecK.lean` |
| size reject, specification | K | `hb_e2e_reject_size_spec : hb_reject_size_spec_stmt` | `E2eHb/HbSpecK.lean` |
| reject completeness | K | `hb_e2e_reject_complete : hb_reject_complete_stmt` | `E2eHb/HbSpecK.lean` |
| hand `Desc` = producer `Desc` | K | `prysmHbDesc_deserialize_checker` | `E2eHb/HbDescEq.lean` |
| accept witness | K | `WitHbA.hb_accept_runs` and three concrete inputs (0, representative, 0xff) | `E2eHb/WitHbA.lean` |
| size reject witness | K | `WitHbR.hb_reject_runs` (lengths 524287, 524289, 0, review r5 M3) | `E2eHb/WitHbR.lean` |
| axioms gate | X | PASS, nonstandard 0, sorryAx 0 | `lv/axioms-gate-hb.json` |
| gate control (planted `sorry`) | X | FAIL (as expected) | `lv/axioms-gate-hb-plant.json` |
| MarshalSSZTo, SizeSSZ, HashTreeRoot | N | out of scope | |
| morestack, write barrier on | N | the premises block them | |
| negative test (mutation) | X | `negcases-hb.json` 10/10 (control 3, mutation 7). The mutations of the specification pairs and reject completeness are in `negcases-spec.json` | `CHECKS-HB.md` section 2, `negative-hb.json`, `negative-spec.json` |
| declaration drift check | X | base `6a78c591`, roots E2e, E2eAd, E2eScal: drift 0, planted control drift 1 | `decl-drift-hb.txt`, `decl-drift-seg.txt` |

The frozen statements were committed in `b3cb1ca`. They did not change after that. No statement changed to N.
`hb_iter2` and `hb_loop2` are not frozen statements. The return slot value was added to the conclusion during the work (section 5).

## 3. Reuse measurement

### 3.1 Method

`gen/e2e/hbreuse.py` divides the non-blank lines of the HistoricalBatch files into three classes.
"verbatim" is the case where the SyncCommittee source has the same line.
"mechanical" is the case where the line is the same as a SyncCommittee line after renames and number changes.
"new" is the case where neither applies. Comment and documentation lines are counted separately.
The comparison is per line and ignores order. A short line such as `kunfold` easily becomes verbatim.
Thus this count is the quantity of transferred text. It is not evidence that the proof structure is the same.

### 3.2 Result (log 37)

| HistoricalBatch file | SyncCommittee source | verbatim | mechanical | new | comment/doc |
| --- | --- | --- | --- | --- | --- |
| `E2eHb/Code.lean` | `E2eList/Code.lean` | 2 | 2 | 1 | 7 |
| `E2eHb/Defs.lean` | `E2eList/Defs.lean`, `Desc.lean` | 1 | 4 | 10 | 18 |
| `E2eHb/StmtHb.lean` | `E2eList/StmtSc.lean` | 92 | 49 | 26 | 43 |
| `E2eHb/HbReject.lean` | `E2eList/ScReject.lean` | 56 | 23 | 1 | 8 |
| `E2eHb/HbLemmas.lean` | `E2eList/ScLemmas.lean` | 29 | 19 | 9 | 7 |
| `E2eHb/HbLoop1.lean` | `E2eList/ScLoop.lean` | 155 | 84 | 63 | 25 |
| `E2eHb/HbLoop2.lean` | `E2eList/ScLoop.lean` | 148 | 93 | 67 | 18 |
| `E2eHb/HbAccept.lean` | `E2eList/ScAccept.lean` | 118 | 94 | 34 | 22 |
| `E2eHb/HbSpec.lean` | `E2eList/ScSpec.lean` | 32 | 47 | 46 | 15 |
| `E2eHb/HbSpecK.lean` | `E2eList/ScSpecK.lean` | 8 | 12 | 11 | 5 |
| `E2eHb/HbSpecChecker.lean` | `E2eList/ScSpecChecker.lean` | 4 | 0 | 1 | 4 |
| `E2eHb/HbDescEq.lean` | `E2eList/ScDescEq.lean` | 6 | 25 | 4 | 9 |
| `E2eHb/WitHbA.lean` | `E2eList/WitScA.lean` | 40 | 22 | 31 | 28 |
| `gen/e2e/hblink.py` | `gen/e2e/lvlink.py` | 36 | 0 | 27 | 17 |
| `gen/e2e/hbaxioms_gate.py` | `gen/e2e/lvaxioms_gate.py` | 24 | 0 | 2 | 11 |
| `gen/e2e/AxiomsHb.lean` | `gen/e2e/AxiomsLv.lean` | 0 | 6 | 13 | 1 |
| total | | 751 | 480 | 346 | 238 |
| `E2eHb/HbLoop2.lean` | `E2eHb/HbLoop1.lean` (outside the total) | 207 | 62 | 39 | 18 |

Of the 1577 proof code lines (comments excluded), 78% are verbatim or mechanical.
22% (346 lines) are new text.

### 3.3 Items imported without a copy

| Imported item | SyncCommittee lines | Used in |
| --- | --- | --- |
| `lvHdrs`, `lvElems` (`Defs.lean`) | 5 | statements, loops, accept |
| `zz`, `lvElems_snoc`, `lvHdrs_length`, `lvHdrs_snoc`, `lv_flatten_split`, `jge_false512` (`ScLemmas.lean`) | 40 | `HbLemmas`, loops |
| `laddr` macro (`ScLoop.lean`) | 6 | loops, accept |
| `headWidth_inline`, `bodyWidth_inline`, `assemble_inline_ok` (`ScSpec.lean`) | 16 | `HbSpec` |
| `BumpAllocT`, `bump_makeslice_t1`, `bump_makeslice_t24` (`BumpT.lean`, `BumpAllocT.S`) | 164 | witness |
| `E2eList.Data.lvSliceType_addr` | data 1 | contract instance |

The total is about 231 lines. No contract instance and no witness model was written new.
`E2eList.WitScA.u8_ne_slice` (3 lines) could not be imported, so it was copied. That module declares its own `Host` instance.

### 3.4 Newly written parts and why

| File | New part | Reason |
| --- | --- | --- |
| `Defs` | `PHb`, `prysmHbDesc` | it is a new type |
| `StmtHb` | one local slot, second header, second input, second array and elements, constants | there are two fields and four frame slots |
| `HbReject` | one line of the frame size expression | `sub $0x38` |
| `HbLemmas` | three theorems in the 32/8192 version | the SyncCommittee theorems fix 48/512 in the statement |
| `HbLoop1` | two `shl $5`, the `jb` overflow check does not branch, fourth local slot, store order, `shl5` notation | the compiler produced a different index computation |
| `HbLoop1` | `shl5` notation | the width of the term that `kshl64` produces is `Width.W64.bits`. Its syntax differs from `x <<< 5`, so `ecancel` did not match it |
| `HbLoop2` | directive numbers, `nop` positions, receiver offsets, `lea 0x40000`, return slot value | the step sequence of the second loop differs from the first |
| `HbLoop2` | the return slot value `k + 133` is in the conclusion | the last call is in the loop. In SyncCommittee, the tail field wrote that slot again |
| `HbAccept` | the middle 86–103 | the makeslice of the second array. It is a copy of the head steps |
| `HbSpec` | 32-byte version lemmas, `v32_serialize`, `v32_of_bytes`, the container theorem for two vector fields | the SyncCommittee lemmas fix 48. The field form is different |
| `HbSpecK` | length lemmas for the two fields | there are two fields |
| `WitHbA` | memory layout, addresses, two inputs | the receiver, frame and heap sizes are different |
| `hblink.py` | function name, type word assertion | it is a new function |

### 3.5 Parts that a generator can produce

This is a judgment. No generator was made or tested.

- Can be produced as is: `Code`, `HbSpecChecker` (`lvdescterm.py` already produces it), `HbDescEq`, `HbSpecK`, `AxiomsHb`, the link script.
- Can be produced from the IR and `.S`: `StmtHb` (field offsets, frame size, heap total), `HbReject` (only the directive numbers and the frame size differ), the memory layout of `WitHbA`.
- After one generalization with a size parameter, no generation is necessary: `HbLemmas`, the 32-byte lemmas of `HbSpec`.
- Can be produced if per-directive templates exist: the `kat` sequence and the load and store steps of one loop iteration. A template for each directive kind is necessary.
- Items that needed a hand: the exact form of the `shl5` term, the `jb` branch inequality, the decision to put the return slot value in the conclusion, the memory form of the loop invariant.

## 4. Time and memory

Method: `heavy.py` records, one run (n = 1), sampled RSS is the group sum (upper-bound estimate). The module time is the Lake output.

| Module | Module time | Wall clock | RSS |
| --- | --- | --- | --- |
| StmtHb | 3.4 s | 9.3 s | 1.96 GiB |
| HbReject, HbLemmas | 4.5 s, 3.0 s | 6.2 s | 3.25 GiB |
| HbLoop1 | 6.8 s | 9.4 s | 2.10 GiB |
| HbLoop2 | 20 s | 22.8 s | 5.76 GiB |
| HbAccept | 7.9 s | 10.4 s | 2.52 GiB |
| HbSpec | 3.3 s | 5.2 s | 0.94 GiB |
| HbSpecK, HbDescEq | 3.5 s, 3.3 s | 8.3 s | 0.91 GiB |
| WitHbA | 15 s | 17.7 s | 2.07 GiB |

HbLoop2 is about 3 times HbLoop1. The cause is the kernel check of the `laddr` (omega) proof of one address expression with the constant 262144 (12.2 s, `CHECKS-HB.md` section 3).
`hb_loop2_g` (`E2eSeg/V32Hb.lean`), derived again from the general loop, makes that constant a variable, and its module is 6.2 s (`REPORT-SEG.md` section 1.1).
In comparison with SyncCommittee (ScLoop 6.3 s, WitScA 16 s), loop 1 and the witness are similar.
The 8192-iteration loop is also not unrolled. It is an induction proof, so the iteration count did not affect the time.

`maxHeartbeats` is only on `WitHbA.hb_accept_runs`. The value is 2000000.
Measurement: 200000 (log 23) and 400000 (log 26) fail in `whnf`. 1000000 (log 25) and 2000000 (logs 24, 28) pass.
Cause (profile, log 27): `simp` 11.8 s (9.5 s and 2.23 s). It is the AC sorting that closes the memory premises. This is the same cause as SyncCommittee.
There is no `maxRecDepth` setting.

## 5. Attempt record

| Obligation | Strategy count | Fact |
| --- | --- | --- |
| link | 1 | filter, conv, data, check all exit 0 |
| statements | 1 | first build exit 0 |
| size reject, lemmas | 1 | first build exit 0 |
| loop 1 | 1 | 3 compiles. A probe (log 10) found the form of the `shl` term |
| loop 2 | 2 | strategy 1: a mechanical copy of the loop 1 text (logs 14, 15). Strategy 2: the return slot value in the conclusion (logs 16, 17) |
| accept | 1 | first build exit 0 |
| specification bridge | 1 | 2 compiles. One remaining `rfl` line was deleted |
| specification pairs, `Desc` equality | 1 | first build exit 0 |
| witness | 1 | one syntax error (a name that cannot be imported), then heartbeat measurement |

Compile iterations in one strategy counted as one attempt. This is the same interpretation as the list/vector work.
No obligation reached the attempt limit.

## 6. Trust items and limits

- The contract instances are the same three as SyncCommittee. There is no new contract form and no new instance value.
- The producer `Desc` file was printed before the hand `Desc` was written. The independence is weaker than in SyncCommittee. The equality with the producer `Desc` is K.
- The objdump used the file of the list/vector work directory again. Its sha256 is the same as `build-ids.txt`. `go tool objdump` was not run again.
- The witness is one theorem for a fixed-size type. There is no variable length, so there is no split into empty, 1 and maximum.
- The three concrete inputs of the witness are `example`s. Each applies the theorem to concrete values and passes the type check.
- `lakefile.toml` only got appended items (one `input_dir`, one `lean_lib`). The root `AGENTS.md` requires approval for a lakefile change. The task instruction permitted the append.
- The gate control put one `.olean` in `.lake/build` for a short time. It was deleted after the run (the same method as the list/vector work).
- The stale check was not run. No build was killed or hit the cap.

## 7. Verification

| Check | Command | Result |
| --- | --- | --- |
| link | `hblink.py filter`, `link/conv.py --norm`, `hblink.py data`, `link/check.py` | exit 0, `PASS all` (logs 02–06) |
| build | `lake build E2eHb` | exit 0, 642 jobs (log 29) |
| `--no-build` | `lake build --no-build E2e E2eAd E2eScal E2eList E2eHb` | exit 0, `All targets up-to-date (1094 jobs)` (log 30) |
| axioms gate | `python3 -I -B ../gen/e2e/hbaxioms_gate.py run …` | exit 0, PASS, declarations 6364, hand list 476, nonstandard 0, sorryAx 0 (log 31) |
| gate control | same command, planted `E2eHb.Planted` | exit 1, FAIL, sorryAx `E2eHb.Planted.planted_sorry` (log 35) |
| prohibited words | `grep -rnE "sorry|admit|axiom |native_decide|bv_decide|maxRecDepth|maxHeartbeats" lean/E2eHb gen/e2e/hb* gen/e2e/AxiomsHb.lean` | only one measured `maxHeartbeats` line and one comment line in `WitHbA.lean` |
| home paths | `grep -rnE "Users/|/home/|lv-work"` (new files) | 0 |
| reuse measurement | `python3 -I -B gen/e2e/hbreuse.py` | exit 0 (log 37) |
| negative test | `lvnegative.py ../prysm/go1.26.10/e2e/lv/negcases-hb.json …` | exit 0, 10/10 (`CHECKS-HB.md` section 2). The specification side is `negcases-spec.json` (`REPORT-SEG.md` section 5) |
| declaration drift | `decl_dump.lean` + `decl_drift.py` | drift 0 (`decl-drift-hb.txt`, `decl-drift-seg.txt`) |
| Go differential test, hardware comparison | | not run. The host is arm64 |

`STEPS-HB.tsv` has the table of commands and exit codes. The logs are only local.

## 8. Finding candidates

- There is no new production defect candidate.
- Finding LV-1 (wrapped negative displacement) is not in the HistoricalBatch `.S` (0 `0xffff` patterns).
