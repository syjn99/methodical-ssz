# REPORT-ENC: first variable-length encoder hand proof (DataColumnsByRootIdentifier encoder work)

**Verdict: conditional.**

Conditions:

1. Runtime calls are contract hypotheses (`MemmoveC`, `GrowsliceC`). There is no refinement proof of the Go runtime machine code.
2. On the grow path, only the case with one grow at site 1 (the first-site grow path) is K. The other grow cases (the any-site grow path) are N.
3. The too-big reject is K only for the case where the first two sites do not grow.
4. The premise `guard + 8 < rsp` blocks the morestack path. This function has no write-barrier call.
5. The composition of decode then encode is N. The repo has no decoder proof for this type.
6. The Go differential test, the x86-64 execution comparison and the negative tests (mutation) were not run.
7. There is no independent review yet. All K are results of the author's build.

## 1. Target and pins

| Item | Value |
| --- | --- |
| Target | `(*v1alpha1.DataColumnsByRootIdentifier).MarshalSSZTo` (`fulu.ssz.go:1754`), 118 directives, 107 instructions |
| Type | `block_root` Bytes32, `columns` List[uint64, 128] |
| Base commit | `1b5f524` (`claude/ssz-fv-list-vector-20261112`) |
| Branch | `syjn99/ssz-fv-enc` |
| ELF sha256 | `c6403c02a110ffd6fe6d31a3c89cd395ac457b5d62e60e2e611b8ab9a8dd911e` |
| Kraken | `6064eecbb730a1152aa6ed891a155d3a92a4f298` |
| EthLib | `862185680cf23ccf54d44eb25b63b26c5020597b` |
| Lean | `4.36.0-nightly-2026-09-21` |
| Host | darwin/arm64. Heavy jobs ran one at a time with `heavy.py` (cap 40960 MB) |
| Model | Implementation `claude-opus-5-5` |

`SELECTION-ENC.md` gives the selection reasons.
`DESIGN-ENC.md` gives the design.
`STEPS-ENC.tsv` has the commands, exit codes, times and RSS. The logs are only local.

## 2. Results per obligation (K kernel-checked, X executed only, N not proved or not run)

| Obligation | Result | Kind | Theorem or file |
| --- | --- | --- | --- |
| 1 selection | `DataColumnsByRootIdentifier` | X | `SELECTION-ENC.md`, `callgraph-enc.json` |
| 1 IndexedAttestation check | `AttestationData.MarshalSSZTo` is a call. It is not inlined. Excluded | X | `callgraph-enc.json` |
| 2 link (a)–(f) | PASS all, bundle `f7cdf5e5…` | X | `link-enc/RESULT` |
| 3 design | paths, invariants, written bytes | — | `DESIGN-ENC.md` |
| 4 frozen statements | 8, committed before the proofs in `abd42d8` | — | `lean/E2eEnc/StmtEnc.lean` |
| 5 fast path, capacity sufficient | K | K | `dc_e2e_marshal_fast_main : dc_marshal_fast_stmt` (`Fast.lean`) |
| 5 fast path specification | K | K | `dc_e2e_marshal_spec : dc_marshal_spec_stmt` (`SpecM.lean`) |
| 5 first-site grow path | K | K | `dc_e2e_marshal_grow_main : dc_marshal_grow_stmt` (`Grow.lean`) |
| 5 first-site grow path specification | K | K | `dc_e2e_marshal_grow_spec : dc_marshal_grow_spec_stmt` (`SpecG.lean`) |
| 5 bytes-length reject | K | K | `dc_e2e_reject_bytes_main : dc_reject_bytes_stmt` (`Reject.lean`) |
| 5 too-big reject | K | K | `dc_e2e_reject_toobig_main : dc_reject_toobig_stmt` (`Reject.lean`) |
| 5 bytes-length reject and too-big reject specification | K | K | `dc_e2e_spec_reject_bytes`, `dc_e2e_spec_reject_toobig` (`Spec.lean`) |
| 5 specification bridge | K | K | `pdc_serialize`: `serialize prysmDcDesc g.toValue = .ok (pdcEnc g)` |
| 5 loop | K | K | `dc_iter`, `dc_exit`, `dc_loop` (`Loop.lean`), `dc_tail` (`Tail.lean`) |
| 5 any-site grow path | no statement | N | section 7 |
| 5 too-big reject, grow case | no statement | N | if the first two sites grow, the case is outside the statement |
| 6 fast path witness | n = 0, 1, 128 | K | `WitF.dcf_runs_n0`, `dcf_runs_n1`, `dcf_runs_n128` |
| 6 first-site grow path witness | n = 0, 1, 128 (len 3321, cap 3352) | K | `WitG.dcg_runs_n0`, `dcg_runs_n1`, `dcg_runs_n128` |
| 6 bytes-length reject witness | all bl ≠ 32 (examples: 0, 31, 33) | K | `WitR.RB.dcrb_runs` |
| 6 too-big reject witness | n = 129 | K | `WitR.RT.dcrt_runs` |
| 7 composition | there is no decoder accept specification | N | — |
| 8 `lake build E2eEnc` | exit 0, 636 jobs | X | log 63 |
| 8 `--no-build` all | E2e E2eAd E2eScal E2eList E2eEnc: exit 0, 1102 jobs | X | log 64 |
| 8 axioms gate | PASS, declarations 6582, theorems 5482, hand list 483, nonstandard 0, sorryAx 0 | X | `axioms-gate-enc.json` (log 65) |
| 8 gate control | FAIL with a planted `sorry` (as expected) | X | `axioms-gate-enc-plant.json` (log 59) |
| 8 prohibited-word grep | none in `E2eEnc/*.lean`. Only the comment "axiom check" in `AxiomsEnc.lean` matches | X | — |

The axioms gate is a new file `gen/e2e/encaxioms_gate.py`.
It imports the existing `axioms_gate.py` and `lvaxioms_gate.py`. It adds `E2eEnc` to ROOTS and `AxiomsEnc.lean` to the hand list.
The `.olean` of the planted control was in the build directory for a short time and was deleted immediately.

## 3. Contract instances

| Directive | Callee | Instance | Used by theorem |
| --- | --- | --- | --- |
| 23 | `runtime.growslice` (site 1) | `GrowsliceC Heap E2e.Data.e2eU8Type_addr 1 S` | first-site grow path |
| 36 | `runtime.memmove` | `MemmoveC S`, n = 32 | fast path, first-site grow path, too-big reject |
| 49, 94 | `runtime.growslice` (sites 2, 3) | same form | none. The fast path and the first-site grow path prove that it does not branch |
| 112 | `runtime.morestack_noctxt.abi0` | premise `guard + 8 < rsp` | all |

- There is no new contract form. The element size is 1. The model `rt_growslice` (esz 1) matched as is.
- The type word `type__+387072` is the same as the word of the Checkpoint encoder (`enclink.py data` checks it).
- No new data reader (`*_data_include`) was made. The statements use the existing names and labels.

## 4. Obstacle list

### 4.1 Contract forms and models

- No contract form was missing. The fast path, the first-site grow path, the bytes-length reject and the too-big reject all closed with the existing forms.
- The any-site grow path is not blocked by a contract. It is a proof design problem (section 7).

### 4.2 Kraken instructions

- There was no new instruction gap.
- `add $-0x80,%rsp` and `sub $-0x80,%rsp` were read as −128.
- `movl $0x24,-0x4(%rbx,%rax,1)` (32-bit immediate, SIB address) was read as `Int.toBytes 4 (BitVec.truncate 32 36)`.
- A 32-bit `xor` (`xor %esi,%esi` and others) makes an undefined AF. Each one needed `intro _`.
- `ecancel` failed once on a `mov ssz.X(%rip)` read. The cause was a wrongly split slice in an earlier step (logs 32–36). It is not a tool defect.

### 4.3 Loop and proof size

- When `omega` closed address and comparison facts directly in one loop iteration, the kernel load became heavy.
- Log 11: the author killed lean after 340 s. The sampled RSS max is 16.7 GiB. The result is not a pass.
- Log 12: the proof was cut and run again. 188 s, 20.4 GiB, a kernel deep-recursion error in `dc_iter`.
- Fix: the address and comparison facts moved to small lemmas outside the machine context (`dc_addr`, `dc_room`, `dc_rbx`, `dc_inc`, `dc_idx`).
- That form is the form of Go 1.26.3 `Fk/LuMarshal.lean` (`lum_addr`, `lum_room`). After the fix, the `Loop` build is 6.2 s.
- The exact terms of the heavy part were not profiled. "The omega proof terms are the cause" is an inference.
- The main theorems have no `maxHeartbeats` or `maxRecDepth` setting.

### 4.4 Witness cost

| Witness | `maxHeartbeats` | `maxRecDepth` | Measurement |
| --- | --- | --- | --- |
| three `WitF` | 4000000 | 20000 only on `dcf_runs_n128` | heartbeats: 200000, 1000000 fail, 4000000 passes (logs 40–42). recDepth: 512, 2000 fail, 20000 passes (logs 60–62) |
| three `WitG` | 4000000 | 20000 | heartbeats: 1000000 fails, 4000000 passes (logs 45, 46). recDepth: same as above |
| `WitR.RT` | 4000000 | default | 200000, 1000000 fail, 4000000 passes (logs 49–51) |
| `WitR.RB` | default | default | — |

- Profile: `simp` is 10–12 s per witness. It is the step that sorts the memory premises with `sep_comm` (the same cause as log 27 of the list/vector work).
- The `simp` of `WitR.RT` is 2.5 s. The `whnf` that uses the remaining heartbeats was not divided further.
- The cause of `maxRecDepth` was not profiled. The long constant list (`z k`) is a suspect. This is not confirmed as a fact.
- The whole-file `maxRecDepth 100000` copied from the model file was deleted after the measurement (`566c09d`).

### 4.5 Time and memory (heavy.py, n = 1, sampled RSS is an upper-bound estimate of the group sum)

| Module | Module time | Wall clock | RSS |
| --- | --- | --- | --- |
| StmtEnc | 3.4 s | 8.3 s | 1.93 GiB |
| Loop | 4.2 s | 6.2 s | 2.08 GiB |
| Tail | 6.2 s | 8.3 s | 2.28 GiB |
| Fast | 4.4 s | 6.2 s | 2.02 GiB |
| Spec, SpecM | 3.2 s, 3.4 s | 8.3 s | 0.94 GiB |
| Grow | 6.0 s | 8.3 s | 2.25 GiB |
| SpecG | 3.5 s | 5.2 s | 0.95 GiB |
| Reject | 6.9 s | 9.4 s | 2.16 GiB |
| WitF | 63 s | 91.7 s (WitF and WitG together) | 3.44 GiB |
| WitG | 90 s | same as above | 3.44 GiB |
| WitR | 20 s | 20.8 s | 2.05 GiB |

New Lean lines: Code 18, Defs 47, StmtEnc 338, Loop 203, Tail 270, Fast 92, Grow 179, Reject 310, Spec 53, SpecM 32, SpecG 36, WitF 140, WitG 185, WitR 142.
New scripts: `enclink.py` 99 lines, `encaxioms_gate.py` 38 lines, `AxiomsEnc.lean` 32 lines.

## 5. Items reused from the decoder proofs and items not reused

Reused:

- The frame of the loop proof: the `ia_iter`, `ia_exit`, `ia_loop` form of `E2eList.IaLoop` (recursion on the remaining iteration count).
- `Fk.block_split`, `E2eList.jge_false512`, `E2eScal.lea_cmp_be_false`(N = 8), `Fk.add8_neg8`.
- Specification side: `Fv1.serializeEach_u64`, `Fv1.inl_*`, `Fv1.u64Bytes_size`, the proof order of `E2eList.pia_serialize`.
- Contract models and the witness Host: `rt_memmove`, `rt_growslice`, `bumpHeap`, `Fk.WHost` (`mkHost`, `wit_split`).
- Witness models: `E2e.WitCpM`, `E2e.WitCpG`, `E2e.WitCpMR`.

Not reused:

- The decoder loop invariant is "first i items ++ 0". The encoder invariant is "first i items ++ old content". Thus `enc_split` and `enc_join` were written new.
- The head and tail segment lemmas of the decoder had no use. The encoder writes more than it reads.
- The too-big reject copied the proof text of directives 29–54 of `dc_tail`. The reason: the branch is in the middle of the tail (55).
- The decoder Data/Include reader was not necessary. The only globals of this function are label addresses.

## 6. Added trust items

- `MemmoveC` and `GrowsliceC` are hypotheses. The model proofs are only non-vacuity evidence (`CONTRACTS.md` section 3).
- The equality of the hand `Desc` (`prysmDcDesc`) and consensus-specs is a judgment. The comparison with the producer `Desc` was not done (N).
- The witness error words (`0x10e8`, `0x2b`) are substitute values. Runtime initialization sets the real values.
- Before the reject, the too-big reject path writes 36 bytes into the spare capacity of dst. The postcondition states this. It follows the Go semantics, and it was not treated as a defect candidate.

## 7. Any-site grow path: why it is blocked

- growslice can be called at site 2 or in any loop iteration. The grow count differs for each path.
- After each grow, the old block stays in the postcondition of the contract. Thus the postcondition needs an existential predicate (garbage blocks).
- The heap budget premise must also depend on the grow count. Each grow requires `2·nc + 8192`.
- The loop invariant must make the block pointer and the capacity existential variables. The one-iteration theorem gets two branches (fits, grows).
- The contract form is sufficient. The blockers are the statement design and time. This unit did not write it as a statement.

## 8. Checks not run

| Check | Status |
| --- | --- |
| Go differential test | not run |
| x86-64 hardware comparison | not run. The host is arm64 |
| negative test (mutation, `lvnegative.py` form) | not run |
| declaration drift (`decl_drift.py`) | not run. The existing files did not change, except for the lakefile append |
| producer `Desc` comparison | not run |
| stale check | run, exit 1, 518 flagged (log 66). `.lake` is an APFS clone, so the mtime of the existing outputs is older than the sources. The 22 E2eEnc outputs are AFTER (written after the flag reference). The module `E2eEnc.Loop` of the killed build (log 11) was built again in logs 13 and 14 |

## 9. Commits

`70cf11f` (selection, link), `abd42d8` (statements, design), `6f39561` (loop), `f679153` (tail), `441b9cc` (fast path), `d9d6c4f` (specification), `208254f` (first-site grow path), `26731a2` (first-site grow path specification), `38773d1` (reject), `4630633` (WitF), `d74fe38` (WitG), `8af7614` (WitR), `566c09d` (settings cleanup, gate), and the commit of this report.

## 10. Attempt count

- One attempt is one proof strategy. Error-fix builds in the same strategy counted as development steps (the same interpretation as the list/vector work).
- Loop (obligation 5): attempt 1 (`omega` in the machine context) failed in logs 11 and 12. Attempt 2 (small lemmas) passed.
- The other obligations passed at attempt 1. No obligation reached the limit (3 attempts).
- `sorry` was not used to see goals during development. Incomplete proofs were built, and the open goals were read.
