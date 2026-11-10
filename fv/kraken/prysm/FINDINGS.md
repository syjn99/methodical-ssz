# FINDINGS: cumulative ledger (generator, generated code, proofs and tools)

Stable IDs. Old items keep their IDs and discovery dates; their full text stays in `GENERATOR-FINDINGS.md` (unchanged).
Each entry: discovery checkpoint, affected pin / type / function, repro and evidence, consequence, status, independent review.

## 1. Generator defects (sszgen `698c202`)

| ID | Found | Affected | Repro / evidence | Consequence | Status | Review |
| --- | --- | --- | --- | --- | --- | --- |
| D1 | 2026-11-09, `846982c` (phase1c) | generator IR: nested container field keys | `GENERATOR-FINDINGS.md` §1 | IR key is the container name, not the field name | open (generator not changed, rule) | phase1c reviews r1–r8 |

## 2. Generated SSZ code defects

None confirmed. Candidate C-1 is in §5.

## 3. Proof, checker and tooling defects

| ID | Found | Affected | Repro / evidence | Consequence | Status | Review |
| --- | --- | --- | --- | --- | --- | --- |
| K1 | 2026-11-09 (phase1c) | Kraken runtime parser: `%riz` index | `GENERATOR-FINDINGS.md` §4 | 13 generated functions did not parse | normalised by `link/conv.py --norm` (`f17f9c8`) | phase1c r8 |
| K2 | 2026-11-09 (phase1c) | Kraken parser: `bsr` | `GENERATOR-FINDINGS.md` §4 | `ssz.ValidateBitlist` not included | open (Kraken request) | phase1c r8 |
| T-1 | 2026-11-10, run fve2e, before `fd8a561` | Lean closing tactics on register goals with symbolic BitVec (`trivial`/`rfl` inside `first`) | prysm-e2e jobs 27, 28, 33, 34 (memcap kill at 6 GiB per process, oom_kill 5 → 5); probes 34, 35, 37 isolate the final register goals | one Lean process above 6 GiB; build killed | fixed: decoder proof split at `L_b4` (`cp_e2e_accept_tail`), closing by `exact trivial` / `with_reducible rfl` / `toBitVec_inj` + `eaddr` | pending (Fable review of this run) |
| T-2 | 2026-11-10, run fve2e, before `fd8a561` | `ecancel` final AC step | job 44: all 26 chunks match textually but `ecancel` fails; job 43 shows two atoms sorted differently (same print, different elaboration) | composition of `cp_e2e_accept_main` with its tail failed | worked around: `rw [show a = a from rfl] at Hm2` re-elaborates the two atoms (log 45) | pending |
| T-3 | 2026-11-10, run fve2e, `61eec5e` | `Fk/Include.lean` keeps the data reader private to its module | `lean/E2e/Include.lean` | a second data directory needs a copy of the reader | copy with a textual check (`gen/e2e/check_include.py`: SAME ×4) | pending |
| T-4 | 2026-11-10, run fve2e, before `fd8a561` | `kaddr` (Fk.Step) does not reduce `Width.W64.bits` | job 21 (omega atoms `2 ^ Width.W64.bits`) | address goals after a callee return fail | local macro `eaddr` (E2e.CpAccept) with `Width.bits` | pending |
| T-5 | 2026-11-10, run fve2e, INBOX 004 (`ca14ba6`) | `ecancel` bounded unfolding on `uintBytes` of a symbolic epoch (`E2e.CpSpecM`) | jobs 84, 85 (Lean heartbeat timeout in `ecancel`) | `cp_e2e_marshal_spec_k` did not close | worked around: `generalize` of the epoch byte list (`CpSpecM.lean:68-69`, job 86) | e2e-r2: workaround present, cause not verified |
| T-6 | 2026-11-10, run fve2e session 3, before `fc40cb4` | a Lean file that imports two witness modules (two `Host` instances: `E2e.WitCpA.host`, `E2e.WitCpM.host`) | jobs 147 (max recursion), 148, 149 (heartbeat timeout at the declaration) | the implicit instance of `rt_memmove` resolves to the other host; unification unfolds both programs | worked around: one witness host per file (`WitCpSpecs`, `WitCpMS`, job 150) | pending |
| T-7 | 2026-11-10, run fve2e session 4 (INBOX 009), before the session-4 encoder commit | contract form `GrowsliceC` (`Fk/Contracts.lean`): its result gives the remaining heap only as `avail' + esz·newCap ≤ avail` (an upper bound) | job 184: `cpw_tail_grow` after `cpw_head_grow` needs `2·nextSliceCap (len + 40) C1 + 8192 ≤ av1`; omega counterexample `av1 = 0` | only the **budget premise of the second growslice call** (a lower bound on the heap that the first call left) is not derivable; with that fact the existing lemma `cpw_tail_grow` gives the return (review e2e-r3 S7). Session 5 (INBOX 010 M1): `cp_e2e_marshal_grow_any_sharp` (same premises, existing forms) proves: return when the first block holds the root; return through the second growslice when `2·nextSliceCap (len+40) C1 + 8192 ≤ av1`; otherwise the entry of the second call with `Heap av1` and `av1 < 2·nextSliceCap (len+40) C1 + 8192`. Only that last state is not continued | blocked for the residual state only; not a code defect; controller decision (INBOX 010): no new contract form; the residual (no lower bound on the remaining heap) is **blocked / differential only** pending a user decision (a lower bound on the remaining heap would be a new form) | e2e-r3: obstruction genuine for an unconditional return; statement sharpened (M1) |
| T-8 | 2026-11-10, run fve2e session 4 | `ecancel` with a frame mvar instantiated to `… ⋆ emp`, and AC normal forms of witness memory | jobs 184–187 (type mismatch only in a trailing `⋆ emp`), 192–197 (same atoms, different AC order until the `uintBytes`/root lists were generalized) | proofs did not close | worked around: `simp only [sep_assoc, sep_emp]` + AC sort + `exact`; `generalize` of the symbolic byte lists before AC sorting (as T-5) | pending |
| R-1 | review e2e-r1 at `9bad532` (M1) | `E2e.cp_e2e_unmarshal_then_marshal`, REPORT §11 E5 row | the theorem starts at the encoder entry, runs no decoder code and does not use `cp_e2e_accept_main`; no single witness host | E5 (compose_hupd, compose_witness) was reported as done | fixed: renamed `cp_e2e_marshal_decoded_receiver` (`fcb4f7e`); the real composition `E2e.cp_e2e_unmarshal_then_marshal` (`E2e/CpCompose.lean`, decoder entry → `cp_e2e_accept_main` → hupd → `cp_e2e_marshal_main`) with the one-Host witness `E2e.WitCpC.cp_compose_runs` and 11 negatives (`cpx-*`, logs 104–110) | found by review; **closed** by review e2e-r2 at `9e7d2f9` (APPROVE; closure and one-Host witness checked by program). The 4 composition code mutants were later removed as rename-only (e2e-r2 N2) |

## 4. Known issues (not defects)

| ID | Found | Affected | Evidence | Note | Status |
| --- | --- | --- | --- | --- | --- |
| O1 | 2026-11-09 (phase1c) | generator log | `GENERATOR-FINDINGS.md` §1 observations | empty package name in a log line | unchanged |
| O2 | 2026-11-09 (phase1c) | Prysm hand-written `primitives` SSZ methods | `GENERATOR-FINDINGS.md` §1 observations | not generated; need their own proofs | `(*Epoch).UnmarshalSSZ` accept path proved as function spec `EpUAccC` (`37fdcf9`), length reject proved (`e5b68c9`); the other 23 methods not |
| N-1 | 2026-11-10, run fve2e, `e10b146` | `Checkpoint.UnmarshalSSZ` → `fmt.Errorf("Epoch: %w")` | `cp_e2e_epoch_err_unreachable` | unreachable with `len = 40` (unreachable_mc column, not reject coverage) | proved |
| N-2 | 2026-11-10, run fve2e, `61eec5e` | `Checkpoint.MarshalSSZTo` → `fmt.Errorf("Epoch: %w")` | `CALLGRAPH.md`, `-m=2` log | removed by the compiler (inlined `Epoch.MarshalSSZTo` cannot fail) | recorded |
| N-3 | 2026-11-10, run fve2e session 3, `3bb3819` | `AttestationData.UnmarshalSSZ` (`phase0.ssz.go:301,307`) | `ad/CALLGRAPH.md`, decoder `.S` (`newobject` then store, no nil test) | the decoder always allocates a new `Source` and `Target` (`new(Checkpoint)`), also when the receiver already has them; same as the Go source; stated by `E2eAd.ad_e2e_accept_main` (session 4: one theorem for every receiver, old words `aS`/`aT` arbitrary, conclusion has the fresh pointers and the full 72-byte objects; witness `WitAdA` with nil and non-nil old words) | known behaviour, not a spec violation; proved |
| C-2 | 2026-11-10, run fve2e session 3, `3bb3819` | `AttestationData.MarshalSSZTo` (`phase0.ssz.go:254-256, 262-264`) | encoder `.S` (`cmpq $0x0,0x30(%rdx)`; `newobject`; store to the receiver) | the encoder writes the receiver: a nil `Source`/`Target` is replaced by `new(Checkpoint)` before it is encoded (zero Checkpoint, Root nil → the callee returns ErrBytesLength wrapped "Source: %w"); A4 must state this side effect | known behaviour, not a spec violation |
| G-2 | 2026-11-09 (pin smoke, before phase1c) | Prysm `consensus-types/blocks` error-text tests (`TestMarshalPartsMetadata/available_too_large`, `/requests_too_large`, `TestPartialDataColumn_PartsMetadata/marshal_error_due_max_bitlist_size`) | `GENERATOR-FINDINGS.md` §2 | generator change `280b752` checks the Bitlist by bits (`ssz.ValidateBitlist(x, 4096)`); too large input still rejected, only the error text differs from the test | reference row (review e2e-r1 S9); compatibility issue, not a generator defect; unchanged |
| G-3 | 2026-11-09 (pin smoke, before phase1c) | `-tags minimal`: `consensus-types/blocks` test build, `encoding/ssz/detect` `TestByState` | `GENERATOR-FINDINGS.md` §3 | fails on the committed baseline too; unrelated to generated code | reference row (review e2e-r1 S9); baseline failure; unchanged |

## 5. Unconfirmed candidates

| ID | Found | Affected | Repro / evidence | Consequence | Status | Review |
| --- | --- | --- | --- | --- | --- | --- |
| C-1 | 2026-11-10, run fve2e (orchestrator observation, PROOF-PLAN §1; confirmed in the code `5a3ca92`) | `(*v1alpha1.Checkpoint).MarshalSSZTo`, Go 1.26.10 ELF | `.S` directive 35 stores the 8 epoch bytes at `dst[len:len+8]` before directives 37–38 test `len(Root) = 32`; Go source order (`phase0.ssz.go:1963` before `1967`); differential cases `enc-rootlen0/31/33` return `(nil, ssz.ErrBytesLength)` | on the error return the caller's backing array beyond `len(dst)` holds 8 new bytes (when `cap ≥ len + 8`); `dst` itself is not returned; no SSZ rule covers an invalid Go value | confirmed as machine behaviour and stated exactly by `cp_e2e_marshal_reject_main` (after `9bad532`): with `cap ≥ len + 8`, `dst[len:len+8]` = epoch bytes, rest of `dst` unchanged, result `(nil, ErrBytesLength)`; statement mutant "dst unchanged" fails (negative `cpmr-stmt-dst-unchanged`). Classified: known behaviour, not a spec violation (SSZ has no rule for a Go value with `len(Root) ≠ 32`); not a generator defect | pending |

## 6. False positives

| ID | Found | Claim | Resolution |
| --- | --- | --- | --- |
| FP-1 | 2026-11-10, run fve2e (PROOF-PLAN §1) | Go 1.26.10 changed `growslice` | the `slice.go` hunk is in `moveSliceNoCap`; `growslice`, `nextslicecap` are byte-identical (`go1.26.10/e2e/runtime-diff.json`); orchestrator erratum (INBOX 002) |

## 7. Historical index (F1, F2, G1–G3, H1)

Index only (no new finding, no fix in this commit). Stable IDs of the sszgen work before run fve2e. Source:
`/workspace/agent-runs/methodical-fv-milestone-scalability/milestone/FINDINGS-INDEX.md` (controller, MS1); every commit
below resolves in this repository. **Namespace:** historical `G2`/`G3` (no hyphen) are not the ledger rows `G-2`/`G-3`.

| ID | Kind | Commit | What | Status |
| --- | --- | --- | --- | --- |
| F1 | behaviour-defect fix (generated code and runtime) | `f0b85c7d5dcf56a54a0507eb6a0849e1f54e101a` | a Bitvector with nonzero padding bits was accepted; now rejected | fixed; found by an FV counterexample (commit body) |
| F2 | behaviour-defect fix (generated code) | `280b7523805233cdb96a58a7f50677637309b4c6` | the Bitlist encoder checked the length in bytes; now in bits | fixed; found by an FV counterexample (commit body) |
| G1 | compile fix (generator template) | `ab0fb00e3f7c1f6272d428d6331541eb133f53cf` (mapping presumed: by elimination only) | the `[N]T` array-field decoder emitted a `make` that does not compile | fixed; ID mapping not confirmed |
| G2 | documentation and test — **not a bug fix** | `e9cbf5c3a6748ce2d17a5b0dad454d39ed1021f2` | on a `MarshalSSZTo` error, `dst[:len]` is unchanged (more than "unspecified") | documented |
| G3 | dead-code removal — **not a bug fix** (the commit subject says "fix") | `b51620a2ab5b55a706f16d56841d8a2c1508bbde` | the unreachable first-offset `ErrOffset` branch is removed | removed |
| H1 | test and comment — **not a defect** | `b03a45d69c7229c74af0fb09fbded3ba46e05c82` | the in-place `gohashtree.Hash` aliasing premise is pinned by a test | tested |
| (none) | behaviour fix found by code review, not by FV | `60d4d3b366919cb5b991d311a8a19bfa96b3eeb4` | `ValidateBitvector` uint64 overflow panic (introduced by the F1 fix) | fixed |

Only F1 and F2 are behaviour-defect fixes found by FV. `698c2025a73a296b55b95744a8408f3b03b2546b` is a comment-only follow-up
and the generator pin; it is not the fix commit of any ID. The G2, G3, H1 and `60d4d3b` rows come from the commit bodies
(controller's `HISTORICAL-FIXES.md`); this session did not re-read their diffs line by line.

## 8. Policy audit of `4a5e0b9` (AU-01 … AU-17)

Source: the controller's audit report and `audit.json` (3 Opus agents + controller, run dir outside the repository).
Historical IDs above are unchanged. Audit verdict: bounded pass with findings; no false or weakened proof found.
"Fixed" below means a commit in `cc61ebc..a372145` on this branch, reviewed by fix-r1 (REQUEST_CHANGES, narrow), or a later commit named in the row (not reviewed yet).

| ID | Sev | Finding (short) | State |
| --- | --- | --- | --- |
| AU-01 | high | gate lock is not FIFO | user decision: gate not replaced, measure first (controller's task); rule kept: ≥ 2 s pause between own gated jobs |
| AU-02 | medium | whole negative suites ran as one gated job | rule adopted: one gated job per case or small batch (jobs 251–253, 258–259, 288–291) |
| AU-03 | medium | per-case timeout killed only memcap.py | fixed `cc61ebc` (tree kill + survivor assertion, fake-child test) |
| AU-04 | medium | unknown-identifier first error counted as pass | fixed `e9e8565` (class `wrong_target`), `6951eb8` (3 mutants re-expressed as type-weakening; all inside); gap NF-1 fixed `23eceac` |
| AU-05 | medium | trace-stale E2eAd modules; `lake env lean` has no trace check | fixed `875368f` (precheck in drivers; jobs 248 exit 3, 249 rebuild, 250 exit 0) |
| AU-06 | medium | wit_split side-goal omega dominates WitCpW/WitCpWR | fixed `301300f` (E2e-side `wit_split_n`; 4 modules 1636.8 s → 165.3 s, n = 1; drift 0 with allowlisted auxiliaries) |
| AU-07 | medium | P2EncCp omega side goal (audit: 720 s of a 732 s build) | open: 3 attempts (953–973 s omega), no speed-up against the same-method unchanged-file run 986.0 s (NF-5); the slow omega is not the `hfit` goal (lines 164–165) and was not located; file unchanged (`opt1/AU-07.json`) |
| AU-08 | medium | p2dec statement had no same-statement check | `4581b8f` checked only the text after the colon (NF-2); full statement checked by the `_kind` identity, `094e51e` |
| AU-09 | medium | hold-out limits (C-03, C-04) | user decision: H1 kept with limited claims (`SizeSSZ` excluded), H2 = Eth1Data `UnmarshalSSZ` / `MarshalSSZTo` only; recorded in `HOLDOUT-MARKER.json`; nothing opened |
| AU-10 | low | axioms gate checked a hand list only | fixed `fcead74` (all declarations by program: 2705 at job 254, 2726 in 79 modules at job 293; `sorry` control fails) |
| AU-11 | low | `⋆ True` remainders not all disclosed | fixed `6308c64` (REPORT §11 column "나머지") |
| AU-12 | low | witness wording (corollary, `*_spec_here`) | fixed `6308c64` |
| AU-13 | low | README module count 14 (true: 11) | fixed `1a99ef9` |
| AU-14 | low | policy tool limits (decl_dump roots, stale_olean) | deferred (policy repository; no push authorized) |
| AU-15 | low | many tactic-limit overrides; heartbeat-timeout runs | rule adopted for new work (small `maxHeartbeats`, raise only with a profiled cause) |
| AU-16 | low | cost records not bounded; proof_lines +1 per file | fixed `cfb7613` |
| AU-17 | info | stale docstrings, nm file hash, Go tests not in the gate, other minor items | docstrings `a497f54`, nm hash + Go tests `151c99c`; other items recorded in the audit, not changed |


## 9. Independent review fix-r1 of `a372145` (NF-1 … NF-5)

Review verdict: REQUEST_CHANGES (narrow); no proof problem, no drift on named declarations.
Section 8 IDs are unchanged. "Fixed" below means a commit after `a372145`, not reviewed yet.

| ID | Sev | Finding (short) | State |
| --- | --- | --- | --- |
| NF-1 | must-fix (M1) | `negative.py`: first error `unknown tactic`, `unknown namespace`, `Invalid field … environment does not contain` counted as `inside` | fixed `23eceac` (patterns enumerated from the toolchain's error strings; selftest with 15 new fixtures fails on 12 of them with the old pattern; reclassification delta 0). The list is not complete: two escapes found by review fix-r2, see NF-6 |
| NF-2 | must-fix (M2) | p2dec statement check covered only the text after the colon; a hypothesis added before it compiled | fixed `094e51e` (`_kind` identity on the whole declared type against the hand kind `rootDecSegKind`; 5 added-binder cases fail only in the `_kind` line) |
| NF-3 | should-fix (S1) | p1 statement unchecked without a hand theorem | fixed `094e51e` (`u64DecAcceptKind`; anchored to the two hand theorems; no hand theorem needed for a new instance) |
| NF-4 | should-fix (S2) | a wrong conclusion literal ran into the 300 s wall limit | fixed `094e51e` (`with_reducible exact`: `scal-gad-stmt-literal` fails inside in 1.4 s) |
| NF-5 | should-fix (S6) | AU-07 compared with 732 s from another run | `opt1/AU-07.json` has the same-method baseline 986.0 s (reviewer, n = 1) |

Also fixed: S7 (`negative.py` with an unknown case id exits 2, `23eceac`), S3 (counts by command), S4 (paths and run
names in the files of this range; older generated records listed in `TOOLS.md` "Known deviations"), S5 (marker text).

## 10. Independent review fix-r2 of `56dfc27` (NF-6 … NF-8)

Review verdict: APPROVE, hold-out ready with conditions. Section 9 IDs are unchanged.
These items were handled by the evaluation session BEFORE the hold-out was opened (step 0 of the S3 order).

| ID | Sev | Finding (short) | State |
| --- | --- | --- | --- |
| NF-6 | should-fix (N1) | `negative.py`: first errors ``Unknown option `o` `` and ``Case tag `t` not found`` classified `inside` (a pass) | fixed (step 0): both forms are `wrong_target`; 3 selftest fixtures fail with the old pattern; reclassification delta 0 (154/154, 28/28). The `WRONG_TARGET` list is still not complete: an unlisted parse or name form classifies `inside`, so the first error of every row is read |
| NF-7 | should-fix (N2) | the `_kind` line is generator output; nothing checked its right-hand side by program (a degenerate line compiles) | reader-side check `gen/scal/kindcheck.py` (step 0), see its README limits |
| NF-8 | should-fix (N3) | no `stale_olean.py` run after failed builds; known-deviation list incomplete; one hand-typed OUTBOX time | (a) correction (review s4-r1 S1): in session 9 `stale_olean.py` ran twice for four failed builds (314, 317, 318, 321), each time after the passing build, and not after 321. No effect on the result: later `--no-build` prechecks passed and the reviewer's cold rebuild is independent of those artifacts. From session 10 on, `lake build --no-build` or `stale_olean.py` runs right after every failed build; (b), (c) recorded, not changed |

## 11. Independent review s4-r1 of `8734a1e` (NF-9 … NF-12)

Review verdict: APPROVE (hold-out H1 decoders), 0 must-fix. Should-fix S1–S6 are wording fixes (NF-8 corrected above, README, marker, CONTAMINATION §4, `BhSpecChecker.lean` header path). New findings of the review:

| ID | Sev | Finding (short) | State |
| --- | --- | --- | --- |
| NF-9 | note | `kindcheck.py` passes a wrong kind parameter (Lean rejects it in the `_kind` line), and Lean passes a degenerate kind line (`kindcheck.py` rejects it). Neither check alone is enough | recorded; both are run together on every generated file (README "Limit of `t_kind`") |
| NF-10 | note | the hand `prysmBhDesc` was written after the checker Desc had been printed in the same session: independent of the code under test in content, not in time | recorded; limit stated next to the codec-equality theorems in `RESULT.json` |
| NF-11 | low | `bh_e2e_accept_main` hides the three argument-area slots in one 24-byte existential (`spl`); the AttestationData theorem names two of the three values. Dead stack only | recorded, statement not changed |
| NF-12 | low | no negative case targeted `bh_e2e_reject_size_spec` or the two codec-equality theorems | cases added in session 10 (`negcases-holdout.json`), one gated job each |

## Checkpoint deltas

(T-5 has its row in section 3 since session 3, review e2e-r2 N7.)

- 2026-11-10 `02b0e89` (prysm-e2e E6): new T-1, T-2, T-3, T-4, N-1, N-2, C-1, FP-1; O2 updated (Epoch decoder accept proved). No new generator defect.
- 2026-11-10 `507da34`+ (INBOX 004): C-1 confirmed and stated by `cp_e2e_marshal_reject_main` (classified known behaviour); O2 updated (Epoch reject proved). New tooling note T-5: `ecancel` bounded unfolding times out on `uintBytes` of a symbolic epoch (job 84/85); worked around by `generalize` (job 86). No new generator or generated-code defect.
- 2026-11-10 session 2 (M1 fix): R-1 fixed by the real machine composition and its witness (pending re-review). No new generator or generated-code defect.
- 2026-11-10 session 2 (grow path): `cp_e2e_marshal_grow_main` proved (first growslice site). Tooling note, not a defect: `simp` turns `{ toBitVec := x.toBitVec + 8 }.toNat` into `(x.toNat + UInt64.toNat 8) % 2^64` with an unreduced literal, and a general `rw [cpg_w]` unifies by structure eta with the wrong subterm; worked around by explicit lemmas `cpg_n8`, `cpg_w rdi`, `cpg_e8` (logs 111–115). No new generator or generated-code defect.
- 2026-11-10 session 2 (review e2e-r1 S-items): S2 kept as the explicit note (N-1 is a local lemma joined with `ep_uacc_holds` in the text, not in one theorem); S8 makes C-1 observable in the Go differential (backing bytes LE(epoch) after ErrBytesLength); full negative suite 73/73 with the S7 limit (job 125, no timeout). No new defect.
- 2026-11-10 session 3 (review e2e-r2 N1–N7): R-1 closed by e2e-r2; T-5 row added to section 3; negative harness classes `timeout_heartbeat`, `timeout_wall`, `recursion_limit` (never a pass): the two heartbeat-timeout mutants of 9e7d2f9 (`cpmr-stmt-dst-unchanged`, `cpg-stmt-e8off`) were counted as "fails inside" before; now replaced. No new generator or generated-code defect.
- 2026-11-10 session 3 (A1, A2): new N-3 (AttestationData decoder always allocates Source/Target), C-2 (AttestationData encoder replaces a nil Source/Target in the receiver), tooling T-6 (two Host instances in one file). The ELF Checkpoint abi.Type (reached from `newobject`) has Size_ 72 = the IR size. No new generator or generated-code defect.
- 2026-11-10 session 4 (A3): N-3 stated and proved by `ad_e2e_accept_main` (four segment lemmas, peak 1.98 GiB, no memcap kill: the T-1 split was applied from the start). T-2 recurred at the Slot/CommitteeIndex callee saved-rbp word (job 155: the callee post carries the word with a width term that prints as `BitVec.toInt (rsp - 8#64)`; `ecancel` does not match the source-written `(rsp - 8#64).toInt`); the same workaround (`rw [show a = a from rfl] at H`, job 156). Witness runtime model `E2eAd.bump_newobject72` (72-byte object, text of `Fk.bump_newobject32`). No new generator or generated-code defect.
- 2026-11-10 session 4 (INBOX 009, Checkpoint encoder): `cp_e2e_marshal_grow2_main` (first fits, second grows), `cp_e2e_marshal_grow_any_main` (first grows, every cap < len + 8: returns, or reaches the second growslice call), `cp_e2e_marshal_reject_grow_main` (reject after the first growslice; C-1 form on the new block; caller array unchanged, also in the differential), covers `cp_e2e_marshal_cover` / `cp_e2e_marshal_reject_cover`. New T-7 (blocked: `GrowsliceC` does not chain two calls) and T-8 (tooling). C-1 extended: after a growth the epoch bytes are in the new block only. No new generator or generated-code defect.
- 2026-11-10 session 5 (INBOX 010 M1): `cp_e2e_marshal_grow_any_sharp` (three exact disjuncts: return through the first block, return through the second growslice, or the second call's entry with the remaining heap below its budget). T-7 narrowed to the budget premise of the second call (S7); residual blocked / differential only pending a user decision. No new contract form, no new defect.
- 2026-11-10 session 5 (INBOX 010 M2, S1–S7, items 4–5): framed covers `cp_e2e_marshal_cover_framed` / `cp_e2e_marshal_reject_cover_framed` (no `⋆ True`; reject: `blk = dst` when len + 8 ≤ cap, else the caller's array unchanged); Go-value theorems for the cover witnesses (`rl ≤ 48` is the Go-value range); stale records fixed (S3–S6); historical index (section 7); S0 baseline. C-1 unchanged (stated per range in the framed covers). T-7 residual unchanged (blocked / differential only, user decision). C-2 unchanged (A4 not started). No new ID.
- 2026-11-10 session 6 (INBOX 011, scalability S1–S2, development set only): parameterized segment lemmas `E2eScal.u64dec_accept` (P1), `rootdec_seg` / `rootenc_seg` (P2 decode / encode, fits case); in-sample re-derivations with the hand statements (`sl_same_stmt`, `ad_root_same_stmt`, `cp_marshal_same_stmt`: `rfl`); generator `gen/scal/scalgen.py` (raw outputs `GenCi`, `GenAdDec`, `GenCpDec` build unedited; `ci_unmarshal_accept_main_g_same`). No new generated-code or generator (sszgen) defect. Tooling notes, not defects: (a) a Lean structure instance whose fields continue on a less indented line does not parse (`{ base := …,⏎ disp := … }`; the error recovery silently drops `disp`, and the template then reads displacement 0 — the next errors are far away, job 216); templates use `AddrExpr.mk` (job 217). (b) `cp_e2e_marshal_main_s` (the hand proof with directives 36–62 replaced by one lemma application) exceeds the hand theorem's 16 M heartbeats (job 235) and builds in about 730 s, longer than the 300 s negative-case limit: `maxHeartbeats` 64 M for that theorem; its code negatives run on the separate placement theorem `cp_enc_tmpl_at`. (c) Generator G1 (development, before any hold-out input): doc comment emitted before `set_option … in` (jobs 229/230), fixed. The hold-out sources were not opened (`scal/HOLDOUT-MARKER.json`).
- 2026-11-10 `cc61ebc..deeef13` (FIX-1): new section 8 with AU-01 … AU-17 (policy audit of `4a5e0b9`). No new generator or generated-code defect. Negative suite 154/154 again after the AU-04 re-expression (the 3 cases were not passed between the reclassification and the rerun). Scal negatives 20/20.
- 2026-11-10 `301300f..a372145` (OPT-1): AU-06 fixed (`301300f`). AU-07 stays open: the audit attribution of the 720 s omega to the `hfit` side goal is not confirmed (a standalone lemma for it left one omega at 968 s); the call was not located within 3 attempts.
- 2026-11-10 `23eceac..` (review fix-r1): new section 9 (NF-1 … NF-5). No new generator (`sszgen/`) or generated-code defect. The NF items are tooling and statement-check gaps; no committed negative result changed class.
- 2026-11-10 evaluation session (S3 hold-out H1, after `scal/HOLDOUT-OPENED`): NF-6 … NF-8 (section 10) handled before opening. Proved: the ValidatorIndex decoder accept path; the BeaconBlockHeader decoder accept path, size reject and spec alignment (wording corrected by review s4-r1 S4; was "decoders proved"). Not proved at that checkpoint: the two `fmt.Errorf` wrap sites of the BeaconBlockHeader decoder as `unreachable_mc` theorems, the ValidatorIndex length reject, the BeaconBlockHeader encoder, a Lean Go-value predicate for the BeaconBlockHeader receiver. The raw generator outputs built unedited. No new generator (`sszgen/`) or generated-code defect. Compiler variation seen (not a defect): the BeaconBlockHeader decoder spills rdi before rbx (directives 12/13), AttestationData spills rbx first; the third root segment of BeaconBlockHeader uses rsi/rcx in its write-barrier block (outside the template). The decode template covered all three root segments unedited.
