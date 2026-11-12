# HISTORY: Kraken x64 session history

There is one paragraph per session. The times are IST commit times. They are agent time, not human time.
The old reports (`REPORT-1b*.md`) and the review evidence (logs, json, mutation copies) are in the git history.
The review evidence is in commits `28ea489` (re-proof fix) and `0ef30e3` (re-proof fix 2). The evidence of earlier sessions is in each review commit.
The review texts were in `review/*.md`. That directory was removed on 2026-11-12 (section 13). Tag `archive/fv-before-workflow` holds it.

## 1. Evaluation (2026-11-04 21:30 – 11-05 00:40)

Commits `c60e0d2..1f95206`, review `8f3faff`.
We evaluated whether we can use Kraken x64 (main `6064eec`) instead of MiniRV.
K0: on Lean 4.35.0, the Kraken parser does not build. On nightly-2026-09-21, Kraken and the EthLib SSZ closure build (332 s).
K1: `link/conv.py` changes objdump output into labeled assembly. 9 functions pass the runtime parser.
K2–K4: we proved Scalars reject, accept, size and encoder, and the ListU64 loop and accept path. 57 theorems.
`kstep` ended with a `grind` timeout in a large context. So we made 439 lines of step lemmas and macros (`Step`, `Labels`, `Flags`, `Block`, `Bytes`).
Cost: Scalars reject 24 minutes, ListU64 accept 61 minutes. The same work took about 4 hours in 1a MiniRV (includes the learning effect). Fk build 19.7 s.
The verdict was "conditionally possible".
astra review: `lu_accept_main` is vacuous (the contract `hms` is quantified over all `cnt` and frames, so the premise is contradictory). ValidateBitlist has `bsr`, which Kraken does not know.
We could not do the K5 hardware comparison because Docker did not respond.

## 2. 1b (2026-11-05 06:13 – 13:44)

Commits `8f3faff..4e37f2e`, review `9ff7c73`.
We increased the targets to 9 types: BitVec, Nested, ListC, BitL, Prysm v7.1.8 reduced Checkpoint·AttestationData.
We made size, encoder fast path, decoder accept and reject, and EthLib round-trip theorems. 597 theorems.
We changed `MakesliceC` to the heap fragment form and proved `lu_accept_main` again. Witness `lu_accept_runs` (n = 0, 1, 16).
We made the link check `link/check.py` (27 functions, 2751 instructions).
Findings F1 (BitVec accepts padding bits), F2 (BitL encoder counts bytes). `semtest/f12_test.go` reproduced them.
B0: we evaluated the vcgen branch and decided to stay on main (`vcgen/B0.md`).
The self-assessment was "gate 1 conditionally passed".
The astra review rejected it: `GrowsliceC` was contradictory, so the three BitL accepts were vacuous. `fmt.errorf` without arguments returns nil, so the ListC reject contract was wrong. The link check passed instructions whose meaning changed.

## 3. 1b-fix (2026-11-05 14:42 – 17:59)

Commits `32c0bdc..694f129`, review `f452384`.
We put input ranges and a budget into `GrowsliceC` and proved the model `rt_growslice`.
We divided fmt into `FmtErrorfNilC` (0 arguments, rax = 0) and contracts with arguments.
We added (f) SHash and (g) format constants to the link check.
We made premise witnesses for 10 main theorems and 1 contract call.
We fixed the field offsets of the B0 specification and measured again.
Numbers: 704 jobs, AXIOMS 754, self-tests 9, negative tests 7.
The self-assessment was "conditional, gate 1 not passed".
astra review: the B0 spill coordinates were wrong (`rsp + 8` before the call, not `rsp + 16`). The SHash check has a new bypass. There is no non-vacuity of the full premise and no composable postcondition.

## 4. Re-proof (2026-11-05 23:01 – 11-06 01:28)

Commits `2d0150b..440e079`, review `df024af`.
We proved again on top of `2d0150b`, which merged the generator fix `698c202` (F1, F2, G1–G3, H1: two behaviour fixes, a compile fix, a documented error contract, a dead-branch removal and an aliasing test). New ELF `9c850c97…c501`.
F1·F2 became reject theorems. `ssz.ValidateBitvector` became a machine-code theorem, not a contract.
The first offset `> size` branch that G3 deleted was also not in the old ELF. There was no machine-code theorem to delete.
Numbers: 804 jobs, AXIOMS 1296/6648, self-tests 10. Direct witnesses for 48 of the 53 main theorems.
astra review: two link check bypasses, witnesses that differ from the real Go state, a failing Go regression test. 7 required fixes.

## 5. Re-proof fix (2026-11-06 02:09 – 03:25)

Commits `df024af..813a86a`, review `28ea489`.
We made witnesses for the four remaining main theorems and `lum_grow_site`. All 53 main theorems have witnesses.
We made `goval.py` (Go value check). We moved the `%w` calls to `FmtErrorfWC`. We deleted the unrestricted `FmtErrorfC`.
`joint_models` satisfies 10 contracts on one Host and one heap.
We put label invariants into B0 and measured again: VC 20, closed 3, open 17.
Numbers: 830 jobs, AXIOMS 1432/7334, self-tests 14, negative tests 14, witness files 69, goval violations 0.
The self-assessment was "gate 1 conditionally passed".
The astra review rejected it: comments inside strings break the SHash check. Suffix expressions and spaces break the format constant check. The Go object of Scalars is 24 bytes, not 16. fmt contract scope, rodata messages, ListC inner lists, postconditions, gate table. 8 required fixes.

## 6. Re-proof fix 2 (2026-11-06 06:51 – 08:33)

Commits `28ea489..7152188`, review `0ef30e3`.
We completed 6 of the 8 required fixes. #7 (postconditions) is partial.
We changed (f) to a comparison with the generated source text, and (g) to role classification and a Go parser (`golits.go`). We added the (h) runtime data check.
`layout.go` writes the gc amd64 layout to `layout.json`. goval looks at size, alignment, padding, bool and overlap.
We divided fmt into `FmtErrorfWC` (`%w`) and `FmtErrorfDWC` (`%d %w`). We put the box content into `ConvT64C`. We put the ValidateBitlist messages in rodata (`vblRO`).
New reject theorems: `sc_reject_bool_main`, `bl_reject_invalid_main`. 6 ListC non-empty element witnesses. Composition witnesses WitLuComp, WitScComp.
We did not do the ListC element offset order reject.
Numbers: 856 jobs, AXIOMS 1583/8028, self-tests 24, negative tests 16, witness files 79, goval 79/0/2.
astra review: role classification cannot tell Host binders from name shadowing. (h) accepts suffix expressions and other pointer types. The Go parser treats a local `fmt` as the standard package. The error witnesses are not valid Go error interfaces. The size theorem classification was wrong (seven are memory identity). We retracted "full type complete" for Scalars and ListU64. 8 required fixes.
After that, `DIRECTION.md` (`3548e9d`) decided to replace (f)(g)(h) with Lake `input_file` and ELF data include.

## 7. Cleanup (2026-11-06 09:30 – 19:58)

Commits `3548e9d..` (branch `syjn99/ssz-fv-cleanup`).
We reduced code, comments, reports and artifacts. We did not change the statements of main theorems, witnesses and contracts, the target Go code, the ELF, the `.S`·objdump·nm of link/out, the negative tests or the self-tests.

- We merged six reports into `REPORT.md` (current state) and this file. We deleted `COST.md` (the evaluation session cost is in section 1). We applied the section 8 correction of astra fix 2 to the gate table.
- `review/`: we deleted 68 logs, json, txt and mutation copies. We deleted regression blocks that do not build with the current signatures, and three files (`Review1b.lean`, `ReviewB0CountAstra.lean`, `ReviewFixB0CountAstra.lean`). The 11 remaining Lean files ran without errors.
- Artifacts: we deleted 30 `link/out/raw/*.S` (check.py does not read them), 9 vcgen logs, `goval-result.txt`, `regress-fix2.log`, `link/out/SELFTEST` and `link/out/FUNCS.md`, and put the generated files in `.gitignore`.
- We found 16 unused lemmas with the dependency closure and deleted them: `bva_s40`, `bva_s48`, `bva_slot'`, `bva_nat`, `bva_rbx`, `bvm_o`, `bvm_one`, `bvr_a`, `bvr_sc`, `bvr_sc'`, `Fk.sep_drop`, `cpm_slot`, `Fk.spill_sep`, `f88`, `f120`, `Keep1.refl`. We kept `rtvbl_16` because it is an rfl lemma.
- Witness generator: the common functions of `wgen.py` and one table `ALL` make the 74 files again. The regeneration result is byte-identical to the committed files. The files without a generator are `WitAd`, `WitCp`, `WitCpM`, `WitFv` and `Witness`. We moved the proof skeleton (`hk_*`, `hf_*`, block split) to four theorems and the macro `wit_split` in `WHost.lean`.
- We deleted session marks and past-state sentences from the `Fk/*.lean` comments. The file header docstrings are 5 lines or fewer.
- We reduced `fv/AGENTS.md` to 76 lines that contain only rules.

Checks (baseline → after cleanup):

| Check | Baseline | After cleanup |
| --- | --- | --- |
| `lake build` | 856 jobs | 856 jobs |
| AXIOMS theorems | 1583, NONSTANDARD 0 | 1571, NONSTANDARD 0 (−16 deleted, +4 `WHost` theorems) |
| AXIOMS all declarations | 8028, NONSTANDARD 0 | 7975, NONSTANDARD 0 (witness skeleton auxiliary declarations −26, deleted theorems and their auxiliary declarations −27) |
| Link check | PASS | PASS. ELF sha256 `9c850c97…c501`, `norm/*.S`·objdump·nm·`Code.lean` unchanged. BUNDLE changes because `AXIOMS.txt` changed |
| Self-tests | 24 | 24 |
| Negative tests | 16 | 16 as expected (control PASS, 15 mutations FAIL in the designated theorem) |
| goval | 79/0/2 | 79/0/2 |
| `go test ./fv/kraken/semtest/` | ok | ok |
| `RegressFix2.lean`, review Lean files | Some fail | All without errors |

Size (files that git tracks):

| Scope | Files before → after | Lines before → after | Size before → after |
| --- | --- | --- | --- |
| `lean/Fk/*.lean` | 148 → 148 | 27,733 → 26,269 | 1,820K → 1,688K |
| Of these, `Wit*.lean` | 79 → 79 | 9,645 → 8,596 | 740K → 640K |
| `lean/tools/wit` | 34 → 31 | 3,679 → 3,164 | 304K → 244K |
| All of `link` | 72 → 40 | 33,812 → 27,326 | 3,820K → 3,588K |
| `review` | 96 → 23 | 10,612 → 3,857 | 948K → 304K |
| `vcgen` (without `.lake`) | 17 → 8 | 2,583 → 388 | 192K → 44K |
| Report md | 11 → 6 | 2,267 → 586 | 244K → 68K |
| `fv/AGENTS.md` | 1 → 1 | 167 → 76 | 8K → 8K |
| All of `fv/kraken` | 434 → 311 | 85,757 → 66,598 | 7,712K → 6,372K |

## 8. Memory optimization memopt (2026-11-09 20:31 – 21:27)

Commits `86fd060..509faff` (branch `syjn99/ssz-fv-memopt`). The report was `memopt/REPORT.md`. It was removed on 2026-11-12 (section 13).
In a 9.69 GiB Linux environment, `lake build` failed with OOM at `Fk.WitLcM4x16`.
The cause is the `by decide` of `u64v0`–`u64v3`. Elaboration computes `u64Bytes`, and the four proofs run at the same time.
We changed one proof line of `wlcm.py` to `simp [u64Bytes, uintBytes]` and regenerated three witnesses. We did not change the propositions.
Numbers: `WitLcM4x16` alone peak 13.01–13.27 GiB → 1.42 GiB (macOS 48 GiB). In a 9.69 GiB container, the original alone got an OOM kill, and the full build of the fixed version succeeded with 856 jobs (`memory.peak` 7.41 GiB).
The inspector diff is only 7 lines of `u64v` axioms (`propext`, `Quot.sound`). AXIOMS 1571/7975, NONSTANDARD 0. All regressions succeeded.
The verdict is "conditional". Reproduction on the user machine remains.
The independent review (gpt-6-astra, `253a84a`) was also conditional. In the `Expr.equal` comparison of 290 declarations, there was no assertion weakening.
P1 of the review (cache reuse in the section 8.2 reproduction) and the two P2 items (`run.sh` exit code, `gen.py` source) were fixed in the last commit of the branch.

## 9. Fix 3 link redesign (2026-11-09 15:15 – 17:25 UTC, fix3 stream)

We deleted the Lean and Go source regexes of the link check and got the same guarantee with Lake inputs and ELF data include.
X1: we registered three `input_dir` in the `Fk` `needs` of `lakefile.toml`. After an experiment (control Built 0, on a 1-byte change `Fk.Code` rebuild and designated theorem failure, restore), we deleted SHash and check (f).
X2: we included 22 entries with `link/data.py` and `data_include`. We replaced 12 hand constants and deleted checks (g)(h), role classification and `golits.go`. The new check (f) is data file = ELF. The self-tests went from 24 to 10.
X3: we added `sc_reject_bool_err` (premise `e0 ≠ 0`, conclusion rax ≠ 0). We changed the error globals of 18 witnesses to initialized values, and the type descriptors of 5 `%w` witnesses to ELF bytes. goval checks both.
X4: `sc_size_main` memory identity, `sc_marshal_main` r14, `ne_marshal_main` R, ListC dead stack `lcStk`.
X5: contract `FmtErrorfDDC`, model and `joint_models` (11), loop lemma `lcl_order`, `lc_reject_offset_order_main` from the entry (first pair), witness `WitLcO`, negative test lcorder and control. At first we deferred it only on a cost estimate, then we did it by the orchestrator decision. We did not start element error propagation ("Items: %w").
X6: gate table correction (eight size identical, BitVec makeslice, ListC 5/10 (6/10 after X5), count of not-checked items by kind).
X7 (final code `f45903c`): cold project build 863 jobs, axioms 1627/8287 NONSTANDARD 0, check PASS, self-tests 10, negative tests 18, goval 80/0/2, go test PASS.
Retractions: `review/ReviewSHashFixAstra.lean` (target deleted), the `bool_two_returns_nil` example (the issue closed, so we changed it to `bool_two_returns_error`).

## 10. Fix 3 review changes (2026-11-09 17:55 – 20:05 UTC, fix3 stream)

The first review of fix 3 was REQUEST_CHANGES (items M1–M4).
Stage A (`d9cdb40`, approved by the second review of fix 3): `data.py` gives the same output as the tracked files (deleted the `# text` lines, added `data.py --check`). We rewrote REPORT section 8 as a block that runs unchanged. We wrote the trust limits of astra 1–3, which were closed by deletion. We made the line rules of the two readers the same.
Stage B (M4): the function specification of the ListU64 short input reject (`LuURejShortC`, derived from the machine code), the element error propagation theorems `lcl_itemerr`·`lc_reject_item_main`, the include entry `lcFmtItems` (API v3, addition only), witness `WitLcI`, negative test lcitems and a control that builds again.
The first build of `WitLcI` was a kernel OOM kill. After that, we diagnosed it with an RSS monitor (5 GiB): the `exact h` of the last theorem unfolded the separating conjunction by definition because of the remaining `emp` frame. The second attempt built with 2.74 GiB.
The third review of fix 3 approved stage B (`f9e2bc3`). The verdict stays conditional (gate 1 not passed). The last commit changed only documents (numbers, memory prerequisites, known limits).

## 11. 1c generator and Prysm inventory (2026-11-09 15:14 – 23:27 UTC, phase 1c stream)

We regenerated Prysm `ab15ff70` (slice + `ssz-size`) with the generator `698c202` and made a new experiment ELF with Go 1.26.10 (P1, inventory 135, 132 in scope).
We first committed the fixed inventory (3676 theorems + 134 hand case rows) and the list of allowed assumptions. The independent Desc checker was fixed three times in reviews r1–r3, and after r3 we changed the design to a closed world and content-bound results (r4 approval).
Two rebases after the fix3 approval. P7: witness generator (76/76 bytes same, Go value Lean predicate). P8 (X4): the generator made again the 58 hand main theorems of the 9 hand-case types. Scalars·ListU64·ListC use the directive walk and loop template, and the other six use a fixed template read from the hand modules. All have statement SAME, Lean passes, only standard axioms, and the mutations fail inside the designated theorem. 88–100% of the generated proofs are the same text as the hand proofs.
X5: Go 1.26.10 link table (a)–(f) PASS. Of the 132 Prysm types, only the size of 46 was proved. All decoders and encoders were rejected because the templates do not fit (hand-written primitives calls 2, no template 132).
X6: the `%riz` rule of `conv.py --norm` (Go 1.26.3 bundle unchanged), a fix of the 10-byte instruction read defect of `check.py`, section 10 of this report.
Reviews: the phase 1c reviews 1 to 7 (all APPROVE from review 4, recommended fixes applied). Memory: all Lean work under gate + memory cap, 0 kernel OOM.

## 12. End-to-end proof of the real Prysm Checkpoint (2026-11-10 01:17 – 02:40 UTC, Prysm end-to-end proof stream)

On top of the phase 1c checkpoint `6e82ae24`, we made a new Lean library `E2e` and the namespace `prysm/go1.26.10/e2e/`.
We confirmed from the call graph and `-m=2` whether the Epoch methods are inlined. Link table 7 functions, 10 data entries, checks (a)–(f) PASS.
We wrote a hand Desc from consensus-specs and matched it with the checker Desc. We read the Go 1.26.10 runtime source again (no changed contracts, the growslice change in the plan was a change of `moveSliceNoCap`).
We proved Epoch decoder accept as a function specification. We proved Checkpoint decoder accept, size reject, unreachable paths and specification alignment, encoder fast path and composition.
The decoder theorem was killed two times at the 6 GiB process cap (not a kernel OOM). The cause was `trivial`/`rfl` on the last register goal. We divided the theorem in two and changed the closing tactic.
Negative tests 30/30, 23 axioms standard, Go differential 47 cases match. We did not do encoder reject, the growslice path or Epoch reject.
The first review of the Checkpoint proofs (9bad532) found that the composition theorem does not run the decoder (item M1, FINDINGS R-1). We renamed it to `cp_e2e_marshal_decoded_receiver` and changed E5 (the composition step) to not complete. In INBOX 004, we proved encoder reject, encoder specification alignment, size with a witness, Epoch reject and the Go value predicate.
In session 2, we proved the real composition of M1, `cp_e2e_unmarshal_then_marshal` (decoder entry → encoder return, output = dst ++ 40 input bytes), and the one-Host witness `WitCpC` (first attempt, 1 syntax fix for the witness). Negative tests 11/11. Then we proved the encoder growslice path `cp_e2e_marshal_grow_main` (first site, `GrowsliceC` esz 1) and the witness `WitCpG` (len 30, cap 36) (4 theorem runs: UInt64/BitVec form of the length inequality, 1 probe. Witness on the first attempt). Negative tests 9/9. We handled review S1–S9 (S2 wording kept). All negative tests 73/73 (900 s per-case limit), 49 axioms standard, Go differential 48 cases with 0 mismatches.

2026-11-10 Prysm end-to-end session 4: we proved A3 (real AttestationData decoder accept, size reject, 4 unreachable wraps, specification alignment, witnesses) at `8cba8b4`. After that, by INBOX 009, we stopped A4 (the AttestationData encoder) and proved the remaining capacity cases of the Checkpoint encoder: the case where the first site fits and the second grows, all cases where the first site grows (up to the entry of the second growslice call), the reject after growslice, and two case covers. The rest of the run of the second growth after the first growth is blocked because the `GrowsliceC` form cannot connect two calls (T-7, OUTBOX 007). We did not change the existing theorem statements.

2026-11-10 Prysm end-to-end session 5 (INBOX 010, handling of the third review of the Checkpoint proofs, REQUEST_CHANGES): we committed M1 `cp_e2e_marshal_grow_any_sharp` (after the first growth: return, return through the second growslice, or the entry of the second call when the remaining heap is smaller than the budget), M2 two cover theorems that state the frame and the witnesses `WitCpWF`·`WitCpWRF`, S1 `GoValW`, S3–S6 record fixes, the FINDINGS history index and the extensibility step S0 baseline (`scal/BASELINE.json`). We did not change the existing theorem statements. The remaining area of T-7 is blocked (differential only) until a user decision. S2 is partly done. A4 (the AttestationData encoder) and step S1 (the scalability lemmas) are not started.

2026-11-10 Prysm end-to-end session 10 (INBOX 020, after the review of the evaluation of hold-out H1 (ValidatorIndex, BeaconBlockHeader) approved): we added the S1–S6 document fixes and 4 negative tests for NF-12 (no negative case targeted three H1 theorems). We proved the unreachability of the two error-wrap sites of the BeaconBlockHeader decoder and the ValidatorIndex length reject. The BeaconBlockHeader encoder fast path did not close the memory postcondition of section A. We stopped at the limit of 3 attempts (T-9, 4 memcap kills).

2026-11-11 Prysm end-to-end session 11 (INBOX 021, after the review of session 10 approved): we added the S1–S5 record fixes and the notes NF-13…NF-15. We diagnosed T-9. The cause of the memcap kills was the memory of the Lean kernel. When we divided section A into A0 (stack guard), A1 and A2, there was no kernel memory failure in A1, A2 and the composition (session 12 correction: we wrote that they closed, but they depended on `sorryAx`). The kernel check of A0 did not close within the limit. We stopped at the T9-PLAN limit (6 attempts).

2026-11-11 Prysm end-to-end session 12 (INBOX 022, handling of the review of session 11, REQUEST_CHANGES): we fixed only records. We did not change Lean files. The "A1, A2 and composition closed" of session 11 was wrong. In the `#print axioms` run of the review, all three depended on `sorryAx`, and the composition also depended on an A0 variant that the kernel rejected. The location of the kernel memory fault in A0 is valid. The "unreachable" proofs in the first paragraph of §12, session 4 and session 10 are conditional skips. Unreachability for all inputs holds only together with the callee specifications (NF-15). We added the process rules P-1 (decide the closure of a temporary result with `#print axioms`) and P-2 (a task command ends with the Lean exit code) to FINDINGS.

2026-11-11 Prysm end-to-end session 13 (INBOX 023, hold-out H2 evaluation): we opened `v1alpha1.Eth1Data` at `7a5ea61`. The one run of the fixed generator `p2dec` stopped with exit 2 and no output (SG-1, DepositRoot at offset 0). The generator coverage is 0/2 fields. We proved by hand the decoder accept, size reject, specification alignment, codec equivalence and witnesses (standard axioms). We did not try the encoder because it has the same stack guard head as T-9. We did not change the generator, kinds, lemmas or templates. This session did not change `REPORT.md`.

2026-11-11 Prysm end-to-end session 14 (INBOX 024, handling of the first review of H2, REQUEST_CHANGES): we fixed only records. We did not change Lean files. We deleted "H2 was not opened" from section 11 of `REPORT.md` and added the H2 results and limits (M1). We fixed section 7 of `CONTAMINATION.md`, FINDINGS SG-1 and `RESULT.json` (S1–S3). We added 2 negative tests (S6, 27/27).

2026-11-11 T-9 stream (user instruction, new budget, base `48b74b6`, branch `claude/ssz-fv-t9-fable`): a new Fable session wrote the proofs directly. One diagnosis decided the cause. A proof that closes the stack guard branch with `simp` and `omega` fails the kernel check under the 5 GiB limit. It is the same for a `BitVec` proposition without the machine context. We did not profile the expensive subterm. That the literal 2^64 − 32 is the cause is an inference (wording of the review of the T-9 stream). We closed it with the lemma `E2eScal.lea_cmp_be_false` (on top of the unchanged `Fk.cmp_be_false`). We proved `bh_e2e_marshal_main` (fast path only) with six sections and a composition. We added a witness, specification alignment, 36 negative tests, 21 Go differential cases and the axioms gate. 5 attempts (2 failures: a missing range assumption in the return address expression, and the `⋆` association direction and a missing import in the specification-conformance theorem). We did not change `Fk/*`, contracts, generators, kinds, templates, the ELF or the toolchain. The growslice branch and the length reject are out of scope. There is no independent review yet.

2026-11-11 SG-1 stream (user instruction, base `48b74b6`, branch `claude/ssz-fv-sg1`): this is development work after the two hold-outs were opened. We added the template `rootdec_seg_z` and the kind `rootDecSegZKind` for the offset-0 decode section. We made `scalgen.py p2dec` accept the offset-0 form. The extended generator produces 2 of the 2 Eth1Data root fields (`GenE1Dec.lean`). Eth1Data is development data of this extension and is in-sample. The H2 result from before the extension (fixed generator, exit 2, 0/2 fields) stays as a historical result. The results of H1 and H2 did not change. The review of the SG-1 extension approved `da3f233`.

2026-11-11 Prysm end-to-end session 15 (INBOX 027, integration): we merged the T-9 stream (`154944e`) and the SG-1 stream (`da3f233`) with `--no-ff` (`e56063c`, `63ef3b9`). The conflicts were only in the records and inventories that the two streams changed. We kept both sides. The Lean, generator and test files are the same bytes as in each stream. On the merge tree, we ran again the build, the axioms gate, the three-way declaration comparison, the regeneration check, the kind check and the negative tests of the two streams. We applied the items to fix of the reviews of the T-9 stream and the SG-1 extension and of the second review of H2 to the records and tests. There is no independent review yet.

2026-11-11 base record unit (items to fix R1–R5 of the review of the session 15 integration): we do not change earlier dated paragraphs, and we add corrections.
The T-9 stream got a review (approval, `154944e`).
The integration also got a review (approval, `c3c56a1`).
The "There is no independent review yet" in the T-9 stream paragraph and the session 15 paragraph is replaced only on this point.
We added a "historical" mark to the H1-time and H2-time statements of `scal/RESULT.json`. We did not change the numbers.
We changed the description text of `StackGuard.lean` to the recorded cause. We did not change the theorems or proofs.
We added the baseline document `prysm/BASELINE.md` to move to another machine.

Hold-out H3 (2026-11-11, method frozen at `dda707c`): a new evaluation session opened `UnmarshalSSZ` of BlobIdentifier and DepositMessage once.
We committed the opening record first (`782a41b`). The fixed generator ran once per type, and the raw output was not touched.
The generator coverage is 1/2 and 1/3 fields. The rest was proved by hand (FINDINGS SG-2: the frozen generator reads only 32-byte byte-vector fields).
We did not change the generator, kinds, template lemmas, `Fk/*` or contracts. There is no independent review yet.

2026-11-11 encoder reuse stream (user instruction, base `dda707c`, branch `claude/ssz-fv-enc-reuse`): a new Fable 5.2 session wrote it directly.
We added the reuse blocks `E2eScal.enc32_call` (memmove call) and `E2eScal.enc_reject_tail` (length reject tail).
We proved the three BeaconBlockHeader root blocks again with `enc32_call`. The statements are equal by `rfl` to the existing ones. We did not change existing modules.
We proved the fast path, the specification-conformance theorem and the witness of `Eth1Data.MarshalSSZTo`.
We proved the three BeaconBlockHeader length reject sites and witnesses. The premise is `len + 112 ≤ cap`.
A multi-directive encode template does not fit all 6 sites in common (FINDINGS ENC-1). We stepped the section before the call by hand at each site.
10 attempts (3 failures), 3 diagnoses, gate 646 s. Two modules of the `.lake` that we moved from the first task were stale, so we ran `lake build E2eScal` once. `P2EncCp` was not built again.
The gate did not accept the stream name `enc`. We ran the tasks with the stream `prysm-e2e` and the tag `enc:`.
32 of the 33 negative tests are as designed. For 1, the author targeted the wrong theorem, and we do not count it as a pass.
The axioms gate is PASS (3813 declarations). The declaration difference is ADDED 330, CHANGED 0, REMOVED 0.
Not proved: the growslice branch, the morestack path, the length reject with a small capacity, the Eth1Data length reject, the Go value predicate.
There is no independent review yet. We did not write to the remote.

2026-11-11 integration of H3 and the encoder reuse work (base `dda707c`): we merged the two streams with `--no-ff` (`500571c`, `c10daf9`).
The review of H3 approved `75166e4`, and the review of the encoder reuse work approved `ad15fbc`. Neither has required fixes.
The "There is no independent review yet" in the H3 paragraph and the encoder reuse paragraph is replaced only on this point. We did not change the dated paragraphs.
The conflicts were only in records and inventories. We kept both sides. A `.lean` file that only one stream changed is byte-identical to the end of that stream.
In FINDINGS, both streams added a section 15. H3 keeps section 15, and the encoder reuse work became section 16. No file cites this number.
The H3 merge commit title is `merge(kraken):`, and the earlier merges are `merge:`. We do not change the history.
The merge tree checks and the handling of the items to fix are in `integration_int2` of `scal/RESULT.json` and in REPORT section 11.
Note (item S7 of the review of H3): commit `11babc9` used `spec(...)` as the type. In `fv/AGENTS.md`, `spec` is a scope. We do not change the history.
Note (item S8 of the review of H3): the H3 evaluation session ran `ls` and `git log -1` in a second worktree, read-only. This was not in the deviation list.
Note (item S4 of the review of the encoder reuse work): one interval between its tasks was 1.95 s. The rule is 2 s or more.
Note (item S5 of the same review): the author of the encoder reuse work saw the file names of the run directory `h3/` and 5 H3 gate records. The author did not see the code.
Note (b1-r1 S8): there was no 2 s pause between B1 tasks 02 and 03.

2026-11-11 integration of the optimization test OPT-R1 (a generator option that reserves `len + 40` once in `Checkpoint.MarshalSSZTo`): we merged the stream `5821b19` with `--no-ff` (`83e0b6a`). There were no conflicts.
The review of OPT-R1 approved `5821b19`. There are no required fixes. The items to fix S1–S6 were closed with records.
S2 and S4 were written as statements without new proofs. S3 ran once with 900 s per case. Neither is a pass.
We did not merge the generator branch `claude/ssz-gen-opt-r1` (`ca191bb`). We did not change proof bodies or theorem statements.
The merge tree checks are in `integration_int3` of `opt-r1/RESULT.json` and in REPORT section 11. We did not write to the remote.

2026-11-11 record after the review of the two integrations (H3 with the encoder reuse work, and OPT-R1): that review approved `a70492c`. 0 required fixes, 6 items to fix.
S2 was closed with a `fv/kraken/.gitignore` rule and "Known violations" in `TOOLS.md`. S3 and S4 were closed with appended corrections and current-state cells.
S5 was closed by writing the OPT-R1 commands and the 20 H3 modules in the reproduction block of REPORT section 11. S1 stays a user decision.
S6: the merge commit `500571c` has no `Co-Authored-By` line. We do not rewrite history.
We changed only documents, JSON records and ignore rules. We did not change `.lean`, generators or pinned versions. We did not write to the remote.

2026-11-11 generator work for the `--gen2` mode (base `6c62a49`, new Opus session, no review yet):
We added the optional modes `p2dec --gen2` and `--compose` to the proof generator `scalgen.py`. The output of the default mode is the same.
The review of the `--gen2` lemma unit approved that unit. This work did not change the lemma files.
The generator ran once per type, and the raw output is 6 new files. The old generated files and the H3 records are unchanged.
We proved again the accept theorems of BlobIdentifier and DepositMessage with generated sections. The statements are equal by `rfl` to the hand theorems.
We added 76 names of the two `--gen2` units to `AxiomsScal.lean`. We replaced the committed `axioms-gate.json` with the output of the current tree.
We did not write to the remote. Records: REPORT section 11, section 14 of `scal/CONTAMINATION.md`, `gen2` of `scal/RESULT.json`.

2026-11-11 fix unit for the `--gen2` mode (new Opus session, no review yet).
The review of the `--gen2` generator work was REQUEST_CHANGES. The two required fixes were documents.
We fixed the sentence "the remaining hand work is one generator command line per type" in REPORT section 11. The hand base theorems and the 824 lines of the `--gen2` lemma modules remain.
We deleted the run directory name from a `kindcheck.py` comment.
`kindcheck.py` accepts `_type` only for composed theorems, and only with a right side that is not a generated name.
`--gen2 --partial-out` writes a valid Lean module. We committed `Gen2BhDecPartial.lean` (3/5) as the raw output.
If `--compose` has no hand statement, it writes an `UNCHECKED STATEMENT` mark. We added `--same-as-prop`.
Known cosmetic item: the header of the lemma module `KindN.lean` says "four places" and lists five (item S4 of the review of the `--gen2` lemma unit). It is a lemma module, so we do not fix it.
We did not write to the remote. Records: REPORT section 11, section 15 of `scal/CONTAMINATION.md`, `gen2-fix` of `scal/RESULT.json`.

2026-11-11 hold-out H4 evaluation of Deposit_Data and PendingPartialWithdrawal (new Opus session, evaluator, no review yet).
We counted again the 15 blobs and two tree ids of the method freeze `eacf0fb`. All are the same. The opening record is `9d338fa`.
We committed the hand Desc and the hand statements (`H4Stmt.lean`) before the generator run.
Segment result (S): Deposit_Data 3/4 (exit 3), PendingPartialWithdrawal 0/3 (exit 2). Composed result (C): both rejected (exit 2).
We kernel-checked the Deposit_Data accept theorem as a hand composition. It uses three generated sections and one new hand lemma.
We could not prove the PendingPartialWithdrawal accept theorem within the limit of 3 attempts.
Negative tests 30/32, axioms gate PASS, declaration comparison only ADDED 281, Go differential 12/12.
We did not write to the remote. Records: REPORT section 11, section 16 of `scal/CONTAMINATION.md`, `H4` of `scal/RESULT.json`, FINDINGS SG-3 (coverage gaps of the `--gen2` generator on H4).

2026-11-11 integration of the `--gen2` work and H4 (new Opus session): we merged `claude/ssz-fv-h4` `fae7d6f` (`56e0c88`, no conflicts).
The "no review yet" in the `--gen2` generator, `--gen2` fix and H4 paragraphs above is replaced by the following reviews. We do not change those paragraphs.
The review of the generator work was REQUEST_CHANGES (documents only), and the fix unit closed it. The reviews of the fix unit and of H4 are APPROVE, 0 required fixes.
Correction to the H4 paragraph (item S1 of the review of H4): two of the covered fields of Deposit_Data 3/4 are close to the sample.
The only covered field outside the sample is Signature. The field that it could not cover has the 32-byte shape that is close to the sample.
Record of item S7 of the review of H4: three H4 commits use `spec(...)` as the type. In `fv/AGENTS.md`, spec is a scope. We do not rewrite history.
On the merge tree, we confirmed again the build, the axioms gate (5007 declarations), the declaration comparison (0 differences) and `regen_check.sh` 16/16 SAME.
We did not change `.lean`, generators, checkers or pinned versions. We did not write to the remote. Records: REPORT section 11, `integration_int4` of `scal/RESULT.json`.

Generator unit for the `--gen3` mode (base `f5c5f52`, Opus 5.5 implementation, before review): we added `p2dec --gen3` to the proof generator.
It covers call fields, two-directive uint64 reads and padding `nop` before makeslice with the lemmas of the `--gen3` lemma unit. The 16 old outputs are SAME.
Development type coverage (in-sample): PendingPartialWithdrawal 3/3, Deposit_Data 4/4, BeaconBlockHeader 5/5, AttestationData 3/5.
Deposit_Data composition run 1 was a syntax error. We keep the raw output as a record and used the fixed run 2.
We put items S1–S4 of the review of the `--gen2` fix unit and the new kinds into `kindcheck.py`. Records: REPORT section 11, `gen3` of `scal/RESULT.json`, CONTAMINATION section 19.

2026-11-11 hold-out H5 evaluation of SyncCommitteeMessage and PendingConsolidation (new Opus session, evaluator, no review yet).
We counted again the 5 blobs and 4 tree ids of the method freeze `6dc0e2a`. All are the same. The opening record is `3762644`.
We committed the hand Desc and the hand statements (`H5Stmt.lean`) before the generator run.
Segment result (S): SyncCommitteeMessage 2/4 (exit 3), PendingConsolidation 1/2 (exit 3). Composed result (C): both rejected (exit 2).
By field kind, the two types are close to the sample. Only the order is new.
We kernel-checked the two accept theorems as hand compositions of generated theorems and hand lemmas.
Negative tests 37/41, axioms gate PASS, declaration comparison only ADDED 378, Go differential 12/12.
We did not write to the remote. Records: REPORT section 11, section 20 of `scal/CONTAMINATION.md`, `H5` of `scal/RESULT.json`, FINDINGS SG-4 (coverage of the `--gen3` generator on H5).

2026-11-11 integration of the `--gen3` work and H5 (new Opus session): we merged `claude/ssz-fv-h5` `1fec11e` (`2bedf6d`, no conflicts).
The "before review" and "no review yet" in the `--gen3` generator and H5 paragraphs above are replaced by the following reviews. We do not change those paragraphs.
The reviews of the `--gen3` lemma unit, the `--gen3` generator unit and H5 are APPROVE, 0 required fixes. The review of the `--gen2` and H4 integration approved that integration.
H5 correction (item S1 of the review of H5): 2/4 and 1/2 are the results for types that are close to the sample by field kind.
H5 correction (S2): there are 77 gate tasks. The shared gate seconds are 315.0 (includes tasks 84 and 85).
Record of item S6 of the review of H5: four H5 commits use `spec(...)` as the type, and one uses `test(link)`. We do not rewrite history.
On the merge tree, we confirmed again the build, the axioms gate (5841 declarations), the declaration comparison (0 differences) and `regen_check.sh` 23/23 SAME.
We did not change `.lean`, generators, checkers or pinned versions. We did not write to the remote. Records: REPORT section 11, `integration_int5` of `scal/RESULT.json`.
2026-11-11 task B and AU-07, the slow omega side goal in `P2EncCp` (base `71161fa`, macOS 26.7.2 arm64, Apple M5 Pro, 18 cores, 48 GiB).
We ran the first build once from an empty `.lake`.
The toolchain was already installed.
`lake build E2e E2eAd E2eScal` is exit 0, 1209.1 s, 912 jobs (n = 1).
The gate is PASS (4519 declarations, 3813 theorems, hand list 315).
The comparison with the committed record is `DIFF []`.
This is not x86-64 evidence.
We found the slow call of AU-07 with the trace log.
The position is the `bv_omega` of the argument `hLo` of `rootenc_seg`, line 163 of `P2EncCp.lean`.
The independent review of task B, REVIEW-B, confirmed the position.
The verdict of REVIEW-B is "accept after required fixes".
That run record and review record are outside the repository.
Record before the fix: attempts 1–3 (953–973 s omega) did not become faster.
The `hfit` side goal and the three `have` were not the cause.
The before-fix baseline with the same method is one run of item S6 of the review of the audit fixes, 986.0 s.
That run was on the original machine (Linux arm64) with the unchanged file.
The 732 s of the audit is the value of a different run.
We changed that one `by` block to the form `rw [show … by bv_omega]`.
The theorem statement is the same.
The file check went from 1022.9 s to 8.3 s (macOS arm64, n = 1 each).
The two values use different methods (`opt1/AU-07.json` attempt 4).
The incremental rebuild of the existing `.lake` (rebuild of one module, 7.3 s) is exit 0.
The declarations went from 4519 to 4518, and the theorems from 3813 to 3812.
The `Quot.sound,propext` set is 2085 to 2084.
Data: by name, `cp_e2e_marshal_main_s._proof_1_23` is REMOVED and `_13`–`_22` are CHANGED.
By content, the base row with no head match is `_proof_1_13` (type hash `00000000e439c2be`).
For n = 13…22, the head `_proof_1_n` is the same as the base `_proof_1_(n+1)`.
Limit: the type hash is a 32-bit structural hash and is not a proof of definitional equality.
The type hash and axioms of the main theorem are the same.
Inference (from the position): the removed base `_proof_1_13` is the lemma of the slow call.
The verdict of the independent review REVIEW-AU07 (2026-11-11) is APPROVE.
There are 0 required fixes and 7 recommended fixes (RA-1–RA-7).
The review target is the base `71161fa` and the diff sha256 prefix `6b056f2a`.
The reviewer built from an empty `.lake` in a new copy: exit 0, 489.4 s, 912 jobs (n = 1).
REVIEW-AU07 confirmed that RB-1–RB-10 of REVIEW-B are closed.
Applying RA-1–RA-7 changed only documents, and it needs a separate check.
We did not write to the remote.

2026-11-11 integration (ARM task B, AU-07 fix): we merged `74cc9ca` of `syjn99/ssz-fv-arm-b` (= `71161fa` + `ab43cbb` + `74cc9ca`) into this branch.
The changed Lean is one `by` block of `E2eScal/P2EncCp.lean`. The theorem statement is the same (the task B record above and the reviews on that side, REVIEW-B, REVIEW-AU07, REVIEW-AU07-R2).
This merge did integration only. On the merged tree, we did not run a build, the axioms gate, a declaration comparison, time measurement or a new review (user instruction).
The numbers in the task B paragraph above (4518 declarations, 3812 theorems, axiom set 2084, 1022.9 s → 8.3 s, 489.4 s) are values measured on the `71161fa` + fix tree on macOS arm64. They are not the values of this tree.
The committed `axioms-gate.json` of this tree is the record from before the merge (5841 declarations), and we did not make it again. By the declaration comparison of task B, one auxiliary declaration goes away and ten numbers shift. We did not confirm this on this tree.
We did not bring in the task B addenda (the 4518 note) to `opt-r1/MANIFEST.md` and `opt-r1/RESULT.json`. We kept the `axioms-gate.json` of this branch unchanged.
2026-11-11 generator unit for the `--gen4` mode (base `718e023`, Opus 5.5 implementation, before review): we added `p2dec --gen4` to the proof generator.
It uses data-flow matching, per-instruction step theorems and window blocks. The 23 old outputs are SAME.
Coverage of the 10 development types (in-sample): 9 fully, AttestationData 3/5. With `--gen3`, SyncCommitteeMessage was 2/4 and PendingConsolidation 1/2.
We proved the three accept theorems again with generated chains. The field composition is hand text.
The SyncCommitteeMessage generated chain is 457 lines. We recorded that it goes over the 400-line condition.
Records: REPORT section 11, `gen4` of `scal/RESULT.json`, CONTAMINATION section 22.

2026-11-11 first fix of the `--gen4` mode (base `21b8aab`, Opus 5.5 implementation, before review): we fixed items M1, M2 and S1–S3 of the review of the `--gen4` generator unit.
On 7 review inputs, the `--gen4` walk said "covered" without an entry state. Now it rejects them.
We added the head check, the stack store rules, the stop on rbp / r14 writes, the miss classification and the `reached` flag.
The 10 committed `--gen4` outputs and the 23 old outputs are SAME. We wrote in the records that "covered" is a generator claim.
Records: REPORT section 11, CONTAMINATION section 23, `gen/scal/README.md`.

2026-11-11 second fix of the `--gen4` mode (base `a81c0ea`, Opus 5.5 implementation): we fixed item M3 of the review of the first fix.
It compares the head size immediate with the IR size, and we added the epilogue rules.
The review of the second fix found a gap in the epilogue rules (item M4). It accepted a `jmp` to a label outside the file.
So "checks the epilogue" in the README and REPORT section 11 went too far. The third fix fixed it.

2026-11-11 third fix of the `--gen4` mode (base `6ac27e4`, Opus 5.5 implementation, before review): we fixed item M4.
Three reviews in a row each found one path that was not checked. So we changed the result logic to fail-closed.
Exit 0 comes only when all three success flags are set. The injection tests confirm this at each step.
The 10 committed `--gen4` outputs and the 23 old outputs are SAME.
Records: REPORT section 11, CONTAMINATION section 25, third-fix section of `gen/scal/README.md`.

2026-11-11 hold-out H6 evaluation of 7 flat fixed-size types: PendingDeposit, PowBlock, HistoricalSummary, SigningData, SyncAggregatorSelectionData, ValidatorBalance, VoluntaryExit (new Opus session, evaluator, no review yet).
We counted again the 5 blobs and 4 tree ids of the method freeze `0e775ac`. All are the same. The opening record is `dcc71a8`.
We committed the hand Desc and the hand statements (`H6Stmt.lean`) before the generator run.
Segment result (S): all 7 types of the batch exit 0, total 18/18 steps covered. Composed result (C): reject by design, not run.
By field kind, several types are close to the development types. We measured only the variation of known kinds.
We kernel-checked the PendingDeposit and PowBlock accept theorems as hand compositions of the 8 generated chains as produced.
Negative tests 36/36, axioms gate PASS, declaration comparison only ADDED 570, Go differential 12/12.
The hold-outs of this population are all used. We did not write to the remote. Records: REPORT section 11, CONTAMINATION section 26, `H6` of `scal/RESULT.json`, FINDINGS SG-5 (coverage of the `--gen4` generator on H6).
2026-11-11 integration of the `--gen4` work and H6 (new Opus session): we merged `claude/ssz-fv-h6` `8ce5dda` on top of `3e1cedc` (`9d8aaf9`).
The conflicts were in 8 record files. We kept both sides. `.lean` is the same as the stream, and only `P2EncCp.lean` is the same as `74cc9ca`.
The "before review" and "no review yet" in the `--gen4` generator, first fix, third fix and H6 paragraphs above are replaced by the following reviews. We do not change those paragraphs.
The reviews of the `--gen4` lemma unit, the third fix and H6 are APPROVE. The reviews of the `--gen4` generator unit, the first fix and the second fix were REQUEST_CHANGES. The review of the `--gen3` and H5 integration approved that integration.
Addition to "did not build the merged tree" in the ARM task B merge record above: this integration built it for the first time.
`lake build` exit 0, 53 modules built (52 new modules and `P2EncCp`). `E2eScal.P2EncCp` was built again in 10 s (Lake display, n = 1).
Axioms gate PASS, 7649 declarations. We made the committed `axioms-gate.json` again.
The only difference against the dump of the H6 review is 11 lemma lines of `cp_e2e_marshal_main_s` (REMOVED 1, CHANGED 10). The main theorem row is the same.
Record of item S8 of the review of H6: four H6 commits use the type `spec(kraken)`, and one uses `test(link)`. We do not rewrite history.
`regen_check.sh` 40/40 SAME, `kindcheck.py --selftest` PASS, `p2dec_test.py` 262/262.
Task 08 ran without arguments and gave exit 2 (usage). Task 09 ran it again with the arguments.
We did not change `.lean`, generators, checkers or pinned versions. We did not write to the remote. Records: REPORT section 11, `integration_int6` of `scal/RESULT.json`.

2026-11-11 generator unit for the `--gen5` mode (new Opus session, before review): we added `p2dec --gen5`. The front end is the `--gen4` walk.
It produced accept theorems and size reject theorems for 15 flat development types. It refused 2. The result is fail-closed.
The 9 types with a hand statement are bound by `rfl`. Checkpoint is not bound (layout order). The old outputs 40/40 are byte-identical.

2026-11-11 review of the `--gen5` lemma and generator units (new Fable, target `ea6a0c6`): REQUEST_CHANGES, records only. All technical checks passed.
Step 0 of the close-out unit fixed the records. The hand statement identities are 9, not 10.
Before the committed generator run, there were five scratch test runs without the gate. The results do not change. Records: CONTAMINATION section 30.

2026-11-12 close-out of the five remaining flat decoders (close-out unit, new Opus session, before review): we built specifications, rejects and witnesses on top of the generated theorems.
The three independent hand statements are equal by `rfl` to the generated statements. We added the verification inventory script. The decoders of the 16 flat types are complete in the defined meaning.

2026-11-12 review of the close-out unit (new Fable, target `c4e1d74`): REQUEST_CHANGES, only inventory wording and script limits. All proof checks passed.
The inventory fix unit (new Opus session) fixed the inventory script and records. "The decoders of the 16 flat types are complete" in the close-out paragraph above is about the 16 types of the development population.
The target has 1292 SSZ methods. For the decoder, 17 of the 211 `UnmarshalSSZ` are complete. 24 of the 40 flat fixed-size types of the target are not started.
Records: CONTAMINATION section 32, `gen5-close.correction_g5cr1` of `scal/RESULT.json`.

2026-11-12 review of the inventory fix unit (new Fable, target `be21280`): APPROVE, 0 required fixes. It made the inventory counts again and they were the same.
2026-11-12 integration of the `--gen5` work (new Opus session): we merged `claude/ssz-fv-gen5` `be21280` on top of `c29ebdc` (`03cf086`). There were no conflicts.
The "before review" in the `--gen5` generator and close-out paragraphs above is replaced by the following reviews. We do not change those paragraphs.
One review looked at the `--gen5` lemma and generator units together. The technical checks passed, and the verdict was REQUEST_CHANGES for records only. The review of the close-out unit was REQUEST_CHANGES for the inventory only.
The review of the `--gen4` and H6 integration approved that integration.
`lake build` exit 0, 60 new modules built. `P2EncCp` was not built again.
Axioms gate PASS, 9758 declarations. It was byte-identical to the committed record, so we did not write it again.
The declaration comparison against the dump of the close-out review is 0 / 0 / 0. `regen_check.sh` 55/55 SAME. The inventory script output is byte-identical to the committed version.
We did not change `.lean`, generators, checkers, inventory scripts or pinned versions. We did not write to the remote. Records: REPORT section 11, `integration_int7` of `scal/RESULT.json`.

2026-11-12 preparation unit of the flat-encoder work (new Opus session, before review): there are no proofs.
We added the link table `e2e/enc2/link` for `MarshalSSZTo` of 13 flat types. The check is PASS, and the bundle is `c08ac537…`.
The 13 code constants are in `E2eScal/Enc2Code.lean`, and the survey of 16 types is in `scal/enc2-survey.md`. Records: `enc2-prep` of `scal/RESULT.json`.

2026-11-12 lemma unit of the flat-encoder work (new Fable session, before review): we added the statement kind `encFastKindN` of the encoder fast path.
The hand statements of BeaconBlockHeader and Eth1Data are equal by `rfl`, and Checkpoint is bound by an implication.
We added new step lemmas (`EncSteps.lean`), six generated-form examples (`Enc2Ex*.lean`) and the witness `WitVbM`.
We proved that the frame check before `runtime.moveSliceNoCapNoScan` does not branch on the fast path (`EncFrameTest.lean`). There is no contract.
We did not prove the growslice branch. We did not change existing `.lean` files or generators. Records: `enc2-lemmas` of `scal/RESULT.json`.

2026-11-12 generator unit of the flat-encoder work (new Opus session, before review): we added `scalgen.py p2enc --gen6` (`gen/scal/gen6enc.py`).
One run generated the encoder fast path theorems of all 16 flat types. The 16 modules build and pass `kindcheck.py` rule 13.
The 55 old generated outputs are byte-identical. It is not a complete encoder result. Records: `enc2-gen` of `scal/RESULT.json`.

2026-11-12 close unit of the flat-encoder work (new Opus session, before review): we closed the encoder fast path of the 16 flat types (premise `len + SizeSSZ ≤ cap`).
The four independent hand statements are equal by `rfl` to the generated theorems. For all 16 types, witnesses and specification-conformance theorems are bound to the generated theorems.
Inventory: encoder fast path complete 16 / 211, no complete encoder. Records: `enc2-close` of `scal/RESULT.json`.

2026-11-12 inventory fix unit of the flat-encoder work (new Opus session, before review): the review of the close unit was REQUEST_CHANGES (item M1, records only).
We changed the NOT proved column of the inventory script to per-type rules. The BeaconBlockHeader cell had missed the length reject with `cap < len + 112`.
The cells of five types changed. Controls 24/24, the two runs are the same. 0 new declarations. Records: `enc2-close.fix_e2c2` of `scal/RESULT.json`.

2026-11-12 review of the encoder inventory fix unit (new Fable, target `eec1d4f`): APPROVE, 0 required fixes. It compared the 16 inventory cells with the dump and they were the same.
2026-11-12 integration of the flat-encoder work (new Opus session): we merged `claude/ssz-fv-enc2` `eec1d4f` on top of `93dae89` (`e70492d`). There were no conflicts.
The "before review" in the preparation, lemma, generator, close and inventory fix paragraphs above is replaced by the following reviews. We do not change those paragraphs.
The review of the preparation and lemma units and the review of the generator unit were APPROVE. The review of the close unit was REQUEST_CHANGES for only one inventory cell.
The review of the `--gen5` integration approved that integration.
`lake build` exit 0, 64 new modules built. `P2EncCp` was not built again.
Axioms gate PASS, 12177 declarations. It was byte-identical to the committed record, so we did not write it again.
The declaration comparison against the dump of the close-unit review is 0 / 0 / 0. `regen_check.sh` 71/71 SAME. The inventory script output is byte-identical to the committed version.
We did not change `.lean`, generators, checkers, inventory scripts or pinned versions. We did not write to the remote. Records: REPORT section 11, `integration_int8` of `scal/RESULT.json`.

Hold-out H7, the 24 other flat fixed-size types (branch `claude/ssz-fv-flat24`, method frozen at `0923998`): we measured the 24 flat fixed-size types once and closed what was generated.
We committed the opening record `be12791` before we opened the types. We ran `--gen5` once and `--gen6` once per type.
Generated: decoders 7/24, encoders 8/24. The rejects come from byte20, byte4, byte1, bool and the Gwei callee.
The 8 independent hand statements were committed before we opened the generated theorems. Identity `rfl` 8/8.
The kernel checked 8 specification bridges, 7 specification alignments, 14 + 16 witnesses and 8 specification conformances. Negative tests 67/67, Go differential 138/138.
Inventory: decoder complete 18/211 (DepositRequest added), encoder fast path complete 24/211.
6 decoders are partial because they have no Desc checker record. There is no review yet. We did not write to the remote.

Integration of H7 (2026-11-12): we merged H7 (`claude/ssz-fv-flat24` `6f20eef`, approved by the review of H7) on top of `0923998` (`e6b46fd`).
There were no conflicts. The merge tree is the same as the tree of `6f20eef`. 65 new modules were built. `P2EncCp` was not built again.
Axioms gate PASS, 14415 declarations. 0 / 0 / 0 against the dump of the H7 review. `regen_check.sh` 86/86 SAME.
The inventory script was byte-identical to the committed version before S4. S4 added the reject classification text. The totals are the same.
We changed `axioms-gate.json` to the `run` format (S2). We added 12 negative tests (S7): 12/12 as expected (4 controls pass, 8 mutations fail inside the target theorem, 0 timeouts, 0 wrong targets).
The review of the flat-encoder integration approved that integration. We did not write to the remote. Records: REPORT section 11, `integration_int9` of `scal/RESULT.json`.

## 13. Integration and removal of the test-type evidence (2026-11-12)

We merged four branches into `syjn99/ssz-fv-integ`: `claude/ssz-fv-gen7`, `claude/ssz-fv-list-vector-20261112`, `syjn99/ssz-fv-hb` and `syjn99/ssz-fv-enc`.
There was one conflict, in `lean/lakefile.toml`, and we kept both sides. The head is `4ccbccb`.
On `4ccbccb`, the full build with `Gen1cX4` passed (2202 jobs, exit 0).
On `4ccbccb`, the axioms gate over the ten E2e roots passed (18086 declarations, 15099 theorems, nonstandard 0).
Tag `archive/fv-before-workflow` (commit `4ccbccb`) holds the full history and the full tree before the removal.
Commit `57c061d` removed `memopt/`, `k0a/` and `k0b/`.
Commit `84a4747` removed `lean/Gen1cX4` (56 modules) and its lakefile entry, 124 `Fk` modules and `Fk/RtVbl.S`.
It also removed `lean/tools`, `lean/scripts`, `AXIOMS.txt`, `AXIOMS-ALL.txt`, `vcgen/`, `review/`, `negative/` and `semtest/`.
It also removed `gen/x4`, `gen/x5`, `gen/complete` and `gen/wit`.
The removed material was the proofs, witnesses, negative tests, review regression files and generator re-proofs about the Go 1.26.3 test types, and the memory-optimization study.
It was not about Prysm types. The goal is the Prysm generated code, so the test-type evidence is no longer part of the goal.
We kept `lean/Fv`, all of `Fv1`, the 28 `Fk` modules that the Prysm proofs import and all E2e libraries.
We also kept the rest of `gen/`, and `prysm/`, `link/`, `target/` and `cmd/`.
On `84a4747`, `lake build Fv Fv1 Fk E2e E2eAd E2eScal E2eList E2eHb E2eSeg E2eDep E2eDepW E2eEnc E2eDec` in `lean/` gave exit 0 (1841 jobs).
No other check ran on the reduced tree. Not run: negative tests, link checks, declaration drift and an independent review.
