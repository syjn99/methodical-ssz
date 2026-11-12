# Generator change record (hold-out contamination record)

This file records the changes to `gen/scal/scalgen.py`.
For each change, it records if the change came before or after a hold-out was opened.
The hold-out types are in `HOLDOUT-MARKER.json`.

## 1. p2dec statement identity (audit AU-08: no same-statement check): before the hold-out was opened

- Time: 2026-11-10, commit `4581b8f`. `scal/HOLDOUT-OPENED` does not exist. Step S3 (the hold-out evaluation) did not start.
- Before the change: p2dec emitted the statement as frozen text. The proof gave all arguments to `rootdec_seg`. Thus the build passed even with a false premise added to the statement (M1 mutation of the audit, exit 0).
- After the change: only the code premises `k`, `hk`, `hf` are before the colon. The rest is one `∀ …, …` after the colon. The proof is `exact E2eScal.rootdec_seg … hA hB hl`, with no arguments after it.
- What this change checks: that the statement after the colon and the type of the lemma instance are definitionally equal.
- Correction (item M2 of the review of the audit fixes): this change does not catch a premise added before the colon. If the proof does not use that premise, the build passes (`rv-gad-extra-before`, no error). The earlier sentence of this section, "the kernel checks the types of the statement and the lemma instance", was wrong to that extent. Section 2 corrects it.
- Same proposition: in the declaration dump, the type hashes of the two generated theorems did not change (gate jobs 254 and 260, `decl_drift` changes 0). The hash is a structural hash and does not look at binder names.
- Input: only the development set was used. That is the `.S` of the AttestationData and Checkpoint decoders and the IR entries of those two types.
- Files made again: `lean/E2eScal/GenAdDec.lean`, `lean/E2eScal/GenCpDec.lean`. The `regen_check.sh` result is SAME.
- Negative tests: `scal-gad-stmt-extra` and `scal-gcp-stmt-extra` (false premise `(1 : Nat) = 2` added) fail inside the theorem (jobs 258, 259).

## 2. Kind check of the full statement (items M2, S1, S2 of the review of the audit fixes): before the hold-out was opened

- Time: 2026-11-10, commit `094e51e`. `scal/HOLDOUT-OPENED` does not exist. Step S3 did not start. No hold-out file was opened.
- Problem: the check of section 1 looks only after the colon. The p1 mode has no statement check if there is no `--same-as` hand theorem. The hold-out types have no hand theorems.
- New hand module `lean/E2eScal/Kind.lean`: the frozen statement kinds `u64DecAcceptKind C` and `rootDecSegKind C j1 j2 dR dB dS fP fL fC src` (`abbrev`).
- `u64DecAcceptKind_of` and `rootDecSegKind_of` prove each kind from the lemmas `u64dec_accept` and `rootdec_seg`. Thus the kernel matches the body of each kind with the lemma conclusion.
- `lean/E2eScal/KindAnchor.lean`: `sl_kind_anchor`, `ci_kind_anchor`. The P1 kind is equal to the full declared type of the reviewed hand theorems `E2eAd.sl_unmarshal_accept_main` and `E2eAd.ci_unmarshal_accept_main`.
- Generator change: right after each generated theorem `t`, the generator emits `t_kind : ∀ (h : Host), type_of% (@t h) = <kind> …`. The proof is `with_reducible rfl`.
- The type of `@t h` includes all binders before and after the colon. Thus `t_kind` fails if a premise is added, removed or changed at any position. No hand theorem is necessary.
- What this check does not look at: whether the parameters given to the kind (instruction numbers, displacements, offsets) fit that Go type. If they do not fit, the code facts of the proof do not hold and the build fails. This is a property of the proof, not a property of `t_kind`.
- The last line of the generated proof is `with_reducible exact …`. If a constant in the conclusion is wrong, it fails at once without unfolding `Int.toBytes` (S2: before, 300 s wall-clock timeout, now 1.4 s).
- `gen/e2e/negative.py`: puts the `theorem <t>_kind` right after the theorem into the mutation file and into the case range.
- Input: only the development set was used. That is the same three `.S` files and two IR entries as in section 1.
- Files made again: `GenCi.lean`, `GenAdDec.lean`, `GenCpDec.lean`. `regen_check.sh` gave SAME all three times (gate job 294). The type hashes of the generated theorems did not change. The only declaration changes are 11 new declarations (`allow-fixr1.txt`, job 293).
- Negative tests (one gate job for each case group, jobs 288–291): premise added before the colon `scal-gad-stmt-extra-before`, `scal-gcp-stmt-extra-before`, `scal-gci-stmt-extra-before`, added at the start `scal-gad-stmt-extra-first`, `scal-gci-stmt-extra-first`, premise removed `scal-gad-stmt-drop`, conclusion constant `scal-gad-stmt-literal`, kind argument `scal-gad-kind-arg`. All fail inside the case range.
- For all five mutations that add a premise before the colon, the errors are only on the `_kind` line. The theorem itself builds even with those mutations. Thus this check is the only mechanism that catches those mutations.
- Result file `negative-result.json`: 28/28 (6 controls, 22 failures inside the theorem).

## 3. Step 0 of the evaluation session (items N1, N2, N3 of the second review of the audit fixes): before the hold-out was opened

- Time: 2026-11-10, evaluation session. `scal/HOLDOUT-OPENED` does not exist yet. No hold-out file was opened.
- Method freeze: commit `56dfc27`, `Kind.lean` blob `3c9b95b1…`, `scalgen.py` blob `78e3339b…`.
- This step does not change the generator, the lemmas or the kinds.
- N1: `gen/e2e/negative.py` classifies the first errors `Unknown option` and `Case tag … not found` as `wrong_target`. The list is not complete.
- N2: `gen/scal/kindcheck.py` is a check on the reader side. For each generated theorem, it checks from the text that the right side of the `_kind` line is a frozen kind.
- N2 limit: the `_kind` line is generator output. A degenerate right side also builds in Lean. Thus this check is necessary.
- N2 limit: it does not look at whether the kind parameters fit the Go type. Only the code facts of the proof check that.
- N3(a): after a failed build, run `stale_olean.py` before you trust the next pass.

## 4. Hold-out H1 evaluation of ValidatorIndex and BeaconBlockHeader (after opening): evaluation session

- Time opened: 2026-11-10T17:53:24Z (`scal/HOLDOUT-OPENED`, commit `fc8749c`).
- The generator, the lemmas and the kinds were not changed. `kindcheck.py` confirmed that the `Kind.lean` blob is the frozen value.
- The generator ran one time for each type. ValidatorIndex `p1` (job 299), BeaconBlockHeader `p2dec` (job 312).
- The raw outputs `GenVi.lean` and `GenBhDec.lean` were committed with no changes. There are 0 lines of hand changes. Both built as they are.
- Hand files added after the opening: `BhCode`, `ViSpec`, `WitVi`, `BhHead`, `BhAccept`, `BhReject`, `BhSpec`, `BhSpecK`, `WitBhA`, `WitBhR`.
- Most of these hand files are changed text of the development-set hand proofs (`AdHead`, `AdReject`, `AdSpecK`, `WitAdA`, `WitAdR`, `Spec`, `WitCi`).
- Tools added after the opening: `gen/e2e/bhlink.py` (text of `adlink.py`), `gen/e2e/bhdiff.py` and `fve2e/bhcheck` of the temporary Prysm tree.
- These tools are not generators. They do not make proof statements.
- Evidence files added after the opening (item S5 of the review of the H1 evaluation): `lean/E2eScal/BhSpecChecker.lean` (`descterm.py` output), the hand-list additions in `gen/scal/AxiomsScal.lean`, `gen/scal/negcases-holdout.json`.
- These evidence files do not change the method. The generator, the lemmas, the kinds and the classifier are the same.
- Limit: `bh/link/norm` is not a Lake `input_dir`. A lakefile change needs approval, so it was not done.
- The results and limits are in `RESULT.json`.

## 5. Session 10 (INBOX 020): after opening

- The generator, the lemmas, the kinds and the templates were not changed. There is also no template change proposal.
- Hand files added: two theorems in `BhReject.lean`, `WitBhU`, `ViReject`, `WitViR`. Only the code constants were changed from the text of the development-set hand proofs.
- Evidence files added: 15 cases in `negcases-holdout.json`, 7 hand-list entries in `AxiomsScal.lean`.
- Encoder (iii) was attempted with a hand proof and was not proved. The draft was not put in the repository.
- Document changes: the head comment of `BhSpecChecker.lean` (declaration dump is the same), `README.md`, `gen.sh` (two hold-out command lines, not a generator change).

## 6. Session 11 (INBOX 021): after opening

- The generator, the lemmas, the kinds and the templates were not changed.
- No Lean file was added to the repository. All T-9 attempts (finding T-9: the BeaconBlockHeader encoder fast path did not close) are temporary files in the run directory.
- Evidence file changes: one weak case was removed from the total in `negative-holdout.json` (item S1 of the review of session 10). `axioms-gate.json` was replaced with the output for the current SHA.

## 7. Hold-out H2 evaluation of Eth1Data (session 13, INBOX 023): after opening

- Time opened: `H2.opened_utc` in `scal/HOLDOUT-OPENED` (commit `7a5ea61`). Before that, no Eth1Data material was opened.
- Scope: the fast paths of `Eth1Data.UnmarshalSSZ` and `MarshalSSZTo`. `SizeSSZ` was excluded (disclosure of audit finding AU-09, the hold-out limits).
- This session could read the H1 files. It is not independent of the H1 experience.
- The generator, the lemmas, the kinds, the templates and the classifier were not changed.
- The generator ran one time (`p2dec`, job 393). Exit code 2, output 0 bytes.
- Record: `e1/gen-e1dec.raw.txt` (command, exit code, original stderr). The empty `GenE1Dec.lean` was not put in the library.
- Order (item S1 of the first review of H2): the record file was written at 02:02:50Z. Commit `a9918d4` is at 02:04:40Z.
- Between those times, `E1Seg0.lean` was written and built (job 394, 02:04:30Z–02:04:33Z).
- Thus the rule "commit the raw output before hand changes" was kept only in commit order. It was not kept in work order.
- There is no effect. There is no generated output to change.
- Cause: the memmove source of DepositRoot is `buf + 0`. The code has no `add $src,%rbx`.
- The frozen template `rootDecMid` requires this instruction. The generator stops at the first field and does not emit BlockHash either.
- Proposal (not done): give `rootDecMid` a variant for source 0 and let `p2dec` accept a block with no `add`.
- This proposal is a method change. It was not done in this evaluation. The generator coverage for this type is 0/2 fields.
- The inline read of DepositCount (instructions 47–49) has no method template (item S2 of the first review of H2).
- Thus, even with the proposed variant, the generator covers only the two root segments (instructions 13–36, 50–74).
- Parts replaced by hand proofs (copied text):
  - `E1Seg0.lean`: the statement and proof text of `rootdec_seg` with the `add` step removed. It is not part of the frozen method.
  - BlockHash segment: the frozen `rootdec_seg` was instantiated by hand (the generated text shape of `GenBhDec` was copied).
  - `E1Accept` (text of `BhHead`, `BhAccept`), `E1Reject` (`BhReject`), `E1Spec` (`BhSpec`), `E1SpecK` (`BhSpecK`), `WitE1A` (`WitBhA`), `WitE1R` (`WitBhR`).
- Hand files added after the opening: `E1Code`, `E1Desc`, `E1Seg0`, `E1Accept`, `E1Reject`, `E1Spec`, `E1SpecK`, `WitE1A`, `WitE1R`.
- Generated file: `E1SpecChecker.lean` (`descterm.py` output, one path line added to the head comment).
- Source of the checker json `e1/prysm_v1alpha1.Eth1Data.desc.json` (item S3 of the first review of H2): it was copied from a reviewer temporary directory of a different run.
- It is the temporary copy `desc/orig/` of the fifth phase 1c review. It is outside this repository.
- sha256 `6064a3dc…782b` is equal to record 74 (`Eth1Data`, PASS) of `gen/desc/results/main.result.json` (counted again in session 14).
- The hand Desc (`E1Desc.lean`, commit `c43359b`) was committed before the checker Desc was made or printed.
- Tools added after the opening: `gen/e2e/e1link.py` (text of `bhlink.py`), `gen/e2e/e1diff.py` (text of `bhdiff.py`), `fve2e/e1check` of the temporary Prysm tree.
- Evidence files added after the opening: `gen/scal/negcases-h2.json`, 15 hand-list entries and three imports in `AxiomsScal.lean`.
- Session 14 (item S6 of the first review of H2) added 2 negative tests: `e1-rc-stmt-size`, `e1-witr-stmt-len`. Both failed inside the theorem (jobs 432, 433).
- `kindcheck.py` was not run. There is no generated theorem to check.
- The stack check of the encoder (`MarshalSSZTo`) has the shape `lea -0x8(%rsp),%r12; cmp 0x10(%r14),%r12; jbe` (the same as T-9).
- Per INBOX 023 step 3, it was not attempted. The budget waits for a user decision.
- Limit: `e1/link/norm` is not a Lake `input_dir`. A lakefile change needs approval, so it was not done.

## 8. SG-1 extension (generator change for finding SG-1, a field at SSZ offset 0, after both hold-outs were opened): development work, not a hold-out

- When: 2026-11-11, after base commit `48b74b6`. This is after both H1 and H2 were opened.
- What: the generator now accepts a 32-byte decode segment at source offset 0.
- New Lean files: `P2DecZ.lean` (template `rootDecMidZ`, lemma `rootdec_seg_z`), `KindZ.lean` (kind `rootDecSegZKind`).
- `rootdec_seg_z` generalizes the text of the hand file `E1Seg0.lean`. The definition and proof text differ only in names.
- `Kind.lean`, `P2Dec.lean` and the statements of the existing theorems were not changed. `decl_drift` shows only 19 ADDED.
- `scalgen.py p2dec`: selects the shape from the instruction after the buffer reload. It does not look at type names or field names.
- If it is `add $X,%rbx`, it is the existing shape. If it is `mov $0x20,%ecx`, it is the offset-0 shape. Anything else is a mismatch.
- Field rule: each field is matched separately. A failure of one field does not stop the check of the later fields.
- The output is complete or absent. If only part matches, the exit code is 3 and stdout is empty.
- If you give `--partial-out`, it writes only the matched fields to a file. The file head records `PARTIAL OUTPUT` and the missing fields.
- If no field matches or segments overlap, the exit code is 2 and nothing is written.
- `kindcheck.py`: accepts `rootDecSegZKind` (8 arguments). It accepts it only when `KindZ.lean` is the frozen blob.
- Contamination: Eth1Data is development data for this extension. The extension was made by looking at the `.S` of Eth1Data.
- Thus the Eth1Data result is not a hold-out result. No new hold-out type was named or opened.
- The H1 and H2 results in §4–§7 above are results from before the extension. They stay as they are.
- Record before the extension: the Eth1Data run of the frozen generator (blob `78e3339`) gave exit code 2, 0/2 fields (`a9918d4`, approval `48b74b6`).
- This record stays as a historical negative result. `gen/scal/p2dec_test.py` reproduces the same result.
- After the extension: the new generator emits 2/2 root fields for Eth1Data (`GenE1Dec.lean`, output with no hand changes).
- The inline read of DepositCount still has no template.
- Regression: GenCi, GenVi, GenAdDec, GenCpDec and GenBhDec were made again with the new generator. All are byte-identical.
- Tests: `scal/sg1-gen-test.json` (10/10), `scal/negative-sg1.json` (7/7). The generalization claim covers only the scope of these tests.

## 9. T-9 stream (BeaconBlockHeader encoder fast path, finding T-9, user instruction, 2026-11-11): after opening

- The generator, the lemmas, the kinds and the templates were not changed. `Fk/*` and the contracts were not changed either.
- This work is a hand proof. It is not a generator result. It is not included in the hold-out claims.
- The author session read the H1 and H2 files and the T-9 records. It is not an independent sample.
- Lean files added: `StackGuard.lean`, `BhEncHead.lean`, `BhEncRoots.lean`, `BhEncMain.lean`, `BhSpecM.lean`, `WitBhM.lean`.
- The bodies of segment parts A1 (directives 0–35) and A2 (directives 36–61) of `BhEncHead.lean` came from the session 11 temporary file `Split3.lean`. Two places were changed: the guard branch and the length goal.
- `WitBhM.lean` is text of `E2e/WitCpM.lean`. `BhSpecM.lean` is text of `E2e/CpSpecM.lean`.
- Evidence files added: `gen/scal/negcases-t9.json`, `scal/negative-t9.json`, `gen/e2e/bhmdiff.py`, `bh/bhmcheck-main.go.txt`, `bh/differential-enc*.json`.
- 11 names were added to `AxiomsScal.lean`. `axioms-gate.json` was replaced with the output of the current tree.
- Proposal (not done): a change that fits the encode template to this three-root-block shape. `scalgen.py` and `Kind.lean` are unchanged.

## 10. Session 15 integration (INBOX 027): after opening

- The T-9 stream and the SG-1 extension stream were merged into this branch. There are no new proofs, generator changes or template changes.
- Both streams added a section 8 to this file. The SG-1 Lean comments point to section 8, so SG-1 is section 8. T-9 became section 9.
- `kindcheck.py` was changed (item S2 of the review of the SG-1 extension). It rejects a file with a `PARTIAL OUTPUT` head. This is a change of the reader-side checker.
- This change does not change the generator output, the kinds or the lemmas. The 6 existing generated files still PASS.
- 8 cases were added to `gen/scal/negcases-sg1.json` (item S3 of the review of the SG-1 extension). They target `rootdec_seg_z` and the BlockHash segment.

## 11. Hold-out H3 evaluation (BlobIdentifier, DepositMessage): after opening

- Time opened: `H3.opened_utc` in `scal/HOLDOUT-OPENED` (commit `782a41b`, 2026-11-11T04:26:30Z).
- Method freeze: commit `dda707c`. The 7 blobs of the freeze record and the `lean/E2eScal` tree id were counted again. All are the same.
- Types: `v1alpha1.BlobIdentifier` (class Z), `v1alpha1.DepositMessage` (class N). The scope is `UnmarshalSSZ` only.
- The evaluation session did not make generators, kinds or template lemmas. It could read the H1, H2, SG-1 and T-9 files.
- The generator, `kindcheck.py`, `Kind*.lean`, the template lemma modules, `Fk/*`, the contracts and the existing statements were not changed.
- The generator ran one time for each type (jobs 11, 12). Both exited 0 and stderr is empty.
- The raw outputs `GenBiDec.lean` and `GenDmDec.lean` were committed with no changes (`936446b`). There are 0 lines of hand changes.
- `kindcheck.py` gives PASS for both files (job 13). Both files built as they are (job 14).
- Generator coverage: 1 of the 2 BlobIdentifier fields, 1 of the 3 DepositMessage fields.
- The generator reads only 32-byte `[]byte` fields (`scalgen.py` `ir_roots`). Thus it does not look at the 48-byte PublicKey.
- The inline uint64 reads (Index, Amount) have no method template. This is a limit recorded before H3.
- Hand lemma: new H3 module `DmSeg0.lean` (`E2eScal.H3.bytes48dec_seg_z`).
- Its text is the text of `rootDecHead`, `rootDecMidZ` and `rootdec_seg_z` with `32` changed to `48`. It is not part of the frozen method.
- Hand files and source text: `BiAccept`, `DmAccept` (`E1Accept`), `BiReject`, `DmReject` (`E1Reject`), `BiSpec`, `DmSpec` (`E1Spec`).
- Continued: `BiSpecK`, `DmSpecK` (`E1SpecK`), `WitBiA`, `WitDmA` (`WitE1A`), `WitBiR`, `WitDmR` (`WitE1R`), `BiDesc`, `DmDesc`, `H3Code`.
- The two accept theorems call the generated segment theorems directly (`bi_dec_BlockRoot_seg`, `dm_dec_WithdrawalCredentials_seg`).
- Generated files: `BiSpecChecker.lean`, `DmSpecChecker.lean` (`descterm.py` output, one path line added to the head comment).
- Source of the checker json: the temporary copy `desc/orig/` of the fifth phase 1c review (the same as H2). The sha256 is equal to the `main.result.json` record.
- The hand Desc (`11babc9`) was committed before the checker Desc was made or printed.
- Tools added after the opening: `gen/e2e/h3link.py` (text of `e1link.py`), `gen/e2e/h3diff.py` (text of `e1diff.py`), `h3/h3check-main.go.txt`.
- Evidence files added after the opening: `gen/scal/negcases-h3.json`, 87 hand-list entries and 8 imports in `AxiomsScal.lean`.
- These tools and evidence files do not change the method.
- Proposal (not done) P-H3-1: an inline uint64 read template.
- The shape for P-H3-1 is `mov dB(%rsp),%rcx; mov src(%rcx),%rcx; mov %rcx,f(%rdx)`. It is the same in both types.
- Proposal (not done) P-H3-2: make the size of the segment template a parameter and let `ir_roots` also read 48-byte vectors.
- With P-H3-2, the PublicKey segment (instructions 13–36) becomes a generation target. It was not done in this evaluation.
- The two proposals are method changes. Thus those fields are reported as not covered by the generator.
- Limit: `h3/link/norm` is not a Lake `input_dir`. A lakefile change needs approval, so it was not done.
- Correction (integration of H3 and the encoder reuse work, item S1 of the review of H3): the curator decided reading A3 (class N counts the type's own fields) after seeing the candidate list.
- At that time, nobody opened the method code. The source is a controller confirmation file outside the repository.
- In a different reading (transitive fields), the class N type is `ProposerSlashing`. That reading was not used.
- A literal reading of A1 (which types already exist in the tree) gives no candidates. The confirmed A1 is the narrow reading of `HOLDOUT-OPENED`.
- Correction (item S2 of the review of H3): the existing file `gen/scal/AxiomsScal.lean` was extended (+97 lines, −0 lines). It is the axioms hand list, not a method file.
- Correction (item S3 of the review of H3): `BiSpecChecker.lean` and `DmSpecChecker.lean` are "Do not edit" files. One head line was added by hand.
- That head records the fixed directory of `descterm.py`. The files are not there. They are in `e2e/h3/`.
- Correction (item S6 of the review of H3): the checker json came from a temporary copy of a different review. Only the sha256 binds it to the record. The repository alone cannot make it again.

## 12. Integration of H3 and the encoder reuse work: after opening

- H3 `75166e4` (approved by the review of H3) and the encoder reuse work `ad15fbc` (approved by its review) were merged with `--no-ff`.
- The merge commits are `500571c` (H3) and `c10daf9` (encoder reuse work). There are no new proofs, generator changes or statement changes.
- The encoder reuse work does not use the code of the H3 types. Its author saw only the `h3/` file names and 5 gate records (item S5 of the review of the encoder reuse work).
- Generator rerun: `regen_check.sh` ran in scratch as an integration check. It is not counted in the generator run count of the H3 evaluation (one time for each type).

## 13. Lemma work for the `--gen2` mode: after H3, development work, not a hold-out

- This work was done after the H3 evaluation and the two integrations (H3 with the encoder reuse work, and the optimization test OPT-R1). The base commit is `71161fa`.
- BlobIdentifier and DepositMessage are now development data. No hold-out claim is made with these two types.
- The author session is a new Fable session and is the direct author. This session did not make the generator.
- This session read the `.S` of the three decoders, the hand proofs, the generated files and the H3 records.
- Only new modules were added: `SegN`, `KindN`, `SegNRel`, `U64Inline`, `KindU64`, `Gen2Examples`, `Compose`, `Gen2ComposeEx`.
- The existing `.lean` files, `scalgen.py`, `kindcheck.py`, `gen.sh`, the H3 generated files and the H3 records were not changed.
- The proof generator is unchanged. Thus the generator coverage (finding SG-2: only 32-byte byte-vector fields) did not change.
- A temporary script made the text of `SegN.lean` and `KindN.lean` from `P2Dec.lean`, `P2DecZ.lean`, `Kind.lean` and `KindZ.lean`.
- That script changes the size `32` to the parameter `n`. The script was not committed.
- `Gen2Examples.lean` was also written with a temporary script. It is not output of `scalgen.py`. It counts as a hand example.
- The inline uint64 shape was first read at three sites. The temporary registers are different: rsi for Eth1Data, rcx for the other two.
- The text of P-H3-1 (§11) records only rcx. That text fits only the two H3 types.
- The sizes of the segment lemma (L1) are only 32, 48 and 96. The development data has no 96-byte site. 96 was not checked in real code.
- The inline uint64 lemma (L2) has 12 registers. The observed ones are two: rsi and rcx. The receiver must be rdx.
- The composition lemmas (L3) are three pieces and one example. There is no general combinator that takes a segment list. The frame handles only `0x20`.
- There is no generality claim. Whether it carries over to other types was not measured.
- Evidence file added: `gen/scal/negcases-gen2.json`. `gen/e2e/negative.py` was not changed.
- The axioms gate ran into a temporary JSON. The committed `axioms-gate.json` was not changed.
- There is no independent review yet.

## 14. Generator work for the `--gen2` mode: generator change after H3, development work, not a hold-out

- After the H3 evaluation, this work changed the proof generator `gen/scal/scalgen.py`. The base commit is `6c62a49`.
- The author session is a new Opus session. It did not write the lemmas (section 13). It also does no review.
- The inputs are development data only: the `.S`, IR, hand proofs and generated files of Eth1Data, BlobIdentifier and DepositMessage.
- BlobIdentifier and DepositMessage are in-sample data for the `--gen2` mode. There is no hold-out claim before H4.
- What changed: the optional mode `p2dec --gen2` was added. The output of the default mode is the same, character for character.
- `--gen2` classifies all fields in the IR. It covers only byte vectors 32, 48, 96 and inline uint64.
- 32-byte fields use the old theorem text. 48 and 96 use `bytesdec_seg(_z)`, uint64 uses `u64dec_inline_seg`.
- Other fields are reported as "not covered: reason". It does not guess a theorem.
- `--gen2 --compose` was also added. If all fields are covered, it writes the full accept theorem.
- The only statement check of the composed theorem is the `_type` identity with the hand theorem. There is no kind for that theorem.
- For a type with no hand theorem (hold-out), there is nothing to check the composed statement against. This is an open gap.
- The generator ran one time for each type (jobs 05, 11). The raw output was committed first with no changes.
- Only new files were written: `Gen2E1Dec`, `Gen2BiDec`, `Gen2DmDec`, `Gen2BiAccept`, `Gen2DmAccept`, `Gen2E1Accept`.
- The H3 raw outputs `GenBiDec.lean`, `GenDmDec.lean` and the H3 records were not changed.
- The outputs of the 8 old generator commands are byte-identical (`regen_check.sh` SAME, jobs 02, 17).
- `kindcheck.py` accepts the three new kinds only together with the frozen blobs. It reports the `_type` identity separately as "identity-checked".
- The lemma modules were not changed. The verdict of the review of the `--gen2` lemma work is APPROVE, with no required fixes.
- The development data has no 96-byte field. The 48-byte add shape had only a text check of a synthetic `.S`. It is not a kernel check.
- There is no generality claim. There is no independent review yet.

## 15. Fix work for the `--gen2` mode: second generator change after H3, before the H4 freeze, development work

- The verdict of the review of the `--gen2` generator work is REQUEST_CHANGES. The two required fixes are documents. There was no proof defect.
- This work is the second generator change after H3. It was done before the generator was frozen for H4.
- The author session is a new Opus session. It did not write the generator work or the lemma work. It also does no review.
- Correction to section 14 (item S4 of that review): there were scratch test runs before "one time for each type" (jobs 01, 09 of the generator work).
- The committed runs are jobs 05 and 11. The scratch outputs were not committed.
- Changed: the `_type` rule of `kindcheck.py`. It accepts the rule only for composed theorems and rejects it if the right side is a generated name.
- Changed: a `--gen2 --partial-out` file is a valid Lean module. `kindcheck.py --partial` gives exit 3.
- Changed: if `--compose` has no `--same-as`, it writes an `UNCHECKED STATEMENT` mark. `--same-as-prop` was added.
- The inputs are development data only. BeaconBlockHeader (an H1 type) is now also in-sample data for the `--gen2` mode.
- `Gen2BhDecPartial.lean` is the raw output of one generator run (job 05). A scratch test of the same command came before it (job 02).
- The default mode and the committed generated files did not change: `regen_check.sh` 15/15 SAME (job 13).
- There is no generality claim. There is no independent review yet.

## 16. Hold-out H4 evaluation (Deposit_Data, PendingPartialWithdrawal): after opening

- Time opened: `H4.opened_utc` in `scal/HOLDOUT-OPENED` (commit `9d338fa`, 2026-11-11T08:53:45Z).
- Method freeze: commit `eacf0fb`. The 15 blobs of the freeze record and the `lean/E2eScal` and `lean/Fk` tree ids were counted again. All are the same.
- Types: `v1alpha1.Deposit_Data` (class A), `v1alpha1.PendingPartialWithdrawal` (class B). The scope is `UnmarshalSSZ` only.
- The evaluation session did not make the `--gen2` generator, checkers, kinds or lemmas. It could read the files of the earlier units.
- Disclosed similarity (selection record H4-A5): Deposit_Data is DepositMessage with a 96-byte Signature added. 3 of its fields are close to the sample.
- The hand Desc (`2daf204`) was committed before the checker Desc was printed.
- The hand statements `H4.dd_accept_stmt` and `H4.pw_accept_stmt` (`d7e3304`) were committed before the generator ran.
- The hand statements were written from the IR `go_fields`, the SSZ layout, the frame facts of the `.S` and the shapes of the Bi/Dm/E1/Bh hand theorems.
- The link table was made before the hand statements. The statements had to use the frame facts of the `.S`. The generator did not run.
- The segment generator (S) and the compose generator (C) ran one time each for each type (jobs 12, 13, 16, 17). They did not run again with other options.
- The raw output `Gen2DdDecPartial.lean`, two summary JSON files and three stderr records were committed first with no changes (`43a0847`, `76b66ba`).
- There are 0 lines of hand changes. One stderr (Deposit_Data (S)) contains a run-directory path, so it was not committed.
- `scalgen.py`, `kindcheck.py`, `Kind*.lean`, the lemma modules, `Fk/*`, the contracts and the existing statements were not changed.
- New hand lemma: `H4.bytes32dec_seg_nop` (`DdSegNop.lean`). It adds one `nop` step to the text of `bytesdec_seg` (n = 32).
- A temporary script made that text from `SegN.lean`. The script was not committed. It is not part of the method.
- Tools added after the opening: `gen/e2e/h4link.py` (text of `h3link.py`), `gen/e2e/h4diff.py` (text of `h3diff.py`), `h4/h4check-main.go.txt`.
- Evidence files added after the opening: `gen/scal/negcases-h4.json`, 7 imports and 46 hand-list entries in `AxiomsScal.lean`.
- The checker json came from the temporary copy of the fifth phase 1c review. The sha256 is equal to the `main.result.json` record.
- `DdSpecChecker.lean` and `PwSpecChecker.lean` are `descterm.py` output. One path line was added to the head by hand (the same as H3).
- Proposal (not done) P-H4-1: allow a `nop` before `callq runtime.makeslice` at the head of a 32-byte segment.
- With P-H4-1, the WithdrawalCredentials of Deposit_Data (instructions 47–72) becomes a generation target.
- Proposal (not done) P-H4-2: read a different shape of the inline uint64 read.
- That shape is `mov 0x8(%rbx),%r8; mov %r8,0x10(%rax)`. Different earlier instructions reload the two base registers.
- Proposal (not done) P-H4-3: a segment template that covers delegated overlay fields (calls) with the existing function specifications `ViUAccC` and `EpUAccC`.
- The three proposals are method changes. Thus those fields are reported as not covered by the generator.
- Tool limit: the code mutation of `negative.py` changes only names inside that module.
- If the statement is an `abbrev` of a different module, the control also fails (`dd-acc-control`, job 46). Those four cases were retracted.
- Limit: `h4/link/norm` is not a Lake `input_dir`. A lakefile change needs approval, so it was not done.
- There is no generality claim. There is no independent review yet.

## 17. Integration of the `--gen2` work and H4: correction after review

- The text of the sections above is not changed. This section is an appended correction.
- In sections 13–16, "There is no independent review yet" is replaced by the reviews below.
- The review of the `--gen2` lemma work: APPROVE (`6c62a49`). The review of the `--gen2` generator work: REQUEST_CHANGES (`cd47028`, documents only). The review of the `--gen2` fix work: APPROVE (`eacf0fb`). The review of H4: APPROVE (`fae7d6f`).
- Correction to section 16 (item S2 of the review of H4): the evaluator read `Gen2DmAccept.lean` before writing `dd_accept_stmt`.
- That file is the generated composed theorem of the sibling development type DepositMessage. It is a file of a different type, so it is allowed.
- Result (C) was rejected for both types. Thus no identity result depends on this reading.
- Correction to section 16 (S1): of the 3 covered fields, PublicKey and Amount are close to the sample. Only Signature is outside the sample.
- The uncovered WithdrawalCredentials has the 32-byte shape close to the sample. It failed at the padding `nop` (finding SG-3: `--gen2` coverage gaps on H4).
- Correction to section 15 (item S5 of the review of the `--gen2` fix work): the job numbers 01, 02, 05, 09, 11, 13 in section 15 are gate jobs of that session.
- Those logs are not in the repository. The numbers are only labels. The evidence in the repository is the committed output and the `regen_check.sh` result.
- Correction to section 16 (S7): the A2 alternative reading of the selection record was added to `H4.review_h4_r1_correction` in `scal/HOLDOUT-OPENED`.
- The `regen_check.sh` of the integration check also ran the generator command of `Gen2DdDecPartial.lean` two more times (scratch).
- This is not an H4 run. The H4 rule "one time for each type" applies to the evaluation session. The result is SAME.
- The proposals (not done) stay as they are: P-H4-1, P-H4-2, P-H4-3, and the kind of the composed statement.
- Items S1–S4 of the review of the `--gen2` fix work (`kindcheck.py` changes) are also proposals (not done). They came after the H4 freeze, so they were not applied.
- There is no generality claim. There is no review of this integration itself yet.

## 18. Lemma work for the `--gen3` mode: after H4, development work, not a hold-out

- This work was done after the H4 evaluation and the integration of the `--gen2` work and H4. The base commit is `6a78c59`.
- Deposit_Data and PendingPartialWithdrawal are now development data. No hold-out claim is made with these two types.
- The author session is a new Fable session and is the direct author. This session did not make the generator.
- This session read the H4 records, the review of H4 and the text of the evaluator's uncommitted proof attempts.
- This session also read all `.S` files and hand proofs of the development decoders.
- Only new modules were added: `CallDec`, `CallDecRel`, `KindCall`, `U64RR`, `SegNPad`, `PwAccept`, `WitPwA`, `BhHeadG3`.
- The example and kind modules are also new files: `Gen3Examples`, `KindAccept`, `KindAcceptRel`.
- The existing `.lean` files, `gen/scal/*`, the contracts, the statements, the ELF and the tool chain were not changed.
- The hand statement `pw_accept_stmt` in `H4Stmt.lean` is unchanged. The type of the proved theorem is that statement.
- The proof generator is unchanged. Thus the generator coverage (SG-3) did not change.
- The call sites were read first: there are 9. Of these, 7 are uint64 overlay calls and 2 are pointer-field calls.
- The call-block lemma fits all 7 sites. The argument setup handles only the three observed shapes.
- Thus the call-block lemma (L1) is partial reuse. A new register choice is "not covered".
- The callee functions are used only in the form of the existing function specifications. `U64CalleeAcc` is equal by `rfl` to the four existing specifications.
- 13 byte segments were read. There is 1 padding variant: a `nop` before the makeslice call.
- A temporary script made the proof text of `SegNPad.lean` from `SegN.lean`. The script was not committed.
- The development data has no 48-byte or 96-byte site of the padding shape. It also has no padding in the offset-0 shape.
- The two-instruction uint64 shape has 1 site. The base registers are fixed as rbx and rax.
- `Gen3Examples.lean` and `KindCall.lean` were also written with temporary scripts. They are not output of `scalgen.py`.
- The composed-statement kind `decAcceptKind` handles only the frame `0x20` and byte/uint64 fields.
- That kind is bound by `rfl` to the three generated composed theorems and to `dd_accept_stmt`. All four are development data.
- There is no kind for a composed statement with call fields.
- There is no generality claim. Whether it carries over to other types was not measured.
- Evidence files added: `scal/negcases-gen3.json`, `scal/negative-gen3.json`. `gen/e2e/negative.py` was not changed.
- The negative tests count 37 of 38 cases. 1 kind mutation ended with a heartbeat timeout. It does not count as passed.
- The axioms gate ran into a temporary JSON. The committed `axioms-gate.json` and `AxiomsScal.lean` were not changed.
- The generator side of the proposals P-H4-1, P-H4-2, P-H4-3 was not done. It is the work of the next unit.
- There is no independent review yet.

## 19. Generator work for the `--gen3` mode: generator change after H4, development work, not a hold-out

- After the H4 evaluation, this work changed the proof generator `gen/scal/scalgen.py`. The base commit is `f5c5f52`.
- The author session is a new Opus session. This session did not write the lemmas and does no review.
- The inputs are development data only: PendingPartialWithdrawal, Deposit_Data, BeaconBlockHeader, AttestationData.
- The coverage of these four types is in-sample. No transfer claim is made. There is no hold-out claim before H5.
- The new shapes are only behind `--gen3`. The default mode and `--gen2` outputs are byte-identical (`regen_check.sh` 16/16 SAME).
- This session read the example file `Gen3Examples.lean` of the lemma unit and matched the generator text to it.
- Of the 34 generated texts, 33 are byte-identical to the examples. 1 differs only in line breaks.
- It ran one time for each type. First there was a scratch test run (job 01). After that came the run to commit (job 06).
- The raw output was committed with no changes before the build (`977db81`).
- Deposit_Data compose run 1 was a syntax error: the generator wrote a doc comment before `set_option … in`.
- That raw output was moved to `scal/gen3/Gen3DdAccept.run1-parse-error.lean.txt` and is kept as it is. Run 2 of the fixed generator is `Gen3DdAccept2.lean`.
- The accept theorems of PendingPartialWithdrawal and BeaconBlockHeader are hand compositions (`PwAcceptG3`, `BhAcceptG3`). They call the generated theorems.
- Generator item of the review of the `--gen3` lemma work (APPROVE): the trailing `nop` (BeaconBlockHeader.ParentRoot, Checkpoint.Root) is recorded as not covered.
- Items S1–S4 of the review of the `--gen2` fix work were put into `kindcheck.py`. H4 is finished, so they can be changed now.
- There is no generality claim. There is no speed claim either. There is no independent review yet.

## 20. Hold-out H5 evaluation (SyncCommitteeMessage, PendingConsolidation): after opening

- Time opened: `H5.opened_utc` in `scal/HOLDOUT-OPENED` (commit `3762644`, 2026-11-11T11:25:14Z).
- Method freeze: commit `6dc0e2a`. The 5 blobs and 4 tree ids of the freeze record were counted again. All are the same.
- Types: `v1alpha1.SyncCommitteeMessage` (class C), `v1alpha1.PendingConsolidation` (class D). The scope is `UnmarshalSSZ` only.
- The evaluation session did not make the `--gen3` generator, checkers, kinds or lemmas. It could read the files of the earlier units.
- Disclosed similarity (selection record H5-A3): by field kinds, the two types are close to the sample. Only the order of the kinds is new.
- The hand Desc (`08adf1d`) was committed before the checker Desc was printed.
- The hand statements `H5.sm_accept_stmt` and `H5.pc_accept_stmt` (`3c4625c`) were committed before the generator ran.
- The link table (`8f3aac7`) was made before the hand statements. The statements had to use the frame facts of the `.S`. The generator did not run.
- Generators (S) and (C) ran one time each for each type (jobs 09, 10, 14, 15). They did not run again with other options.
- The raw output was committed first with no changes (`fe2f266`, `dea6b37`). There are 0 lines of hand changes.
- The two stderr files of (S) contain run-directory paths, so they were not committed. The summary JSON was committed.
- `gen/scal/*`, the kind and lemma modules, `Fk/*`, the contracts and the existing statements were not changed.
- Thus `gen/scal/AxiomsScal.lean` was not extended. The axioms gate counts all declarations. The new declarations are included.
- The negative case file was put outside `gen/scal/`: `h5/negcases-h5.json`. During the run, the same bytes were in `gen/scal/` before the commit.
- Only new H5 modules were added: `H5Code`, `H5Stmt`, `SmDesc`, `PcDesc`, `SmSeg`, `SmAccept`, `PcAccept`, `Sm*`/`Pc*`, `Wit*`.
- New hand lemmas: `bytes32dec_seg_rax`, `sm_vi_arg`, `calldec_nop_seg`. Only some instructions were changed from the existing proof text.
- Tools added after the opening: `gen/e2e/h5link.py` (text of `h4link.py`), `gen/e2e/h5diff.py` (text of `h4diff.py`), `h5/h5check-main.go.txt`.
- The checker json came from the temporary copy of the fifth phase 1c review. The sha256 is equal to the `main.result.json` record.
- Proposal (not done) P-H5-1: in the second block of a 32-byte segment, allow the shape that reloads the receiver into rax.
- With P-H5-1, SyncCommitteeMessage.BlockRoot (instructions 47–81) becomes a generation target.
- Proposal (not done) P-H5-2: read the call-argument shape where the receiver is already in rax (instructions 82–87).
- The generator read that site as the "first field shape" and rejected it because the SSZ offset is not 0. The reject is correct. The shape does not exist.
- Proposal (not done) P-H5-3: allow a padding `nop` between `callq` and `test %rax,%rax`.
- With P-H5-3, PendingConsolidation.TargetIndex (instructions 48–58) becomes a generation target.
- Proposal (not done) P-H5-4: composition for types with call fields. This is a limit known before the freeze.
- The four proposals are method changes. Thus those fields are reported as not covered by the generator.
- The generated `_call` theorems have the premise `hC : U64CalleeAcc`. The accept proofs discharge it with the proved `sl_uacc_holds` and `vi_uacc_holds`.
- Limit: `h5/link/norm` is not a Lake `input_dir`. A lakefile change needs approval, so it was not done.
- There is no generality claim. There is no independent review yet.

## 21. Integration of the `--gen3` work and H5: correction after review

- The text of the sections above is not changed. This section is an appended correction.
- In sections 17–20, "There is no independent review yet" is replaced by the reviews below.
- The review of the `--gen2` and H4 integration: APPROVE (`6a78c59`). The review of the `--gen3` lemma work: APPROVE (`f5c5f52`). The review of the `--gen3` generator work: APPROVE (`6dc0e2a`). The review of H5: APPROVE (`1fec11e`).
- Correction to section 18 (item S1 of the review of the `--gen3` lemma work): "There is 1 padding variant" is correct only for the head and middle of a segment.
- There is a second `nop` site in the pointer tail: BeaconBlockHeader.ParentRoot (instructions 113–115), Checkpoint.Root (75–77).
- Those sites were observed and not covered. The `--gen3` section of `gen/scal/README.md` already records this.
- Correction to section 19 (item S4 of the review of the `--gen3` generator work): the job numbers 01, 06 in section 19 are gate jobs of that session.
- Those logs are not in the repository. The numbers are only labels. The evidence in the repository is the committed raw output and the `regen_check.sh` result.
- Correction to section 20 (item S5 of the review of H5): job 22 tested a candidate fix separately, together with a reproduction. It is not an attempt at the obligation itself.
- The evaluator's declaration-comparison control was an edit of the dump text. The review of H5 ran the planted control at the Lean level.
- Correction to section 20 (S7): the A5 alternative reading of the selection was added to `H5.review_h5_r1_correction` in `scal/HOLDOUT-OPENED`.
- The `regen_check.sh` of the integration check also ran the generator commands of the two H5 (S) partial outputs two more times (scratch).
- This is not an H5 run. The H5 rule "one time for each type" applies to the evaluation session. The result is SAME.
- The proposals (not done) stay as they are: P-H5-1, P-H5-2, P-H5-3, P-H5-4.
- Item S2 of the review of the `--gen3` generator work (`kindcheck.py` change) is also a proposal (not done). It is a checker change, so the integration did not do it.
- There is no generality claim. There is no review of this integration itself yet.

## 21. Lemma work for the `--gen4` mode: after H5, development work, not a hold-out

- This work was done after the H5 evaluation and the review of H5. The base commit is `1fec11e`.
- SyncCommitteeMessage and PendingConsolidation are now development data. No hold-out claim is made with these two types.
- The author session is a new Fable session and is the direct author. This session did not make the generator.
- This session read the H3, H4 and H5 records, the review of H5 and the handoff document of the `--gen3` work.
- This session read all `.S` files and hand proofs of the 10 development decoders.
- A survey table was made first: `scal/gen4-survey.md`. A temporary script made the table from the `.S` text.
- Only new modules were added: `NopView`, `StepK`, `KindStep`, `CallReg`, `SegReg`, `SegRegZ`, `KindSegReg`, `G4Rel`.
- There are more new modules: `Gen4Examples`, `SmAcceptG4`, `PcAcceptG4`, `G4DepCheck`, `HeadN`, `HeadRel`.
- The existing `.lean` files, `gen/scal/*`, the contracts, the statements, the ELF and the tool chain were not changed.
- The two hand statements in `H5Stmt.lean` are unchanged. The types of the two newly proved theorems are those statements.
- The proof generator is unchanged. Thus the generator coverage (findings SG-3 and SG-4: generator coverage gaps on H4 and H5) did not change.
- There is one padding mechanism: a program window `q` and `eraseNop q = template`. There is no `nop` position parameter.
- All three observed `nop` sites are cases of this mechanism.
- There is no general transfer theorem from the dense lemmas to the window lemmas.
- Reason: `callq` pushes the address of the next instruction onto the stack. In the real program, that is the address of the `nop`.
- Thus the window lemmas were proved directly. The earlier shape-specific lemmas were proved again as cases of them.
- The per-instruction step lemmas take the registers as parameters. Each step has one kind.
- The Go ABI fixes the entry registers of a call block. The shape of the callee specification `U64CalleeAcc` is unchanged.
- The receiver registers of a byte segment are a finite set: `rX` is rdx, rsi. `rY` is rax, rcx, rdx, rsi, rdi.
- This set and the sizes 32, 48, 96 are limits of the proof method. They are not limits of the code shape.
- The window lemma for the offset-0 shape was also proved. No variant of that shape was observed in the development data.
- The text of `SegReg`, `SegRegZ`, `Gen4Examples` and `HeadRel` was made with temporary scripts. The scripts were not committed.
- `Gen4Examples.lean` is not output of `scalgen.py`.
- The three complete field-composition examples have no kind. The accept proofs use those statements.
- There is still no kind for a composed statement with call fields.
- The two H5 accept theorems were proved again. The three H5 hand lemmas were not used.
- A program confirmed this by following the proof terms (`G4DepCheck.lean`). The control also passed.
- The SyncCommitteeMessage accept proof is 154 lines. The H5 hand proof is 190 lines.
- The step, segment and field theorems that the proof uses are 371 lines, with the statement and kind lines included.
- The slowest new module takes 25 seconds.
- The prologue, the return segment and the nil-check steps with the frame size as a parameter were also proved (L4).
- Eight per-type hand head, epilogue and spill lemmas were proved again with them.
- There is no generality claim. Whether it carries over to other types was not measured. That is the work of H6.
- Evidence files added: `scal/negcases-gen4.json`, `scal/negative-gen4.json`. `gen/e2e/negative.py` was not changed.
- The negative tests count 40 of 41 cases. 1 statement mutation of a store step ended with a heartbeat timeout.
- That 1 case does not count as passed.
- The axioms gate ran into a temporary JSON. The committed `axioms-gate.json` and `AxiomsScal.lean` were not changed.
- The generator-side work (`--gen4`) was not done. It is the work of the next unit, the `--gen4` generator work (section 22).
- There is no independent review yet.

## 22. Generator work for the `--gen4` mode: generator change after H5, development work, not a hold-out

- The base is `718e023` (end of the `--gen4` lemma work). The implementer is a new Opus 5.5 session. Not reviewed yet.
- After H5, the proof generator `gen/scal/scalgen.py` was changed. The new mode is `p2dec --gen4`.
- The inputs are development data only: the `.S` and IR of the 10 development types, the `--gen4` lemmas and the survey table.
- Thus all `--gen4` coverage is in-sample. There is no transfer claim. The hold-out measurement is H6.
- The matching is not a multi-instruction template. A small data flow follows the values of registers and stack slots.
- A block is emitted only when the data flow shows the entry state. Anything else is "not covered" with a reason and a classification.
- The default, `--gen2` and `--gen3` outputs are byte-identical (`regen_check.sh` old commands 23/23 SAME).
- If `--gen3 --compose` has no hand statement, it now writes an `UNCHECKED STATEMENT` mark (review of the `--gen3` generator work).
- No committed output is such a case. Thus no committed file changed.
- It ran one time for each type (gate job 09). The raw output was committed with no changes before it was used (`e774d9b`).
- Before that there were three scratch test runs (jobs 01, 02, 05). Their results were not put in the repository.
- The one run came after the test runs checked the output shape and the build. Thus that run is not an independent measurement.
- Coverage (`--gen4`, `--gen3`, `--gen2`): Checkpoint 2/2 / 2/2 / 1/2, AttestationData 3/5 / 3/5 / 1/5, BeaconBlockHeader 5/5 / 5/5 / 3/5, Eth1Data 3/3 / 3/3 / 3/3, BlobIdentifier 2/2 / 2/2 / 2/2, DepositMessage 3/3 / 3/3 / 3/3, Deposit_Data 4/4 / 4/4 / 3/4, PendingPartialWithdrawal 3/3 / 3/3 / 0/3, SyncCommitteeMessage 4/4 / 2/4 / 0/4, PendingConsolidation 2/2 / 1/2 / 0/2.
- The uncovered fields are the two AttestationData fields Source and Target. The classification is "new field kind" (nested container).
- The accept theorems of three types were proved again with the generated chain. The field composition is hand text (no kind).
- Types: `H5.sm_accept_stmt`, `H5.pc_accept_stmt`, `H4.pw_accept_stmt`. The statements are unchanged.
- There are no generality, transfer or speed claims.
- Correction (first `--gen4` fix, item M2 of the review of the `--gen4` generator work): "only when the data flow shows the entry state" above is a belief of the generator walk. It is not a kernel check.
- On 7 review inputs that belief was wrong. See section 23.

## 23. First generator fix for the `--gen4` mode: after the review of the generator work, before the H6 freeze, development work, not a hold-out

- The base is `21b8aab` (end of the `--gen4` generator work). The implementer is a new Opus 5.5 session. Not reviewed yet.
- Changed: the `--gen4` walk of `gen/scal/scalgen.py`, the rule 11 exception of `kindcheck.py`, and `p2dec_test.py`.
- The inputs are the 50 inputs of the review of the `--gen4` generator work and the 10 development types. No hold-out material was read.
- "Covered" is a claim of the generator. Each emitted theorem gets a kernel check one by one.
- Only the hand field composition checks whether the step chain makes the block entry state, and whether a call block belongs to that IR field.
- Thus H6 result (S) counts "the walk covers + each theorem builds". It does not count "field proved".
- The 10 committed `Gen4*.lean` files were made again with the fixed generator. All are byte-identical. There are no new files.
- The rules were fixed to fit the review inputs. Thus the results on those inputs are not an independent measurement.

## 24. Second generator fix for the `--gen4` mode: after the review of the first fix, before the H6 freeze, development work, not a hold-out

- The base is `a81c0ea` (end of the first fix). The implementer is a new Opus 5.5 session. Not reviewed yet.
- This is the third generator change after H5. Changed: the `--gen4` walk of `scalgen.py` and `p2dec_test.py`.
- The immediate value of `cmp $size,%rcx` in the head is compared with the IR SSZ fixed size (review M3).
- The epilogue after the last field event is examined. Stores, calls and a different frame size are rejected.
- The inputs are the 83 inputs of the review of the first fix, the 50 inputs of the review of the generator work and the 10 development types. No hold-out material was read.
- The rules were fixed to fit the review inputs. Thus the results on those inputs are not an independent measurement.
- The 10 committed `Gen4*.lean` files are byte-identical. The development-type coverage is unchanged (all 9, AttestationData 3/5).

## 25. Third generator fix for the `--gen4` mode: after the review of the second fix, before the H6 freeze, development work, not a hold-out

- The base is `6ac27e4` (end of the second fix). The implementer is a new Opus 5.5 session. Not reviewed yet.
- This is the fourth generator change after H5. Changed: the `--gen4` result logic of `scalgen.py` and `p2dec_test.py`.
- In the epilogue, a `jmp` to a label that is not in the file is rejected (review M4).
- Exit 0 comes from only one place, when all three success marks are set. Other exceptions give exit 2.
- The inputs are the 89 inputs of the review of the second fix, 83 of the review of the first fix, 50 of the review of the generator work and the 10 development types. No hold-out material was read.
- The rules were fixed to fit the review inputs. Thus the results on those inputs are not an independent measurement.
- The 10 committed `Gen4*.lean` files are byte-identical. The development-type coverage is unchanged (all 9, AttestationData 3/5).


## 26. Hold-out H6 evaluation (seven flat fixed-size types): after opening

- Time opened: `H6.opened_utc` in `scal/HOLDOUT-OPENED` (commit `dcc71a8`, 2026-11-11T17:18:33Z).
- Method freeze: commit `0e775ac`. The 5 blobs and 4 tree ids of the freeze record were counted again. All are the same.
- Batch (S) is all 7 types of the frozen rule: PendingDeposit, PowBlock, HistoricalSummary, SigningData, SyncAggregatorSelectionData, ValidatorBalance, VoluntaryExit.
- The full-proof types are PendingDeposit and PowBlock. The scope is `UnmarshalSSZ` only.
- The evaluation session did not make the `--gen4` generator, checkers, kinds or lemmas. It could read the files of the earlier units.
- Disclosed similarity (selection record H6-A5): by field kinds, several types are close to the development types. By the rules, there is no similarity filter.
- Thus H6 is a measurement of compiler variation on known kinds. It is not evidence for new field kinds.
- The hand Desc (`c7ebeee`) was committed before the checker Desc was printed.
- The link table (`98303d7`) was made before the hand statements. The statements had to use the frame facts of the `.S`. The generator did not run.
- The hand statements `H6.pd_accept_stmt` and `H6.pb_accept_stmt` (`0ad71a7`) were committed before the generator ran.
- The generator ran one time for each type (jobs 10–16, curator order). It did not run again with other options.
- The raw output, the summary JSON and the stderr were committed first with no changes (`1ab614e`). There are 0 lines of hand changes.
- `--gen4 --compose` did not run. The freeze record records a reject. Result (C) is "rejected by design".
- The makeslice literal `type__+387072` is the uint8 type word in this ELF. `h6link.py` confirmed that it is the same as in the Checkpoint batch.
- `gen/scal/*`, the kind and lemma modules, `Fk/*`, the contracts and the existing statements were not changed.
- Thus `gen/scal/AxiomsScal.lean` was not extended. The axioms gate counts all declarations. The new declarations are included.
- The negative case file is in `prysm/go1.26.10/e2e/h6/negcases-h6.json`.
- Proposal (not done): P-H6-1, a kind for the field composition. The composition now is hand text. Most of the hand lines are this.
- Proposal (not done): P-H6-2, let the generator emit the head and epilogue lemmas. The head and epilogue of PendingDeposit are hand lemmas.
- Proposal (not done): P-H6-3, record the differences between the IR and the Prysm types. The `total_difficulty` of PowBlock is `uint256` in the specification and 32 bytes in Prysm.
- There is no generality claim. There are also no superiority or speed claims. There is no independent review yet.

## 27. Integration of the `--gen4` work and H6: correction after review

- In sections 22–26, "Not reviewed yet" is replaced by the reviews below. Those sections are not changed.
- "There is no review of this integration itself yet" in section 21 (integration of `--gen3` and H5) is also replaced: the review of that integration approved `fbbc382`.
- The review of the `--gen4` lemma work: APPROVE (`718e023`). The review of the generator work: REQUEST_CHANGES (`21b8aab`). The review of the first fix: REQUEST_CHANGES (`a81c0ea`).
- The review of the second fix: REQUEST_CHANGES (`6ac27e4`). The review of the third fix: APPROVE (`0e775ac`, H6 method freeze). The review of H6: APPROVE (`8ce5dda`).
- Reason for the three fixes: each review found one path where `--gen4` emitted "covered" without a check. The third fix changed the result logic to fail-closed.
- This document has two "21." sections: the section of the integration of `--gen3` and H5, and the section of the `--gen4` lemma work. Two sides each numbered a section 21. The numbers are not changed.
- Thus, to refer to a section 21, also write its name: "section 21 (integration of `--gen3` and H5)", "section 21 (`--gen4` lemma work)".
- Item S7 of the review of H6: the H6 evaluator's declaration-comparison control was an edit of the dump text. The reviewer's Lean-level control covers it.
- Item S9 of the review of H6: the curator's temporary scripts were outside the evidence directory (`/tmp`). This is only recorded.
- The `regen_check.sh` of the integration check also ran the generator commands of the 7 H6 (S) outputs two more times each (scratch). The result is SAME.
- This is not an H6 run. The H6 rule "one time for each type" applies to the evaluation session.
- The proposals (not done) stay as they are: P-H6-1, P-H6-2, P-H6-3, items S6 and S9 of the review of the third fix.
- There is no generality claim. There is no review of this integration itself yet.

## 28. Lemma work for the `--gen5` mode: after H6, development work, not a hold-out

- This work was done after the H6 evaluation, the review of H6 and the integration of `--gen4` and H6. The base commit is `c29ebdc`.
- All 16 flat fixed-size types are development data. This section makes no hold-out claim.
- The author session is a new Fable session and is the direct author. This session did not change the generator.
- This session read the H6 records, the review of H6, the verdicts of the reviews of the `--gen4` generator work and third fix, and the handoff document of the `--gen4` work.
- This session read the 11 hand accept statements, their proof modules and the generated `--gen4` chain files.
- Only new modules were added: `KindAcceptN`, `AcceptTies`, `FieldComp`, `RejectN`, `RejectTies`.
- The example modules are also new modules: `Gen5ExPd`, `Gen5ExSm`, `Gen5ExVe`, `Gen5ExPb`, `Gen5ExRej`, `Gen5Examples`, `WitVeA`.
- The existing `.lean` files, `gen/scal/*`, the contracts, the statements, the ELF and the tool chain were not changed.
- The kind of an accept statement is `decAcceptKindN C L fields`. `L` is the frame layout and is a parameter.
- The kind does not check that the layout is the frame of the `.S` file. The proof of each case checks that.
- A callee field is `.u64` in the kind. The callee list is a separate parameter of the layout.
- 10 hand statements are equal by `rfl` to the kind cases. The hand statements are unchanged.
- Checkpoint is not `rfl`. A theorem was proved that the kind case implies the hand statement.
- The converse was not proved. The hand statement names the receiver tail chunk separately.
- The intermediate theorems are stated with the full accept memory. The boundary state `StDesc` fixes those statements.
- Each head, field and epilogue theorem has a kind line. The accept proof is an `eventually_trans` chain.
- The boundary states are parameters that the generator gives. Boundary states that do not connect fail in the kernel.
- The example text was made with temporary scripts. The scripts were not committed. It is not output of `scalgen.py`.
- The types of the PendingDeposit, SyncCommitteeMessage and PowBlock examples are committed hand statements.
- The VoluntaryExit example has no hand statement. Its statement is a kind case.
- A witness for the VoluntaryExit accept theorem was added (`WitVeA`). Specification alignment and Desc were not done.
- The size-reject lemma `decrej_seg` takes the frame size as a parameter. The kind is `decRejectKindN`.
- The types of the 12 committed size-reject theorems are cases of that kind.
- The `xor` epilogue has only the existing lemma for frame `0x20`. A frame-parameter shape was not made.
- No example was made for code with mixed fields (PendingPartialWithdrawal).
- The PendingDeposit example module is 1054 lines. The statements are 685 lines and the proofs are 251 lines. Elaboration takes 5.0 seconds.
- The hand module `PdAccept.lean` is 520 lines. The text of the generated shape is longer. No lines are written by hand.
- The negative tests count 35 of 37 cases. 2 kind-line mutations ended with heartbeat timeouts.
- Those 2 cases do not count as passed. `rfl` at default transparency can fail slowly on a wrong number.
- Evidence files added: `scal/negcases-gen5.json`, `scal/negative-gen5.json`. `gen/e2e/negative.py` was not changed.
- The axioms gate ran into a temporary JSON. The committed `axioms-gate.json` and `AxiomsScal.lean` were not changed.
- The generator-side work was not done. It is the work of the next unit, the `--gen5` generator work (section 29).
- There is no generality claim. There is no independent review yet.

## 29. Generator work for the `--gen5` mode: generator change after H6, development work, not a hold-out

- This work was done after the `--gen5` lemma work. The base commit is `94fd8a6`.
- The author session is a new Opus session. It is neither the lemma author nor a reviewer.
- This is the fifth generator change after H6. Only `gen/scal/*` was changed.
- New method: `p2dec --gen5`. The front end is the `--gen4` walk and is unchanged.
- The default, `--gen2`, `--gen3` and `--gen4` outputs are byte-identical. The old commands are 40/40 SAME.
- This session read the handoff document of the lemma work, the example modules and the temporary output scripts.
- This session read the verdicts of the four reviews of the `--gen4` generator work and its fixes. The result logic is fail-closed from the start.
- All 17 flat fixed-size types are development data. This section makes no hold-out claim.
- The hold-out material for flat types is used up. Thus the statement check is the kind and the binding.
- `kindcheck.py` rule 12 computes the kind parameters again, separately, from the IR and the `.S`.
- For the 10 types with hand statements, the type of the generated theorem is equal by `rfl` to the hand statement.
- Checkpoint is a kind case only. The implication `cp_accept_of_kind` requires the layout `layCp`.
- The chunk order of the generated layout is different from `layCp`. Thus it was not bound.
- For the five types with no hand statement, the statements are kind cases. There are no independent hand statements yet.
- These five accept theorems are not complete decoder proofs. Reject, Desc, specification and witness are work of the close-out unit (section 31).
- Rejected: PendingPartialWithdrawal (mixed fields), AttestationData (nested fields). Both give exit 2.
- The raw output was committed with no changes before it was used (`8192427`). There is one run for each type.
- There are no generality, transfer or speed claims. There is no independent review yet.

## 30. Correction to section 29 (review of the `--gen5` lemma and generator work, step 0 of the close-out unit): records changed only

- The verdict of that review is REQUEST_CHANGES (target `ea6a0c6`). The two required fixes are records.
- All technical checks passed. The proofs, lemmas, kinds, generator and checker are not changed.
- A new Opus session of the close-out unit wrote this section. The text of section 29 is not changed.
- M1 correction: "the 10 types with hand statements" in section 29 is wrong. There are 9 `rfl` identities in the tree.
- The 9 are 4 `_same` and 5 `_stmt`. Checkpoint was not bound. PendingPartialWithdrawal was rejected.
- The message of commit `8192427` also says "10 types". The correct number is 9. The commit is not changed.
- M2 correction: there were scratch test runs before "one time for each type". The source is the tool record of the `--gen5` generator worker.
- Test run 1: 19:40:58Z, PendingDeposit only. The output is scratch under `/tmp`.
- Test run 2: 19:41:26Z, all 17 types. The output is scratch.
- Test run 3: 19:41:48Z, SyncAggregatorSelectionData and ValidatorBalance. The output is scratch.
- Test run 4: 19:46:46Z, 15 types. The output is scratch in the work directory.
- Test run 5: 19:53:09Z, VoluntaryExit only. Its bytes were compared with the output of run 4.
- Between the runs, `gen5.py` and `scalgen.py` were changed (reject block, layout constructor, module loading).
- Gate diagnostics D1 (19:42–19:46Z) and D2 (19:47Z) elaborated the 15 scratch outputs.
- The committed run is gate job 04 (19:57:56Z). The scratch outputs were not committed.
- Review S1: the five test runs above ran without the gate. This is a procedure violation.
- All five are Python generator runs, each under 1 second. There was no `lake` or `lean` without the gate.
- This violation does not change the results. The reviewer made the 15 outputs again and they were the same as the committed copies.
- The `--gen2` work (section 15) and the `--gen4` work have the same correction. From this unit on, all generator, `lean`, `lake` and `go` runs go through the gate.
- Review S3: the frame of SyncAggregatorSelectionData and ValidatorBalance is `0x38`.
- This frame shape has no statement bound by hand. For the two statements, it was only shown that two derivations (generator, checker) agree.
- The close-out unit writes the independent hand statements. The results are recorded in the section of that unit.
- Review S2 (checker limit): `kindcheck.py` does not bind the constant `C` to the `.S` of the head.
- Only the Lean code facts (`win … (by rfl)`) fix `C`. They exist only on the accept path and the size-reject path.
- Writing this limit into the rule 12 text is a change to `kindcheck.py`. In this unit the generator side is frozen. It is an open item.
- Review S4: "32 adversarial" in commit `607ba61` is wrong. There are 28 adversarial inputs and 2 real rejected types.

## 31. Completion of the remaining five flat decoders and the verification inventory (close-out unit): development work, not a hold-out

- This work was done after the review of the `--gen5` lemma and generator work. The base commit is `ea6a0c6`. The step 0 record correction is section 30.
- The author session is a new Opus session. It is neither an author of the `--gen5` lemma or generator work nor a reviewer.
- The five types are the (S) types opened in H6. Thus they are in-sample. There is no hold-out claim.
- The generator, checker, lemmas, kinds and existing statements were not changed. Only new modules were added.
- Three independent hand statements were committed first (`e1ccb83`): SyncAggregatorSelectionData, ValidatorBalance, VoluntaryExit.
- At that time, this session had not opened `Gen5SaDec`, `Gen5VbDec`, `Gen5VeDec` or `Gen5ExVe`.
- This session read the text of that review. The text says that VoluntaryExit has the `layCal` shape.
- The review text also records the frame `0x38` shape: 6 chunks, no rdi slot, guard 72, one callee and one uint64.
- These facts also follow directly from the `.S`. But the three statements were written after reading the review text. They are not fully independent.
- The text and kind lines of the generated theorems were not read. The identity check is an independent check against that text.
- All three identities are `rfl` (`8380a3d`). Neither side was changed.
- The five hand Desc files were committed before the checker Desc was printed (`534538e`).
- ValidatorBalance has no container in consensus-specs. Its Desc was taken from the Prysm proto.
- Thus the specification alignment of ValidatorBalance is not independent of the producer source. It is independent only of the checker output.
- The specification alignment, rejects and witnesses were built on the generated theorems. Session scripts made the theorem text from the generated statements.
- `pw_e2e_accept_spec_k` of PendingPartialWithdrawal was added. It was missing in H4 because there was no accept theorem.
- The verification inventory script `gen/tools/inventory.py` was made new. The inventory binds by the code constants of the theorem types.
- Result: the decoders of the 16 flat types are all complete in the defined sense. `INVENTORY.md` records what this sense leaves out.
- There are no generality, transfer or speed claims. There is also no "all codecs" claim. There is no independent review yet.

## 32. Correction of the section 31 verification inventory (review of the close-out unit, inventory fix unit): inventory script and records changed only

- The review of the close-out unit (target `c4e1d74`) is REQUEST_CHANGES. The scope is the inventory wording and the script limits.
- The author session is a new Opus session. It is neither the close-out author nor a reviewer.
- The theorems, statements, lemmas, kinds, generator and generated files were not changed.
- M1: the denominator in section 31 was `functions.json` (641 dumped functions). It was not the full target.
- The target has 211 HashTreeRoot, 211 HashTreeRootWith and 211 MarshalSSZ. These methods were not in the dump.
- The denominator now is `prysm/go1.26.10/ssz-methods.json`. It is made from the nm listing of the pinned ELF.
- The nm listing is in a run directory outside the repository. Its sha256 is equal to `nm sha256` in `build-ids.txt`. The script checks it.
- M2: "the decoders of the 16 flat types are all complete" in section 31 is about the 16 types of the development population.
- By the IR rule, the target has 40 flat fixed-size types. 24 were not started.
- M3: a code key now requires a subject. A different target code constant must not call the function of the row.
- `codec` and `reject_complete` are still not bound to the row. `INVENTORY.md` records this limit.
- S1: a constant is counted only if the `.S` path is inside the link table of the pinned ELF. Subdirectories are also scanned.
- S2 (open): the ValidatorBalance proto was read from the main Prysm checkout `c4e939f`.
- "The tree that the Go differential uses" in the `VbDesc.lean` comment is wrong. The message text is the same as in the pinned tree `ab15ff7` (hash comparison by the review).
- The comment is Lean source, so this unit did not change it.
- S4: the session scripts `mkspeck.py` and `mkwit.py` of the close-out unit are not in the repository. For the theorem text, the committed files are the source.

## 33. Integration of the `--gen5` work: correction after review

- In sections 28–32, "There is no independent review yet" and "Not reviewed yet" are replaced by the reviews below. Those sections are not changed.
- "There is no review of this integration itself yet" in section 27 is also replaced: the review of the `--gen4` and H6 integration approved `c29ebdc`.
- The review of the `--gen5` lemma and generator work (together, `ea6a0c6`): REQUEST_CHANGES, records only. Section 30 closed it.
- An earlier review of the lemma work ended midway because of the usage limit. A partial verdict is not a result.
- The review of the close-out unit (`c4e1d74`): REQUEST_CHANGES, inventory only. Section 32 (inventory fix unit) fixed it. The review of the inventory fix approved `be21280`.
- All `--gen5` work is on development data, in-sample. There is no hold-out claim. The hold-outs of this population are used up.
- The `regen_check.sh` of the integration check ran the 15 `--gen5` commands two more times each in scratch. The result is SAME.
- This is not a new generator result. "One time for each type" in section 29 is a rule of the `--gen5` generator session.
- The integration check also ran the inventory script again. The output is byte-identical to the committed copy.
- Open items: item S2 of the review of the `--gen5` lemma and generator work (checker), items S2 and S3 of the close-out review (`.lean`), items N1–N3 of the review of the inventory fix (inventory script).
- The list and vector work of a different machine is not in this tree. There are no generality, transfer or speed claims. There is no review of this integration itself yet.

## 34. Lemma unit of the flat-encoder work (flat encoder fast path): development work, not a hold-out

- The base commit is `e1fd7c0` (head of the flat-encoder preparation unit). The author session is a new Fable session. There is no review yet.
- All 16 flat types are development data. This population has no hold-out. There is no transfer claim.
- Only new modules were added. The existing `.lean` files, the generator, the checker, the contracts, the statements and the ELF were not changed.
- The scope is the fast path only. The premises are `len + SizeSSZ ≤ cap` and the exact lengths of the byte fields.
- The growslice branch, the length reject and morestack were not proved. The growslice instructions are never stepped on.
- The statement kind is `encFastKindN C L fields`. `L` is the frame facts and is read from the `.S`.
- The hand statements of BeaconBlockHeader and Eth1Data are equal by `rfl` to the kind instances.
- Checkpoint is an implication (`cp_marshal_of_kind`). The hand statement has an additional 32-byte piece `ctl` at `rax + 40`.
- The converse does not hold as written. There is no other difference.
- The author read the three hand statements before writing the kind. Thus the binding is not an independent check.
- The scratch emitter of the unit made the example text. The emitter is not a generator and is not in the repository.
- The emitter reads the `.S` and the IR and walks the fast path in a symbolic state. It ran many times without the gate (Python, under 1 second).
- Six examples were committed: Checkpoint, BeaconBlockHeader, Eth1Data, ValidatorBalance, DepositMessage, HistoricalSummary.
- The last three have no hand statement. Their statements are kind instances. Independent hand statements are the work of the close unit (section 36).
- The emitted text of the other 10 types was elaborated only in scratch (diagnostics D4, D5, 2 gate jobs, 0 errors).
- The text of those 10 types was not committed. It is not a repository result. The generator unit (section 35) makes it again with the generator.
- Those 10 types: BlobIdentifier, Deposit_Data, PendingPartialWithdrawal, SyncCommitteeMessage, PendingConsolidation, PendingDeposit, PowBlock, SigningData, SyncAggregatorSelectionData, VoluntaryExit.
- `runtime.moveSliceNoCapNoScan` (PowBlock, HistoricalSummary, SigningData) comes after the frame check of the epilogue.
- The check is `cmp %rsi,%rdx; jb`. It branches if the result pointer is inside the function's own frame. It is not the growslice path.
- On the fast path the branch is not taken. This was proved from the separation of the output bytes and the frame slots (`EncFrameTest.lean`).
- This function has no contract. No new contract form was made. The lemma fits only frame `0x50`.
- The premise `cap < 2^63` was taken as it is from the hand statement. The proof does not use this premise.
- There is one witness, `WitVbM` (ValidatorBalance, empty prefix and 3-byte prefix).
- There are 23 negative tests. 8 controls passed, and 14 mutations failed inside the target theorem.
- 1 case (`e2-tie-cp-stmt-field`) had an error on a line outside the range, so it was not counted.
- Deviation from the plan: a step theorem is not emitted for each instruction. The steps use library lemmas as proof terms.
- Kind lines (in the `KindStep` style) for the new step lemmas themselves were not made.
- There are no generality, speed or complete-encoder claims.

## 35. Generator unit of the flat-encoder work (`p2enc --gen6`, flat encoder fast path): development work, not a hold-out

- The base commit is `d1e30ca` (head of the lemma unit). The author session is a new Opus session. There is no review yet.
- This is a generator change. It is a change after the `--gen5` work and H6. All 16 flat types are development data (in-sample).
- This population has no hold-out. The statement checks are the kind, the hand-statement binding and `kindcheck.py` rule 13.
- The author read the handoff document of the lemma unit, the six examples and the scratch emitter `mk6.py`. The generator text follows that method.
- The proof bodies of the six examples and of the generated output differ only in names and doc comments. Thus those six are not an independent check.
- The rule 13 interpreter does not import the generator. But the same author wrote it with the same handoff document.
- The three hand statements (BeaconBlockHeader, Eth1Data, Checkpoint) were committed before the lemma unit. The generator reads their layout definitions and compares each slot.
- All generator test runs were done inside the gate: e2g 01, 03, 04, 05. The committed run is e2g 06 only.
- The raw output was committed with no changes before it was used (`e426d84`).
- There are no generality, speed or complete-encoder claims. Independent hand statements, witnesses and specification-conformance theorems are the work of the close unit.

## 36. Close unit of the flat-encoder work (flat encoder fast path: independent statements, witnesses, specification conformance, inventory): development work, not a hold-out

- The base commit is `dcc6e80` (approved by the review of the generator unit). The author session is a new Opus session. There is no review yet.
- All 16 flat types are development data (in-sample). This population has no hold-out.
- Four independent hand statements (PowBlock, SyncCommitteeMessage, PendingPartialWithdrawal, Deposit_Data) were committed before the generated theorems were opened (`0d25193`).
- What the author read before that: the handoff document of the lemma unit (interface section), the kind definition `KindEncN.lean`, the hand statement `bh_e2e_marshal_main`.
- Also read: the generated file `Gen6VbEnc.lean` of a different type (head and fast-path theorems), the witness `WitVbM.lean`, and the `.S` and IR of the four.
- The `Gen6{Pb,Sc,Pw,Dd}Enc.lean` of the four, the summary JSON, the `kindcheck` output and the reviewer's layout output were not opened before that.
- Thus the independence of the four lies in the recomputation of the layout (order of frame slots, post slots and existential slots). The statement shape followed the interface text.
- The unit's evidence tool `scal/e2c/e2cemit.py` emitted the witness and specification-conformance text from the generated statement text. The generator and checker were not changed.
- Three text bugs of `e2cemit.py` (BlobIdentifier and ValidatorBalance specification-conformance attempts 1, 2) are recorded in gate jobs 03, 04. They closed in attempt 3.
- There are no generality, speed or complete-encoder claims. growslice, length reject and morestack were not proved. T-7 (finding T-7: the `GrowsliceC` contract has no lower bound on the remaining heap) was deferred.

## 37. Inventory fix unit of the flat-encoder work (correction after the review of the close unit): inventory script and records only

- Correction to section 36 (item S1 of the review of the close unit): before writing the independent statements, the author also read `scal/enc2-survey.md`.
- That file copies the frame, guard and spill lines of each type from the `.S`. It has no statement text.
- Thus the independence judgment for the four is the same as in section 36. That summary may have helped the layout recomputation.
- Correction to the last line of section 36 (item M1 of the review of the close unit): the paths that are not proved are different for each type. The `INVENTORY.md` NOT proved column is the reference.
- This unit did not change the proofs, statements, generator, checker, lemmas or generated files. There are 0 new declarations.
- The author session is a new Opus session. There is no review yet.

## 38. Integration of the flat-encoder work: correction after review

- In sections 34–37, "There is no review yet" is replaced by the reviews below. Those sections are not changed.
- "There is no review of this integration itself yet" in section 33 is also replaced: the review of the `--gen5` integration approved `93dae89`.
- The review of the preparation and lemma units (together, `d1e30ca`): APPROVE. The review of the generator unit (`dcc6e80`): APPROVE.
- The review of the close unit (`5072b63`): REQUEST_CHANGES, one inventory column only. Section 37 (inventory fix unit) fixed it. The review of the inventory fix approved `eec1d4f`.
- All flat-encoder work is on development data, in-sample. There is no hold-out claim.
- The `regen_check.sh` of the integration check ran the 16 `--gen6` commands two more times each in scratch. The result is SAME.
- This is not a new generator result. "One time for each type" in section 35 is a rule of the generator-unit session.
- The integration check also ran the inventory script again. The output is byte-identical to the committed copy.
- Open items: item S3 of the review of the preparation and lemma units, items S2–S5 of the review of the generator unit, item S3 of the review of the close unit, items N1 and N3 of the review of the inventory fix, item S4 of the review of the `--gen5` integration.
- The list and vector work of a different machine and the AttestationData encoder are not in this tree.
- There are no generality, transfer, speed or complete-encoder claims. There is no review of this integration itself yet.

## 39. Hold-out H7 (24 flat fixed-size types: one measurement, close what was generated): hold-out measurement + closing

- The method freeze is `0923998` (approved by the review of the flat-encoder integration). The evaluation session is a new Opus session. It did not make generators, checkers, kinds or lemmas.
- The opening record H7 block (`scal/HOLDOUT-OPENED`, `be12791`) was committed before the code, `.S` and IR entries of the 24 types were opened.
- What was read before that: only the names of the 24 types (INVENTORY.md) and the flat rule text.
- The generator ran `p2dec --gen5` one time and `p2enc --gen6` one time for each type (jobs 10–57). There were no test runs, reruns or option changes.
- The raw output was committed with no changes (`e5dd848`). 0 lines were changed.
- Result: decoders 7/24 and encoders 8/24 were generated. `--gen4` field coverage is 34/86 (a lower bound after the stop).
- Reject classification (verdict of the evaluator who read the `.S`): new field kind byte20 8 types, byte4 5 types, byte1 1 type, bool 2 types, new callee (Gwei) 1 type.
- There were no rejects because of padding, registers, setup order, only a new instruction form, frame form or mixing.
- 8 independent hand statements (4 decoders, 4 encoders) were committed before the generated theorems of those types were opened (`2735379`).
- What the author read before that: the `.S` and IR of the 24 types, the hand statements of the development types (dd, sa, pd, sm, pw, sc, pb), the interface text of the flat-encoder lemma unit, and the exit codes and summary JSON of the raw output.
- The shape rules of the hand statements came from those texts. The parameters (frame, slots, instruction numbers) were read by hand from the `.S`.
- The `rfl` identities are 8/8 and closed in the first build (`ab46808`). Neither side was changed.
- The unit's evidence tools (`f24/tools/`) emitted the specification, specification alignment, witness and specification-conformance text. They are not generators. `gen/scal/*`, the kinds, the lemmas and `Fk` were not changed.
- Two one-field text bugs of the evidence tools (BuilderPreferences: specification bridge, encoder specification conformance) closed in attempt 2 (jobs 93, 97).
- The independent Desc was written from the Prysm proto. No consensus-specs copy is reachable from this session (other worktrees are out of scope).
- The Desc checker record exists only for DepositRequest. The other 6 decoders did not get codec equivalence (proposal, not done).
- The rejected types were not proved by hand. The coverage proposals are recorded in OUT and RESULT as "proposal, not done".
- There are no generality, transfer or speed claims. These 24 types are now opened. They are not hold-outs. There is no review yet.

## 40. Integration of H7: correction after review

- In section 39, "There is no review yet" is replaced by the review below: the review of H7 approved `6f20eef`. That section is not changed.
- "There is no review of this integration itself yet" in section 38 is also replaced: the review of the flat-encoder integration approved `0923998`.
- S1: three of the generated types are close variants of development types. The reviewer confirmed this with an own `.S` comparison.
- The decoder and encoder of BuilderDepositRequest are the same as Deposit_Data (0 different lines after label normalization).
- The encoders of BlobSidecarsByRangeRequest and ExecutionPayloadEnvelopesByRangeRequest are the same as SyncAggregatorSelectionData.
- The decoders of the two types differ only in 2 lines of the error path (error string length).
- Thus 3 of the 7 generated decoders and 3 of the 8 generated encoders are close to the sample. There is no generality claim.
- S3: 34/86 is a lower bound after the stop. It is not a coverage ratio. 13 is a walk claim with no emitted theorem.
- S5: before the statement commit (`2735379`), the author saw one line of the kindcheck record.
- That line lists only the walk theorem names of BeaconBlocksByRange (decoder, encoder). It has no statement text.
- S6: the DepositRequest `desc.json` was copied from the scratch of a different job. The content sha256 `489fe67a…` is equal to the committed checker record.
- The checker record is in `gen/desc/results/main.result.json` (committed before this unit). The result is PASS.
- The head of `F24DprSpecChecker.lean` records `prysm/go1.26.10/e2e/engine_v1.DepositRequest.desc.json`. `f24/` is missing.
- The real file is `prysm/go1.26.10/e2e/f24/engine_v1.DepositRequest.desc.json`. It is text of a generated file, so it was not changed.
- S7: the integrator added 12 negative tests. Result: 12/12 as expected (4 controls passed, 8 mutations failed inside the target theorem, 0 timeouts, 0 wrong targets).
- The `regen_check.sh` of the integration check ran the 15 H7 generation commands two more times each in scratch. The result is SAME.
- This is not a new H7 run. The 33 rejected runs (exit 2) have no files, so they were not run again.
- The list and vector work of a different machine and the AttestationData encoder are not in this tree.
- There are no generality, transfer, speed or complete-encoder claims. No trend across H3–H7 is claimed either. There is no review of this integration itself yet.
