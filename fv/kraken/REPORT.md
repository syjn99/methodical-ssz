# REPORT: Current state of the Kraken x64 codec verification

On 2026-11-12, commits `57c061d` and `84a4747` removed the Go 1.26.3 test-type evidence and the memory-optimization study.
Tag `archive/fv-before-workflow` (commit `4ccbccb`) holds the full tree and history before the removal.
Sections 0–10 keep only the statements that apply to the files that remain. Section 11 is about the Prysm generated code.
The direction is in `DIRECTION.md`, the session history is in `HISTORY.md`, and the pinned versions are in `TOOLS.md`.
The baseline of the Prysm end-to-end proof work (pinned versions, scope, reproduction) to move to another machine is in `prysm/BASELINE.md`.

## 0. Verdict

**Conditional.**

The verdict of the Prysm stream in section 11 is conditional. Its conditions are in the "Conditions" list of section 11.
Gate 1 was the gate of the Go 1.26.3 test types (Scalars, ListU64, ListC, BitVec, BitL, Nested and similar types).
At tag `archive/fv-before-workflow`, this report said that gate 1 was not passed.
The evidence of gate 1 was removed on 2026-11-12. No one evaluated gate 1 again on the current tree.

Phase 1c (generator and Prysm inventory) is section 10.
At tag `archive/fv-before-workflow`, this report said that gate 1c was not passed. Most of its evidence was removed on 2026-11-12 (section 10).
No one evaluated gate 1c again on the current tree.
The Prysm end-to-end proof work is section 11. The results of the extensibility hold-outs H1 (ValidatorIndex, BeaconBlockHeader) and H2 (Eth1Data) are in `prysm/go1.26.10/e2e/scal/RESULT.json` (last paragraph of section 11).
In H2, the fixed generator covered 0 of the 2 root fields (finding SG-1: the template needs an `add` that a field at SSZ offset 0 does not have). This is a historical result from before the extension. The decoder proof is a hand proof.
The SG-1 extension (the generator change for that shape) is development work after the two hold-outs were opened. In that extension, Eth1Data is in-sample data (section 11).
The result of hold-out H3 (`UnmarshalSSZ` of BlobIdentifier and DepositMessage) is in `H3` of `scal/RESULT.json` (section 11).
The review of hold-out H3 approved `75166e4`.
The result of hold-out H4 (`UnmarshalSSZ` of Deposit_Data and PendingPartialWithdrawal) is in `H4` of `scal/RESULT.json` (section 11).
The review of hold-out H4 approved `fae7d6f`. There are 0 required fixes and 7 items to fix.
The `p2dec --gen2` generator mode had three reviews. The review of its lemma unit is APPROVE.
The review of its generator unit is REQUEST_CHANGES (documents only, closed by the `--gen2` fix unit). The review of the fix unit is APPROVE.
The `--gen2` work and H4 were merged in one integration (`56e0c88`). The review of that integration approved `6a78c59`.
Hold-out H5 (SyncCommitteeMessage 2/4, PendingConsolidation 1/2, composed reject, accept theorems proved by hand composition) is in section 11.
By field kind, the two H5 types are close to the sample. 2/4 and 1/2 are the results for such types (item S1 of the review of H5).
The review of hold-out H5 approved `1fec11e`. There are 0 required fixes and 7 items to fix.
The `p2dec --gen3` mode had two reviews. The review of its lemma unit approved `f5c5f52`.
The review of its generator unit approved `6dc0e2a`. That commit freezes the H5 method.
The `--gen3` work and H5 were merged in one integration (`2bedf6d`). The review of that integration approved `fbbc382`.
In H5, the `--gen3` result on development data did not carry over unchanged (section 11).
The `p2dec --gen4` generator (in-sample) is in section 11. It fully covers 9 of the 10 development types.
The review of the `--gen4` lemma unit is APPROVE. The reviews of the `--gen4` generator unit and of its first two fixes are REQUEST_CHANGES.
The review of the third `--gen4` fix approved `0e775ac`. That commit freezes the H6 method.
Hold-out H6 (a batch of 7 types: PendingDeposit, PowBlock, HistoricalSummary, SigningData, SyncAggregatorSelectionData, ValidatorBalance, VoluntaryExit) is in section 11.
In H6, 18/18 steps are covered. The PendingDeposit and PowBlock accept theorems are proved by hand composition.
The segment result (S) 18/18 of H6 is a claim about steps. The types are close to the development types (selection record H6-A5). There is no similarity filtering (item S1 of the review of H6).
The counts of H3–H6 have different populations and filtering. Do not read them as a trend (item S2 of the review of H6, section 11).
The review of hold-out H6 approved `8ce5dda`. There are 0 required fixes and 9 items to fix.
The `--gen4` work and H6 were merged in one integration, on top of the merge of ARM task B (`3e1cedc`). The review of that integration approved `c29ebdc`.
The `p2dec --gen5` work is in section 11. All of it is development data and in-sample.
It has a lemma unit, a generator unit, a close-out unit for the five remaining flat decoders and an inventory fix unit.
The review of the `--gen5` lemma and generator units is REQUEST_CHANGES (`ea6a0c6`, records only, technical checks passed).
The review of the close-out unit is REQUEST_CHANGES (`c4e1d74`, inventory only).
After the inventory fix unit, its review approved `be21280`. There are 0 required fixes.
The `--gen5` work was merged in one integration (`03cf086`). The review of that integration approved `93dae89`.
The flat-encoder work (`p2enc --gen6`, encoder fast path of the flat types) is in section 11.
It has a preparation unit, a lemma unit, a generator unit, a close unit and an inventory fix unit.
All of the flat-encoder work is development data and in-sample.
The review of the preparation and lemma units approved `d1e30ca`. The review of the generator unit approved `dcc6e80`.
The review of the close unit was REQUEST_CHANGES at `5072b63`. It was only one inventory cell, and all proof checks passed.
After the inventory fix unit, its review approved `eec1d4f`. There are 0 required fixes.
The flat-encoder work was merged in one integration (`e70492d`). The review of that integration approved `0923998`.
Hold-out H7 (the 24 flat fixed-size types that were not opened before) is in section 11. The review of H7 approved `6f20eef`. There are 0 required fixes and 7 items to fix.
H7 was merged in one integration (`e6b46fd`). There is no review yet of that integration itself.
The reviewed local states are the head of the flat-encoder integration `0923998` and the H7 head `6f20eef`.
H7: we ran each generator once per type on 24 flat types that were never opened before.
The decoder was generated for 7 of the 24 types, and the encoder for 8 of the 24 types.
All rejects come from field kinds or callees that the generator does not support.
Classification: byte vector 20 in 8 types, byte vector 4 in 5 types, byte vector 1 in 1 type, bool in 2 types, Gwei callee in 1 decoder type.
Three of the generated types are close variants of development types: BuilderDepositRequest (decoder and encoder have the same code as Deposit_Data), BlobSidecarsByRangeRequest and ExecutionPayloadEnvelopesByRangeRequest (the encoder has the same code as SyncAggregatorSelectionData, the decoder differs only in 2 lines of the error path).
There is no generality claim. We also do not claim a trend across H3–H7.
The only published states are `6a78c59` and the fixed pin `71161fa`. The commits after them exist only on this machine.
The counts of the verification inventory use only `prysm/INVENTORY.md`, the output of `gen/tools/inventory.py`, as the source (section 11).
The denominator is the SSZ methods of the pinned ELF. Each line uses the target count of the method kind (211, 10, 6).
Decoder: 18 of the 211 target `UnmarshalSSZ` are complete by the definition of the inventory.
Partial 10 (primitive types 4, H7 types without codec equivalence 6), none 183.
Not in the decoder "complete": morestack, `writeBarrier ≠ 0`, runtime callee bodies (contracts).
Also not in it: callee error returns, growslice (finding T-7: the `GrowsliceC` contract gives only an upper bound on the remaining heap), x86-64.
Encoder: 24 of the 211 `MarshalSSZTo` have the fast path complete. No encoder is complete.
The premises of the fast path are `len + SizeSSZ ≤ cap` and the exact length of the fields.
Not proved: growslice branch (T-7 is deferred), length reject, morestack.
Also not proved: the `moveSliceNoCapNoScan` branch (PowBlock, HistoricalSummary, SigningData).
We also did not justify the frame separation premise for all Go callers (item S2 of the review of the flat-encoder integration).
The per-type list is the NOT proved column of `INVENTORY.md`. For Checkpoint and BeaconBlockHeader, we proved more of the recorded paths.
There are no theorems for the HashTreeRoot family.
The target has 40 flat fixed-size types. Development 16, H7 types with inventory rows 8, not started 16.
The 8 H7 types: decoder complete 1 (DepositRequest), encoder fast path complete 8.
The reject classification of the 16 not-started types is in `INVENTORY.md`, per type (item S4 of the review of H7).
There are 17 development types: the 16 flat types and the nested AttestationData.
The AttestationData encoder is work on another machine. It is not in this tree.
The list and vector work on the other machine is also not in this tree. We do not claim it here.
We did not adopt the optimization pilot OPT-R1 (a generator option that reserves the output once in `Checkpoint.MarshalSSZTo`).
There is no claim of "all codecs", "encoder complete", "generator finished", generality or speed.
In H4, the `--gen2` result on development data did not carry over unchanged (section 11).
For the BeaconBlockHeader encoder, we proved the fast path and three length reject sites. The premise of the length reject is `len + 112 ≤ cap` (section 11).
For `Eth1Data.MarshalSSZTo`, we proved only the fast path (section 11, encoder reuse work). The review of the encoder reuse work approved `ad15fbc`.
No encoder is complete.
The H3 work and the encoder reuse work were merged in one integration (`500571c`, `c10daf9`).
OPT-R1 was merged in a second integration (`83e0b6a`). The review of OPT-R1 approved `5821b19` (generator `ca191bb`).
One review of these two integrations approved `a70492c`. There are 0 required fixes and 6 items to fix (S1–S6).
What that review did not check is at the end of the OPT-R1 paragraph in section 11.
OPT-R1 is a test on one function and one binary (end of section 11).
It showed a re-check that keeps correctness. It did not show a general speedup. The results are mixed.

Numbers:

- The numbers at the end of fix 3 were about the Go 1.26.3 test types. Their evidence was removed on 2026-11-12.
  The removed evidence: `AXIOMS.txt`, `AXIOMS-ALL.txt`, the witness modules, `negative/RESULT`, goval and `semtest/`. Tag `archive/fv-before-workflow` holds it.
- Check on the reduced tree (`84a4747`): `lake build Fv Fv1 Fk E2e E2eAd E2eScal E2eList E2eHb E2eSeg E2eDep E2eDepW E2eEnc E2eDec` in `fv/kraken/lean`.
  The result is exit 0, "Build completed successfully (1841 jobs)".
- No other check ran on the reduced tree. Not run: negative tests, link checks, declaration drift, independent review.

## 1. Completion unit

The completion of one main theorem has all six elements.

1. Contract or theorem.
2. A witness of the full premise on a concrete Host. For variable length: empty, 1 item, maximum.
3. Machine-code theorem.
4. Link check PASS. The data that the theorem reads is an ELF include (`Fk/Data.lean`).
5. Negative test: the mutation fails in the designated theorem and the control passes.
6. Go value: the witness is a Go value. A value that the check cannot read counts as not checked.

The abstract witness (element 2) and the Go value completion (element 6) are different claims.
For the Go 1.26.3 test types, `lean/tools/wit/goval.py` checked element 6 with `layout.json` (gc amd64 layout).
It looked at size, alignment, padding, bool, slices, overlap, the type descriptors (Size_, Kind_) of `%w` witnesses and the initialization of error globals.
It did not look at Go values of intermediate states.
`lean/tools/wit/` was removed on 2026-11-12. Tag `archive/fv-before-workflow` holds it. For some Prysm theorems, the Lean predicate `cpGoValue` (`E2e.GoVal`) checks the witness receivers (section 11).

## 2. Gate 1 table

Meaning of the columns:

- "Reject paths": decoder error branches closed by a machine-code theorem / total (Go source basis).
- "Witness": empty, 1, maximum and inner lengths.
- "Go value": goval result. It looks only at the scope of section 1.
- "Abstract model": the contracts on which the theorems of that type depend. All contracts have only abstract models.
- "Composition": the two-call composition theorem and the full-premise witness.
- "Post": the resources in the conclusion of the main theorem. "Identical" is a conclusion that all of memory is the same. This is stronger than frame preservation.

This section had the gate 1 table of the 9 Go 1.26.3 test types (Scalars, FixedVec, ListU64, BitVec, BitL, Nested, ListC and the reduced Prysm Checkpoint and AttestationData).
The witnesses, negative tests, goval results and most theorems of that table were removed on 2026-11-12.
Tag `archive/fv-before-workflow` holds the table and its evidence. No one evaluated the table again on the current tree.
The column meanings above stay because the obligation counting rule of `gen/obligations.py` cites them.
28 `Fk` modules remain because the Prysm proofs import them (`lean/Fk.lean`). Some of them hold theorems about the test types, for example `Fk/ScAccept.lean` and `Fk/LuReject.lean`.
The two Prysm types of `target/prysm/` are reduced structs that copy the v7.1.8 `51b5a75` schema.
They are not the real Prysm binary with protobuf fields.

## 3. Trust items

| Item | What we trust | Current check | Next action |
| --- | --- | --- | --- |
| Lean kernel, Kraken x64 semantics, EthLib specification | Shared base | None | Keep |
| Kraken = real CPU | We did not do a hardware comparison | None (arm64 host) | x86-64 Linux machine or CI |
| ELF → Lean program | objdump, `link/conv.py`, `include_x64_rt` | Link check (a)–(e): three independent decoders, symbols and displacements | Keep |
| ELF → Lean data | `link/data.py`, `data_include` (`Fk/Include.lean`) | Link check (f): data file = ELF bytes, pointer word = symbol + offset, same-line rule (only printable ASCII and `\n`). `data.py --check`: regeneration = tracked files. The hash is in the RESULT bundle | Keep |
| Do the theorems use the include definitions | Read the premises of a theorem from the theorem statement. The check tools do not read Lean sources (only `Code.lean` and `AXIOMS.txt` for the hash). `AXIOMS.txt` was removed on 2026-11-12. `link/out/RESULT` still has its hash, and `link/check.py` hashes it only if the file exists. No tool catches arbitrary Host declarations or name shadowing (astra fix 2 finding 1) | None (by design, DIRECTION section 3) | 1c: extract dependencies from elaborated declarations |
| Entry id and address | Check (f) looks only at file = ELF. A file changed to another address and the bytes at that place also gives PASS for (f). For entries that proved code `lea`s (9 format strings, `int`·`uint64` type words), the proof bound them (data mutation `logs/34`). Most of those proofs were removed on 2026-11-12. In the kept modules, `Fk/LuRejectCall.lean` names `luFmtTooBig`, `luFmtMis` and `intType`, `Fk/Contracts.lean` names `blFmtB`, `bvFmtJ`, `lcFmtOrder`, `intType`, `uint64Type` and `staticuint64s`, and E2e modules name `staticuint64s`. The contracts that used `vblMsgE/Z/B` (`Fk/Vbl.lean`) were removed. Only `Fk/Data.lean` names these three entries now | Proof, contract hypothesis | Keep |
| Content of format strings | Lean binds only the length (`*_len`) and the absence of `%` in nil formats (`*_nopct`). The match between the `%w`·`%d` verb shapes and the contracts (`FmtErrorfWC`·`DWC`·`DDC`) is a contract hypothesis. A format with changed content also passes the proof | None | Freeze the format body with a Lean lemma (remaining work) |
| Rebuild tracking | Lake puts the content of the `input_dir` of `needs` (norm, data, `Fk/*.S`) into the input hash | Rebuild experiment of fix 3 (fix 3 commit body) | Keep |
| Value of error globals | Go package initialization puts in `(itab, errorString)` | Theorem premise. The Go 1.26.3 example `sc_reject_bool_err` and its witness were removed on 2026-11-12. For the Prysm theorems, see condition 2 of section 11 | Runtime initialization refinement |
| Go value | The witness is a real Go value | goval was removed on 2026-11-12 (section 1). For the Prysm theorems, see the Go value column of section 11 | 1c X2: as a Lean predicate |
| Runtime contracts | The Go 1.26.3 runtime satisfies the contracts | Abstract models (`rt_*`, `bump_*`). `joint_models` (one Host, one heap, `Fk/Regress.lean`) was removed on 2026-11-12 | After phase 2 (HTR) |
| fmt allocation amount, GC | Allocation is in budget. There is no GC during the call (`runtime.writeBarrier` = 0 is in `F`) | None | Runtime refinement |
| fmt result object | The conclusion says only rax ≠ 0 | None | Define the result object contract before sub-error propagation |
| memmove | Only non-overlapping ranges | `⋆` of the caller | Keep |
| Stack guard, X15 = 0 | Fast path premise | Theorem premise | Keep |
| Go layout | The gc amd64 size rule of go/types (for Prysm, `go_fields` of `prysm/ir/ir-mainnet.json`). We did not confirm it with an amd64 run | None in the tree. `lean/tools/wit/layout.go` was removed on 2026-11-12 | x86-64 machine |

The rows `VblMsg` and ValidateBitlist were removed on 2026-11-12 with `Fk/Vbl.lean` and `Fk/RtVbl.S`. Tag `archive/fv-before-workflow` holds them.
The forms, models and witnesses of the contracts are in `CONTRACTS.md`.

## 4. Remaining items (astra fix 2, 8 required)

| # | Required fix | Status | Plan (DIRECTION section 4) |
| --- | --- | --- | --- |
| 1 | Role and name resolution of the Lean reference check | Closed by deletion: we deleted the role classification. rodata bytes and addresses, `type:int` and `staticuint64s` use include definitions. Include definitions that are not used: `errorStringItab` (+`_addr`), `errorStringPtrType_addr`, `intType`·`uint64Type` bytes, 6 `Err*_addr`. The theorems use `label "ssz.Err*"` and `label "go_itab…" + 8` directly, and the itab word is an arbitrary `ity` (the proof forces this notation). The remaining limit is "Do the theorems use the include definitions" in section 3 | Fix 3, data include step |
| 2 | Full expression and type identity of (h) | Closed by deletion: we deleted (h). We include bytes and pointer words. The self-test catches the itab mutation of the review as FAIL. The proof binds entry id ↔ address (section 3) | Fix 3, data include step |
| 3 | Real target of Go format calls | Closed by deletion: we deleted `golits.go`. The format bytes come from the ELF. The match between the format content or verb shape and the contracts is a contract hypothesis (section 3) | Fix 3, data include step |

Items 4–8 were about the witnesses, goval, postconditions, ListC theorems and the gate table of the Go 1.26.3 test types.
That material was removed on 2026-11-12. Tag `archive/fv-before-workflow` holds the items and their evidence.
No one evaluated items 4–8 again on the current tree.
Items 1–3 are about the link design (`link/`, `Fk/Data.lean`), which stays.
After the removal, more include definitions may be unused than item 1 lists. No one checked this.

Known limit that still applies (fix 3 review S9): we did not freeze the format string bodies with Lean lemmas. See "Content of format strings" in section 3.

## 5. Findings

`syjn99/ssz-gen-fixes` `698c202` fixed the generator defects (F1, F2, G1–G3, H1).
The current ELF is the output of that generator.

- **F1**: The BitVec decoder accepted a byte with padding bits set. The theorem `bv_reject_padding_main` proved that the fixed decoder rejects it.
- **F2**: The length check of the BitL encoder counted bytes, not bits. The theorem `bl_marshal_reject_main` proved that the fixed encoder rejects the excess.
- `semtest/f12_test.go` was the Go regression test for the two defects.
- The two theorems and `semtest/` were removed on 2026-11-12. Tag `archive/fv-before-workflow` holds them. No one checked them again on the current tree.

Observation (not a defect): the ListC element offset order error is a `fmt.Errorf` with two `%d`, so it has two `convT64` calls and an allocation.
Observation (tool): `link/check.py` makes `link/__pycache__`. It is not in `.gitignore`. Run it with `python3 -B`.
Observation (contract): the match between the type argument (`type__ + n`) of `MakesliceC`·`NewobjectC` and the element size `esz` is a contract hypothesis. We did not include the type descriptor content to connect them.

## 6. Kraken request list

- `bsr` parsing. This was why ValidateBitlist was a contract (`Fk/Vbl.lean`, removed on 2026-11-12).
- The condition codes `g, ge, nl, nle, s, ns, o, no, p, np` in the elaborator `include_x64`. Now we go around this with `include_x64_rt` in `Fk/Include.lean`.
- Parsing of multi-byte nop (`nopl (%rax)`, `data16 nop`). Now `link/conv.py --norm` changes them to `nop`.
- A way to catch the `grind` timeout inside `kstep`. Now we use `load_step`/`store_step` in `Fk/Step.lean`.
- Atom comparison in `ecancel`: atoms such as `StaticBox (-4 + rcx)` hit the recursion limit. It cannot tell `@Eq DataMem` atoms from `@Eq (Std.ExtHashMap …)` atoms. Now we avoid this with `generalize`.
- The `@[spec]` form of the vcgen branch. The evaluation was `vcgen/B0.md`. It was removed on 2026-11-12, and tag `archive/fv-before-workflow` holds it.

## 7. 1c design inputs

1. Freeze the three stack coordinates with small theorems: function entry rsp, rsp just before the call, callee entry rsp (= just before the call − 8).
2. Check the contract composition on one Host and one heap. Do not count the number budget of the `emp` heap as physical space.
3. Put symbolic length limits only in the concrete layout generator.
4. Make the completion table from declaration dependencies and full application. Also propagate the external contracts under function specifications.
5. Diagnose address overlap and type aliases at the generation step. Move the bounds check of goval into the generator.
6. Write witness values in the form `n#64`. Keep atoms such as `StaticBox (-4 + x)` opaque with `generalize`.
7. Extract the layout from elaborated Lean expressions. Do not guess declaration roles from source spelling.
8. Derive function specifications from theorems (`*_holds`). Also keep sub-contract dependencies in the completion table.
9. For composition, make three separate completion items: `hupd` exists, full composition witness, execution of real caller instructions. Now only the first two exist.
10. Divide the Go values not checked into value, resource fragment, type content and runtime global. Also look at the Go values of intermediate states and of the second call.
11. Put error values as resources: rodata, box values, fmt format and argument types, global error objects. Put the initialization and non-nil condition of error globals in the specification graph.
12. Do not identify type data only by size and kind. Include the pointee and the method connection.
13. Classify postconditions into three: memory identity, explicit resource preservation, resources discarded with `True`.
14. Bind link mutations and the Lean build in one record. Do not use a checker-only PASS as proof success.
15. If you fix the generator, update the Go regression tests and the Lean reject theorems together.

## 8. Reproduction

Prerequisites: git checkout (clean working tree), Lake packages of `lean/` fetched in advance.
Run heavy jobs one at a time and under a memory limit.
Run the commands from the repository root. If a step fails, stop.
The earlier commands for axioms listings, regression files, vcgen, goval, negative tests and `semtest/` named files that were removed on 2026-11-12.
Tag `archive/fv-before-workflow` holds those commands (this section) and their files.

```sh
set -eu
(cd fv/kraken/lean && lake build Fv Fv1 Fk E2e E2eAd E2eScal E2eList E2eHb E2eSeg E2eDep E2eDepW E2eEnc E2eDec)   # 84a4747: exit 0, 1841 jobs
python3 -B fv/kraken/link/data.py --check fv/kraken/link/out      # not run on the reduced tree
python3 -B fv/kraken/link/check.py fv/kraken/link/out             # not run on the reduced tree
python3 -B fv/kraken/link/check.py --selftest fv/kraken/link/out  # not run on the reduced tree
git diff --exit-code fv/kraken/link/out/RESULT                    # not run on the reduced tree
```

`AXIOMS.txt` is not in the tree now, and `link/check.py` hashes it only if it exists.
All 19 tracked link `RESULT` files (`link/out/RESULT` and the `prysm/go1.26.10/**/RESULT` link tables) have a `file sha256 … AXIOMS.txt` line.
Thus a new run of `link/check.py` may write a `RESULT` without that line and with a different BUNDLE. No one ran it on the reduced tree.
The target regeneration commands are in `TOOLS.md`. The Prysm commands are in section 11.

## 9. 1c inputs (include definitions and data files)

The full interface is in "ELF data include" of `TOOLS.md`. 1c makes the data files of its own ELF in the same format.

| Lean name | Data file | Meaning |
| --- | --- | --- |
| `Fk.Data.<id> : List UInt8` | `link/out/data/<id>.data` | The ELF bytes of that range. If it has pointer words, it depends on `[Host]` |
| `Fk.Data.<id>_addr : BitVec 64` | The `at` line of the same file | `(label "<label>" + <offset>).toBitVec`. If the offset is 0, there is no `+ 0` |
| `Fk.Data.intType_size_kind` and others | — | Structure theorems about the included bytes (Size_, Kind_, Elem, itab type word and methods, `staticuint64s` table) |
| `Fk.staticBox_of_lt` | `staticuint64s.data` | Bytes of `StaticBox v` = `Int.toBytes 8 v` (v < 256) |

Rules for how the generator makes data files:

1. The entry table (id, label, offset, length, pointer slots) holds the addresses and lengths that the code uses (`lea sym+off(%rip)`, `mov $len`). Read the bytes from the ELF. Do not write them by hand.
2. Write a pointer slot as `word <label> <offset>`. The label is the nearest symbol at or below that value. If there are several at the same address, select the label that the converted code uses.
3. Label names follow the clean-up rule of `conv.py` (`go:string.*` → `go_string._`).
4. For each file, `link/check.py` (f) compares it with the ELF again. The files are Lake `input_dir` inputs.
5. The Go 1.26.10 ELF puts its own data files and tables in its own namespace. Do not reuse the Go 1.26.3 values.
6. For error globals, extract only the address. The runtime initialization sets the value. The non-nil conclusion of a reject theorem has an initialization premise such as `e0 ≠ 0`.
7. The witness sets error globals to initialized values and makes the `%w` type word point to the ELF descriptor (`errorStringPtrType`). For the Go 1.26.3 witnesses, goval checked the initialization of the globals and the Size_·Kind_ of the descriptor. goval was removed on 2026-11-12.

## 10. 1c: generator and Prysm inventory (phase 1c stream, branch `claude/ssz-fv-phase1c`)

**Gate 1c: not passed at tag `archive/fv-before-workflow`.** No one evaluated gate 1c again on the current tree.
At the tag, the generator made again the 58 hand main theorems of the 9 hand-case types (statement SAME, Lean passed). But the generated proofs used the hand proof text as a template. Of the 132 types in the Prysm scope, 0 types passed all obligations.
The generated theorems (`Gen1cX4`) and the generators `gen/x4/` and `gen/x5/` were removed on 2026-11-12. Tag `archive/fv-before-workflow` holds them.
Details: the stream report (`$RUN/streams/phase1c/REPORT.md`), `prysm/go1.26.10/X5.md`, `prysm/TYPES.md`, `prysm/GENERATOR-FINDINGS.md`.

### 10.1 Gate 1c table: 9 hand-case types (Go 1.26.3 ELF, `Gen1cX4`)

This subsection had the gate 1c table of the 9 hand-case types: statements, witnesses, machine-code theorems, link, negative tests and Go values of the `Gen1cX4` library.
`Gen1cX4`, `gen/x4/` (with `gen/x4/results/`) and `gen/wit/` were removed on 2026-11-12. Tag `archive/fv-before-workflow` holds them.
No one evaluated this table again on the current tree.

### 10.2 132 types in the Prysm scope (Go 1.26.10, experiment baseline)

- Link table: 136 functions, `conv.py --norm` + `check.py` (a)–(f) PASS, BUNDLE `1bdfc4f0…` (`prysm/go1.26.10/link/RESULT`).
- size: 46 types generated + Lean passed, mutation 46/46, only standard axioms. 86 have variable size, so there is no template.
  The 46 size theorems were in the `Gen1cX4.X5` modules. They were removed on 2026-11-12. The records `prysm/go1.26.10/x5.json` and `x5-sizemut-ranges.json` stay.
- Decoder and encoder: all 134 obligations rejected at the generator step. Contract absent 2 (the Checkpoint·AttestationData decoders call the hand-written `primitives.*.UnmarshalSSZ`), automation limit 132 (field combinations with no template). The 4 Lean runs that forced a fixed template all gave errors (the first error is in `X5.md`).
- Types that passed all obligations: 0. Of an average of about 28 fixed inventory obligations per type (3676 in total), only size was proved (in the removed `Gen1cX4.X5` modules).

### 10.3 Trust items (added by 1c)

1. This item was about the generated proofs of `Gen1cX4` ("generated" = the hand proof text fitted to a template). `Gen1cX4` was removed on 2026-11-12. Tag `archive/fv-before-workflow` holds it.
2. This item was about the fixed template `gen/x4/anchor.py`. `gen/x4/` was removed on 2026-11-12. Tag `archive/fv-before-workflow` holds it.
3. Go 1.26.10 is a new experiment baseline. We did not move the Go 1.26.3 theorems. We did not read its runtime contracts (makeslice, growslice, memmove, newobject, fmt.errorf …) again against the Go 1.26.10 runtime source (unconfirmed assumption).
4. The Prysm hand-written primitive type methods (Slot, Epoch, ValidatorIndex, Gwei, CommitteeIndex, 24 functions) have no specification. Whether to keep them as contracts or to prove them as function specifications waits for a user decision. 52 generated types call them.
5. The Desc of the 135 Prysm types is not compared with an independent specification (consistency check only). Only the 9 hand types are compared with the EthLib specification.
6. Converter: we added a `%riz` rule to `conv.py --norm` (SIB without index, same address). The Go 1.26.3 conversion result is byte-identical. We fixed a defect in the LLVM line reading of the checker `check.py` that dropped the last byte of 10-byte instructions (the check is now stricter).
7. The host is arm64. We did not do an x86-64 hardware comparison.

### 10.4 Failure classification

| Class | Where | Count |
| --- | --- | --- |
| Automation limit | Prysm decoders and encoders (no template), variable-size size | 132 + 86 |
| Contract absent | Prysm Checkpoint·AttestationData decoders (hand-written primitives calls) | 2 |
| New instruction | `%riz` operand (Kraken parser) closed with a conversion rule (18/18 parsed) | 0 remaining |
| Generator defect (sszgen 698c202) | D1: nested container field keys in the IR (no effect on the output code, `GENERATOR-FINDINGS.md`) | 1 |

Defects in our tools (found and fixed in this stream): theorem range of the negative test evaluator (blank lines in the hand text), memcap session maximum notation (in the copies), `check.py` 10-byte instructions.
The row "Hand case X4 blocked" and the defect "x4gen module without theorems" (item S4 of the seventh phase 1c review) were about `gen/x4/`, which was removed on 2026-11-12.

### 10.5 Phase 2 (HTR) inputs

- What the generator has: Desc (combined with the independent checker), fixed inventory obligations, symbolic length and `n#64` normalization, include adapter (API v3). HTR obligations can also go into the same fixed inventory format.
- The witness generator `gen/wit/` was removed on 2026-11-12. Tag `archive/fv-before-workflow` holds it.
- What is necessary before HTR: scope of the directive-walk template (byte vector and container fields, functions with a frame, function calls), a specification decision for the hand-written primitives, a re-check of the Go 1.26.10 runtime contracts, a variable-size size template.
- 1c did not touch the gohashtree path (HTR).

## 11. End-to-end proof of the real Prysm `v1alpha1.Checkpoint` encoder and decoder (Prysm end-to-end proof stream, branch `claude/ssz-fv-prysm-e2e`)

**Verdict: conditional.** For the real protoc type `v1alpha1.Checkpoint`, the decoder (accept, size reject), the encoder (fast path, growslice path, `ErrBytesLength` reject, specification alignment) and SizeSSZ are proved on the machine code of the Go 1.26.10 ELF `c6403c02…911e`. For the Epoch decoder, both accept and length reject are proved. The machine-code-level composition (E5) `cp_e2e_unmarshal_then_marshal` starts at the decoder entry and connects `cp_e2e_accept_main` and `cp_e2e_marshal_main`, and it has a one-Host witness `WitCpC` (fix of item M1 of the first review of the Checkpoint proofs). The encoder growslice path `cp_e2e_marshal_grow_main` is the case where the first append site grows (premise `len + 40 ≤ nextSliceCap (len + 8) cap`).
In INBOX 009 (session 4), we covered the remaining capacity cases with new theorems. We did not change the existing theorem statements.
`cp_e2e_marshal_grow2_main` proves the case where the first site fits and the second site grows (`len + 8 ≤ cap < len + 40`).
`cp_e2e_marshal_grow_any_main` covers all cases where the first site grows (`cap < len + 8`, includes `cap = 0` and nil `dst`, no `nextSliceCap` premise).
Its conclusion is one of two, exactly as the branch in the code. Left: if the capacity that growslice gave is `len + 40` or more, it is proved up to the return. Right: if the capacity is smaller, it is proved up to the exact state at the entry of the second growslice call.
In session 5 (INBOX 010 M1), we added a stronger theorem `cp_e2e_marshal_grow_any_sharp` with the same premises. Its conclusion has three cases, and all of them state the exact frame.
(A) If Root fits in the first new block, it returns. (B) If the heap `av1` that remains after the first call is at least the budget `2·nextSliceCap (len + 40) C1 + 8192` of the second call, it goes through the second growslice and returns.
(C) If the remaining heap is smaller than that budget, it is in the exact state at the entry of the second call, with `Heap av1` and `av1 < 2·nextSliceCap (len + 40) C1 + 8192`.
**We did not prove the execution after (C) (blocked, differential only).** The `GrowsliceC` result gives the remaining heap only as `avail' + newCap ≤ avail` (an upper bound). So we cannot derive only the budget premise of the second call (FINDINGS T-7, item S7 of the third review of the Checkpoint proofs). If that fact were available, the existing lemma `cpw_tail_grow` would give the return.
Controller decision (INBOX 010): there is no new contract form. The remaining area is "blocked / differential only" until a user decision. We do not claim "Checkpoint encoder complete". The only evidence for this area is the Go differential checks (`enc-w-len30-spare0`, `enc-w-len10-spare0`).
`cp_e2e_marshal_reject_grow_main` proves the reject after growslice (`cap < len + 8`, `len(Root) ≠ 32`). The 8 epoch bytes are at `[len, len+8)` of the new block, and the caller array does not change (the form of finding C-1: the encoder writes the epoch bytes before the Root length check).
The case-cover theorems `cp_e2e_marshal_cover` (`len(Root) = 32`) and `cp_e2e_marshal_reject_cover` (`len(Root) ≠ 32`) divide all capacities with `len ≤ cap` among the theorems above. The conclusion of a cover theorem is the output bytes (`dst ++ serialize`, EthLib independent Desc) and the frame `R`, and the rest is `⋆ True`. The exact memory accounting is in each theorem.
In session 5 (INBOX 010 M2), we added 2 cover theorems that state the frame. We keep the existing cover theorems unchanged.
The conclusion of `cp_e2e_marshal_cover_framed` is a disjunction of the postconditions of the component theorems: (1) fast path, (2) first append fits and the second grows, (3A)/(3B)/(3C) the three cases of `cp_e2e_marshal_grow_any_sharp`.
Each case states by name the capacity range, the 72-byte receiver, the stack slots, the guard word, the caller array (`pre ++ spare`), the new block, `Heap` and `R`. There is no `⋆ True`.
In the return cases, the output block is `pre ++ bs` and `serialize prysmCpDesc g.toValue = .ok bs`. In (2), the caller array is `pre ++ epoch ++ spare[8:]` (C-1). In (3), the caller array does not change.
`cp_e2e_marshal_reject_cover_framed`: if `len + 8 ≤ cap`, the epoch is in the caller array at `dst + len` (`blk = dst`, C-1). If `cap < len + 8`, the caller array does not change and the epoch is only in the new block `nb`.
The witnesses `WitCpWF.covf_runs` (len 30, cap 30 + n) and `covf_runs_nil` state in the conclusion the capacity range that the execution reaches. A theorem cannot decide which of (3A)/(3B)/(3C) applies, because `GrowsliceC` hides the capacity and the remaining heap (item S2 of the third review of the Checkpoint proofs, condition 4 below).
Hold-out H1 (extensibility step S3, the hold-out evaluation, method frozen at `56dfc27`, opened at 2026-11-10T17:53:24Z): the results, costs and limits are in `prysm/go1.26.10/e2e/scal/RESULT.json`.
The contamination record is `scal/CONTAMINATION.md`, and the opening record is `scal/HOLDOUT-OPENED`.
Proved: ValidatorIndex decoder accept and length reject, BeaconBlockHeader decoder accept, size reject, specification alignment and unreachability of the two error-wrap sites.
9 attempts in sessions 10 and 11 (3 in session 10, 6 in session 11) did not close this encoder (FINDINGS T-9: the kernel check of the stack guard ran out of memory, and HISTORY).
For the BeaconBlockHeader encoder, we proved **only the fast path**. It passed the kernel check in the T-9 stream (the work on finding T-9, branch `claude/ssz-fv-t9-fable`).
The review of the T-9 stream approved `154944e`. Session 15 merged it into this branch (merge commit `e56063c`).
The theorem is `E2eScal.Bh.bh_e2e_marshal_main`. Its statement shape is the same as `cp_e2e_marshal_main`.
The scope is only the fast path: `len(dst) + 112 ≤ cap(dst)` and the length of the three roots is 32.
Not proved by the T-9 stream: the growslice branch, the three length reject sites, the morestack path.
The encoder reuse stream proved the three length reject sites under a capacity premise (encoder reuse paragraph below).
T-7 is deferred. `GrowsliceC` is unchanged. We do not claim "BeaconBlockHeader encoder complete".
Cause of T-9: a proof that closes the stack guard branch with `simp` and `omega` fails the kernel check under the 5 GiB limit.
We did not profile the expensive subterm.
The hypotheses after `simp` contain `Int` arithmetic on the literal 2^64 − 32. That this literal is the cause is an inference.
We saw the same failure in a `BitVec` reproduction without the machine context (FINDINGS T-9).
The solution is the lemma `E2eScal.lea_cmp_be_false`. We wrote it once for `N`, and it uses `Fk.cmp_be_false` unchanged.
We did not increase `maxHeartbeats`.
Evidence: witness `WitBhM` (receiver as a Go value, two prefixes), specification alignment `bh_e2e_marshal_spec_k`, 36 negative tests (9 controls pass, 27 mutations fail in the theorem).
The Go differential 21/21 (9 fast path cases) ran on a linux/arm64 host. It looks only at Go semantics and did not run amd64 machine code.
The declaration difference against the stream baseline dump is ADDED 161, CHANGED 0, REMOVED 0. The baseline dump is the `9df1fb2` dump of the first review of H2.
Not run: link check rerun (it uses the existing bundle `140eb7bd…`), full cold build of `E2eScal`, the Lean Go value predicate of the receiver.
The costs and limits are in `beacon_block_header_encoder_t9` of `scal/RESULT.json`.
A temporary result is closed only when the `#print axioms` output contains neither `sorryAx` nor its own name (FINDINGS P-1).

The encoder reuse stream (branch `claude/ssz-fv-enc-reuse`, base `dda707c`) added two reuse blocks.
The review of the encoder reuse work approved `ad15fbc`. There are no required fixes. The integration with H3 merged it (`c10daf9`).
We did not change existing theorems, definitions or witnesses. The declaration difference against the baseline dump is ADDED 330, CHANGED 0, REMOVED 0.
Observation (FINDINGS ENC-1): the instruction text is different at all 6 compiled sites that append a 32-byte field.
The registers, the address calculation (`lea` or `add`), the source of the value (register or frame) and `nop` are different.
So a multi-directive template has only one case per site. What is common is the machine state at the time of the call.
Block 1 is `E2eScal.enc32_call`. Its code fact is the one directive `callq runtime.memmove`.
This block states the call, the return slot, the contract application and the frame once. The straight-line section before the call is stepped by hand at each site.
There are 5 cases: BeaconBlockHeader 89, 117, 147 and Eth1Data 36, 80.
The types of `bh_enc_{b,c,d}_via_block` are equal by `rfl` to the types of the existing `bh_enc_{b,c,d}`.
The reuse is partial. Through the block, the proof line counts per site are 56, 66 and 68 lines.
The hand proofs are 61, 71 and 73 lines. The block itself is 18 lines (review of the encoder reuse work).
Measurement (task 07, `lake env lean` per file, n = 2, shared machine): `EncBlock.lean` 1.01 s and 1.04 s, `BhEncBlock.lean` 3.12 s and 3.09 s, hand file `BhEncRoots.lean` 3.43 s and 3.37 s.
The content of the two files is not the same (`bh_enc_e` and lemmas). We do not claim a speedup.
For `Eth1Data.MarshalSSZTo`, we proved **only the fast path**: `E2eScal.E1.e1_e2e_marshal_main`. Its statement shape is the same as `bh_e2e_marshal_main`.
The premises are `len(dst) + 72 ≤ cap(dst)`, length 32 for the two roots, and `guard + 8 < rsp`. The stack guard uses `lea_cmp_be_false` (N = 8) unchanged.
Evidence: specification alignment `e1_e2e_marshal_spec_k` (independent Desc `prysmE1Desc`), witness `WitE1M` (receiver in Go layout, two prefixes).
Block 2 is `E2eScal.enc_reject_tail`. The parameters of the template `rejTail` are the frame release (`add` or `sub`), the constant and whether there is a `nop`.
The reject tail uses the ABI result registers. So one template fits.
We proved the three BeaconBlockHeader length reject sites as cases of this block: `bh_e2e_marshal_reject{1,2,3}_main`, witness `WitBhMR`.
Limit: the premise is `len + 112 ≤ cap`. The premise of the rewritten sections `bh_enc_a1` and `bh_enc_a2` is like that. The code writes only 16, 48 and 80 bytes.
We did not prove the length reject with a smaller capacity.
Before the reject, the earlier fields are written to `dst[len:]`. The conclusion states those bytes (FINDINGS ENC-2, the same class as C-1).
Executed checks: 32 of the 33 negative tests are as designed (9 controls pass, 23 mutations fail in the theorem). They are in `scal/negative-enc.json`.
The remaining 1 (`enc-e1-a-call`) is not a pass. The mutation was rejected in the code-fact lemma `e1_call_at`, which is outside the designated theorem. It is a targeting error of the author.
The axioms gate is PASS: 3813 declarations, 3223 theorems, only standard axioms, 0 `sorryAx` (task 70).
3 of the 10 attempts failed. There are 3 diagnoses. The gate time is 646 s (includes waiting). We did not increase `maxHeartbeats`.
Task 09 was recorded as a diagnosis but it also ran a fix. If we count it as an attempt, it is 11 of the limit of 12 (review of the encoder reuse work).
51 tasks went through the gate. The 52nd row ended with exit 2 before the gate (review of the encoder reuse work).
Not proved: the growslice branch and morestack path of the two encoders (T-7 is deferred), the two Eth1Data length reject sites, the Lean Go value predicate of the receiver.
Not proved (continued): `AttestationData.MarshalSSZTo` (not started), `runtime.memmove` (`MemmoveC` is a hypothesis).
Not run: link check rerun (it uses the `e1/link` and `bh/link` bundles in the tree), Go differential of the new paths, cold build.
We do not claim "encoder complete". The costs and limits are in `enc-reuse` of `scal/RESULT.json`.

The H2 result below and the H1 result above are results from before the SG-1 extension. They did not change, and we keep them as historical results.
Hold-out H2 (`UnmarshalSSZ` and `MarshalSSZTo` of `v1alpha1.Eth1Data`) was opened. The method is frozen at `56dfc27`, the same as H1.
The opening record is commit `7a5ea61` (2026-11-11T01:59:11Z). The results, costs and limits are in `H2` of `scal/RESULT.json`.
Generator result (executed check): we ran the fixed `scalgen.py p2dec` once (task 393).
The exit code is 2 and the output is 0 bytes. The generator coverage is 0 of the 2 root fields (FINDINGS SG-1).
Cause: DepositRoot reads from source offset 0. So the code has no `add $src,%rbx`.
The fixed template `rootDecMid` requires this directive. The generator stops at the first field and does not produce BlockHash either.
Classification: a coverage gap of the scal generator template. It is not a defect of `sszgen/` or of the generated Go. The generator rejected, and there is no wrong output.
At the time of H2 (historical): the offset-0 variant template was only proposed. After that, the SG-1 stream extended it by user instruction (SG-1 paragraph below).
Decoder (kernel check, hand proof): we proved the head `e1_e2e_head`, the accept `e1_e2e_accept_main` and the size reject `e1_e2e_reject_size_main`.
We also proved the specification alignment `e1_e2e_accept_spec_k`, `e1_e2e_reject_size_spec` and `e1_e2e_reject_complete`.
The codec equivalence of the independent hand Desc and the checker Desc is `prysmE1Desc_serialize_checker` and `prysmE1Desc_deserialize_checker`.
The hand section `rootdec_seg0` is hand text outside the frozen method. There is no generated theorem.
The witnesses are `WitE1A.e1_accept_runs` (3 inputs) and `WitE1R.e1_reject_runs` (lengths 71, 73, 0).
The axioms are standard only (task 430, 3303 declarations, 0 `sorryAx`).
Executed checks: link check PASS (task 392), negative tests 27/27 (`scal/negative-h2.json`), Go differential 6/6.
The Go differential ran on arm64. It looks at Go semantics and does not look at the ELF.
Not run at the time of H2: `kindcheck.py` (no generated theorem to check), cold build of the authoring session.
Not proved: the Lean Go value predicate of the Eth1Data receiver.
At the time of H2 (historical): we did not try the encoder `Eth1Data.MarshalSSZTo`. The stack guard has the form `lea -0x8(%rsp),%r12; cmp 0x10(%r14),%r12; jbe`.
Now: the encoder reuse stream proved the fast path of this encoder (encoder reuse paragraph above). We did not prove the other paths.
Reviewed claims (first review of H2): the reviewer rebuilt the 10 new modules cold (exit 0, 25.5 s, n = 1).
Measurement of the reviewer: 549 (52%) of the 1064 non-blank lines of the hand files are copies of H1·P2Dec source lines.

Limits of H2:

1. It is an out-of-sample case of one type.
2. H2 was opened after H1. A session that could read the H1 files evaluated it. It is not independent of the H1 experience.
3. We do not claim that the generator is better than the hand. We also do not claim a causal speedup.
4. We excluded `SizeSSZ` (finding AU-09: hold-out limits). Its code, IR and generated Go were already in the repository and were proved in phase 1c.
5. There is no encode mode. We did not try the encoder. AU-07 (a slow omega side goal in `P2EncCp`) was fixed after that, and review REVIEW-AU07 is APPROVE (audit AU-07 below).
6. This result is a negative result about generator coverage. It is not a negative result about the decoder.
7. A timeout is a timeout. It is not a pass. There was no timeout in H2.
8. `_kind` identity is not a non-vacuity witness.

SG-1 extension (branch `claude/ssz-fv-sg1`, the review of the SG-1 extension approved `da3f233`, and session 15 merged it):
This is development work after the two hold-outs were opened. It is not a hold-out result.
Eth1Data is development data of this extension. So in the extension, Eth1Data is in-sample.
We added a new template lemma `rootdec_seg_z` and the kind `rootDecSegZKind` (`P2DecZ.lean`, `KindZ.lean`).
`scalgen.py p2dec` now also accepts the offset-0 form.
The extended generator produces 2 of the 2 Eth1Data root fields (`GenE1Dec.lean`, untouched output, standard axioms).
The generated Eth1Data sections are only related to the decoder proof. The decoder proof does not use these sections.
`E1Accept` uses the hand lemma. `E1GenSame.e1_dec_DepositRoot_seg_hand` derives the hand conclusion from the generated theorem (kernel check).
The inline read of DepositCount still has no template.
`kindcheck.py` rejects files that have a `PARTIAL OUTPUT` header (item S2 of the review of the SG-1 extension, session 15).
Records: section 8 of `scal/CONTAMINATION.md`, `sg1-extension` of `scal/RESULT.json`, FINDINGS SG-1.

Hold-out H3 (method frozen at `dda707c`, opening record commit `782a41b`, 2026-11-11T04:26:30Z):
The scope is only `UnmarshalSSZ` of `v1alpha1.BlobIdentifier` and `v1alpha1.DepositMessage`. We opened the two types once.
The fixed generator ran once per type. Both exited 0, and the raw output was not touched.
The generator coverage is 1 of 2 fields (BlockRoot) and 1 of 3 fields (WithdrawalCredentials) (FINDINGS SG-2: the frozen generator reads only 32-byte byte-vector fields).
Index, Amount (inline uint64) and the 48-byte PublicKey were proved by hand. The PublicKey section is the new H3 module `DmSeg0.lean`.
Kernel check (standard axioms): the accept paths of the two types, size reject, codec equivalence of the independent Desc and the checker Desc, specification alignment, `reject_complete`, witnesses.
The accept theorems call the generated section theorems unchanged. The witness receiver layout is the IR `go_fields`. DepositMessage is a Go struct that is not from protoc.
Executed checks: link check PASS (`h3/link/RESULT`), negative tests 33/33, Go differential 12/12 (Go semantics on arm64, not the ELF).
Axioms gate PASS (3812 declarations), the declaration change against the `dda707c` dump is only ADDED 329.
Not proved: the morestack path, runtime call targets (contract hypotheses), the Lean Go value predicate of the receiver, everything outside `UnmarshalSSZ`.
Not run by the H3 evaluation session: cold build, `regen_check.sh` (it runs the generator again), x86-64 hardware.
The review of H3 approved `75166e4`. There are no required fixes. The integration with the encoder reuse work merged it (`500571c`).
The reviewer ran the generator one more time per type in scratch. The output is byte-identical to the committed files.
Reading A3 (the N class counts the fields of the type itself) was decided after the candidate list was visible. It was before the method code was opened.
In another reading (transitive fields), the N class is `ProposerSlashing`. If we read reading A1 (which types count as already in the tree) letter for letter, there is no candidate.
There is no witness that satisfies the premise `Pm` of `*_accept_spec_k`. It is the same as the Eth1Data and BeaconBlockHeader models.
Limit of H3: two types, one time. It is only evidence of transfer for these two types. There is no claim of superiority, general automation or causal speed.
Records: section 11 of `scal/CONTAMINATION.md`, `H3` of `scal/RESULT.json`, FINDINGS SG-2.

Merge check (session 15, executed checks, on top of merge `63ef3b9`, inside the gate and the 6 GiB cap):
`lake build E2eScal` exit 0 (task 435). `lake build --no-build E2e E2eAd E2eScal` exit 0 (tasks 436, 493).
Axioms gate PASS: 3483 declarations, 2923 theorems, 0 nonstandard axioms, 0 `sorryAx` (task 437).
Declaration comparison: merge 3483 = base 3303 + T-9 stream 161 + SG-1 extension 19. CHANGED 0.
The type hash and axiom set of every row are the same as the row of that stream dump. All 3 planted-change controls were caught.
`regen_check.sh`: all 6 `gen.sh` commands SAME (tasks 438, 491). `p2dec_test.py` 10/10 (task 492).
`kindcheck.py`: 6 generated files PASS, 23 self-tests PASS.
Negative test rerun: T-9 stream 36/36, SG-1 extension 7/7. The classification and the first error position are the same as the stream results (tasks 439–481).
8 new SG-1 extension cases: 2 controls pass, 6 mutations fail in the theorem (tasks 482–489).
Not run: full cold build of `E2eScal`, link check, Go differential, Go tests (no change to Go and link inputs).
The review of this integration approved `c3c56a1` (HISTORY, the correction item of FINDINGS).

Merge check (integration of H3 and the encoder reuse work, executed checks, on top of merge `c10daf9`, inside the gate and the 6 GiB cap):
We merged H3 `75166e4` and the encoder reuse work `ad15fbc` (`500571c`, `c10daf9`). There are no new proofs and no statement changes.
`lake build E2eScal` exit 0. Only the 28 new modules were built. `P2EncCp` was not built again (task 01).
`lake build --no-build E2e E2eAd E2eScal` exit 0 (task 02).
Axioms gate PASS: 4142 declarations, 3467 theorems, 0 nonstandard axioms, 0 `sorryAx` (task 03).
Declaration comparison: merge 4142 = base 3483 + H3 329 + encoder reuse 330. CHANGED 0, REMOVED 0.
The integration added 0 rows. The added rows of the two streams do not overlap.
Planted control: the gate caught a `sorry` theorem in a scratch module (exit 1). The declaration comparison also exits 1 (task 22).
`regen_check.sh`: all 8 generator commands SAME (6 `gen.sh`, 2 H3, task 04).
This is an integration check that ran in scratch. We do not count it in the "once per type" run of the H3 evaluation.
`kindcheck.py`: 8 generated files PASS, 23 self-tests PASS (task 05).
Negative test rerun: 5 H3 cases, 5 encoder reuse cases. For all 10, the classification and the first error line are the same as the record (tasks 11–20).
Not run: cold build from an empty `.lake`, link check, Go differential, Go tests.
One review of this integration and the OPT-R1 integration approved `a70492c`. See the end of the OPT-R1 paragraph below.
Records: `integration_int2` of `scal/RESULT.json` (includes `review_int_r2`).

Optimization test OPT-R1 (OPT-R1 integration, merge `83e0b6a`, the review of OPT-R1 approved `5821b19`, no required fixes):
We did not merge the generator commit `ca191bb` (branch `claude/ssz-gen-opt-r1`) into this branch. `sszgen/` and `ssz/` are unchanged.
The optional flag `--reserve-marshal` reserves `len + 40` once in `Checkpoint.MarshalSSZTo`.
The target is the new ELF `3ef7ac89…f602`. The 7 theorems are about that ELF (`E2e.OptR1`).
The old theorems are about the old ELF `c6403c02…911e`. They do not carry over to the new ELF.
Proved: fast path, reject, growth, reject after growth, specification alignment, two covers. The covers have no frame (`⋆ True`).
The new function has no second growslice call. So path (C) is not in that function. T-7 is unchanged and stays deferred.
The error path effect changed. With an invalid Root and `8 ≤ spare < 40`, it allocates one block. It does not write the caller spare.
The reject proof in that range depends on `GrowsliceC`, `MemmoveC` and the heap budget. The old reject theorem has no contracts.
The benchmarks (arm64 only) are mixed. B2 allocations 2 → 1. B5 fast path +12–14 %. B9 allocations 0 → 1. B8 ns did not improve.
21 of the 23 negative tests pass. The two `tail_fit` store mutations are not a pass, also in a 900 s rerun (`outside`, `timeout_heartbeat`).
Integration check (executed checks, inside the gate and the 6 GiB cap): only the 11 `E2e.OptR1` modules were built. The other 365 `.olean` files have the same sha256.
`lake build --no-build E2e E2eAd E2eScal` exit 0. Axioms gate PASS, declarations 4519 = 4142 + 377 (at the time of the OPT-R1 integration).
Addendum 2026-11-11: after the AU-07 fix, the values of the task B tree (`71161fa` + fix) are 4518 declarations and 3812 theorems (audit AU-07 below). These are not the values of this branch.
Declaration comparison (against the dump of the integration of H3 and the encoder reuse work): ADDED 377, CHANGED 0, REMOVED 0. The dump-level planted control was caught (exit 1).
User decision (2026-11-11): we do not adopt the test OPT-R1. We keep the evidence. The option stays off (default).
This decision closed U5. U1–U4 and U6 were not decided separately (section 8 of `prysm/BASELINE.md`).
Not run (integrator): Lean-level planted control, cold build, link check, Go differential, benchmarks, x86-64.
One review approved the two integrations (H3 with the encoder reuse work, and OPT-R1) together (`a70492c`, 0 required fixes, 6 items to fix).
That review ran a Lean-level planted control in a scratch copy. Both the gate and the declaration comparison caught it.
Not confirmed by that review: cold build from an empty `.lake` (the 115 base modules and `E2eScal.P2EncCp` were not checked again).
Also the link check, Go differential, Go tests, benchmarks and x86-64 hardware.
73 of the 89 negative tests were not run again. For the two cases of item S3 (the rerun with 900 s per case), it read only the result files of the integrator.
It also did not confirm the runtime contracts, the morestack path or the Kraken semantics. The secret and path checks are regex-based.
Records: `prysm/go1.26.10/opt-r1/MANIFEST.md`, `integration_int3` of `RESULT.json` (includes `review_int_r2`).

`--gen2` generator work (base `6c62a49`, development work, the review of the generator unit is REQUEST_CHANGES, documents only, the review of the `--gen2` fix unit approved `eacf0fb`):
We added an optional mode `p2dec --gen2` to the proof generator. The output of the default mode is the same letter for letter.
The 8 old generator commands are `regen_check.sh` SAME. The 6 new commands also give the same result in two runs.
Covered fields: Eth1Data 3/3, BlobIdentifier 2/2, DepositMessage 3/3. The raw output was not touched.
The 48-byte PublicKey and the inline uint64 fields (Index, Amount, DepositCount) now also have generated theorems.
`--compose` writes the full accept theorem. The only statement check is the `_type` identity with the hand theorem.
For a type with no hand theorem, the composed statement cannot be checked. There is no kind for the composed statement.
The hand compositions `G2.bi_e2e_accept_main_g2` and `G2.dm_e2e_accept_main_g2` also call only generated section theorems.
Hand line counts (without blank lines and comments, full files): BlobIdentifier 210 → 120 → 0, DepositMessage 464 → 155 → 0.
The middle value is the hand composition and the last value is the generated composition. 0 means only "hand lines inside the generated module".
Without `DmSeg0` (209 lines), DepositMessage is 255 → 155 (−39.2 %).
If we count only the proof bodies of the accept theorems, it is 80 → 62 and 120 → 93 (each −22.5 %).
The remaining hand work is as follows.
The hand base theorems (`Bi.bi_e2e_accept_main`, `Dm.dm_e2e_accept_main`, `E1.e1_e2e_accept_main`) stay unchanged.
These hand theorems are the only statement check of the composed theorems. The generated modules import these theorems.
The `--gen2` lemma modules were written by hand once: 824 lines (SegN 413, Compose 209, KindN 96, U64Inline 55, SegNRel 27, KindU64 24).
The generated proofs also call the per-type hand lemma `E1.e1_lo`.
Not in the hand line counts: code modules, Desc, specification alignment, reject theorems, witnesses, link tables, negative tests.
Shapes that it cannot cover: delegated overlay fields (Slot, Epoch, ValidatorIndex and others, compiled as calls), byte vectors with sizes other than 32/48/96.
Also uint64 at displacement 0, nested containers, lists, bitfields, bool and other integers, encoders.
It does not cover fields of type Slot, Epoch or ValidatorIndex. So most consensus containers are outside the current `--gen2` mode.
Reviewer runs: BeaconBlockHeader 3/5, Checkpoint 1/2, AttestationData 1/5 fields.
Shape limits of composition (`--compose`): frame `0x20`, the first field is a byte vector, the fields follow in IR order, the receiver is rdx.
If it is outside this or has a field that it cannot cover, `--compose` rejects with exit 2 and writes nothing.
The `--gen2` fix unit (after the review of the generator unit): `kindcheck.py` accepts the `_type` identity only for composed theorems.
Its right side must not be a generated name (`E2eScal.Gen…`, a declaration in `Gen*.lean`).
The PASS line says "statement evidence only when the right side is an independent hand statement". A person confirms whether it is independent.
If `--compose` has no `--same-as`, the theorem line gets an `UNCHECKED STATEMENT` mark and `kindcheck.py` rejects it.
`--same-as-prop NAME` writes an identity with a hand-written Prop `abbrev`. We tested it only with scratch fixtures.
`--gen2 --partial-out` now writes a valid Lean module. The fields that it cannot cover are in `UNCOVERED-JSON` lines with the reason.
`kindcheck.py` rejects this file by default. `--partial` checks the kind of the theorems that are there and gives exit 3.
`Gen2BhDecPartial.lean` (BeaconBlockHeader 3/5, in-sample) is untouched output and builds.
Executed checks (`--gen2` generator unit): declaration comparison only ADDED 201, negative tests 17/17.
Executed checks (after the fix unit): axioms gate PASS (4726 declarations), only ADDED 6 against the dump of the generator-unit review.
`p2dec_test.py` 51/51, `kindcheck.py` 70 self-tests PASS, all 7 checkers that we broke on purpose fail.
`regen_check.sh` 15/15 SAME (old 8, `--gen2` 6, partial output 1), `lake build --no-build` exit 0.
In the fix unit, we did not run the negative tests again.
Limits: 96-byte fields were not used in real code. The 48-byte add shape has only a text check on a synthetic `.S`.
BlobIdentifier and DepositMessage are in-sample data. All the cover counts above are in-sample results.
The H4 hold-out result is in the next paragraph. The in-sample results did not carry over unchanged.
The reviews of the `--gen2` lemma unit (`6c62a49`) and fix unit (`eacf0fb`) are APPROVE. The fix unit closed the two required fixes of the generator-unit review (`cd47028`).
The items to fix S1–S4 of the fix-unit review are checker (`kindcheck.py`) changes. They stay open proposals. We did not do them.
S1: make rule 6a look at the proof text without comments. S2: make `--partial` compare n with the theorem count.
S3: make the default mode reject a `GEN2 coverage` header with n ≠ m. S4: self-test controls for those two.
We could not make these changes because it was after the H4 freeze. Each gap opens only with a hand edit of a generated file. `regen_check.sh` shows that edit.
Records: section 14 of `scal/CONTAMINATION.md`, `gen2` of `scal/RESULT.json`, FINDINGS SG-2.

Hold-out H4 (method frozen at `eacf0fb`, opening record commit `9d338fa`, 2026-11-11T08:53:45Z, the review of H4 approved `fae7d6f`):
The scope is only `UnmarshalSSZ` of `v1alpha1.Deposit_Data` (class A) and `v1alpha1.PendingPartialWithdrawal` (class B). We opened the two types once.
Deposit_Data is the in-sample DepositMessage with a 96-byte Signature added. 3 of its 4 fields are close to the sample.
The hand statements `H4.dd_accept_stmt` and `H4.pw_accept_stmt` (`H4Stmt.lean`) were committed before we ran the generator (`d7e3304`).
Segment result (S), one `p2dec --gen2` per type: Deposit_Data exit 3, 3 of 4 fields.
It covered PublicKey (48, 0 shape), Amount (inline, rsi) and Signature (96, add shape). The raw output was not touched (`Gen2DdDecPartial.lean`).
It could not cover WithdrawalCredentials. The code has a `nop` between `mov $0x20,%ecx` and `callq runtime.makeslice` (FINDINGS SG-3: `--gen2` coverage gaps on H4).
Of the 3 covered fields, PublicKey and Amount are close to the sample. The only covered field outside the sample is Signature.
The field that it could not cover has the 32-byte shape that the same generator covered in DepositMessage (item S1 of the review of H4).
`kindcheck.py --partial` is exit 3 (the success code of that tool). That file builds.
PendingPartialWithdrawal is exit 2, 0 of 3 fields. Index and WithdrawableEpoch are delegated overlays compiled as calls.
Amount is an inline read, but it is not the 3-directive shape (`mov 0x8(%rbx),%r8; mov %r8,0x10(%rax)`, SG-3).
Composed result (C), one `--compose --same-as-prop` per type: both rejected with exit 2. They have fields that it could not cover. The identity check did not run.
Hand work (after the generated output commit, only new H4 modules): we kernel-checked the Deposit_Data accept theorem `H4.dd_e2e_accept_main : dd_accept_stmt`.
That proof calls the three generated sections unchanged. WithdrawalCredentials is the new hand lemma `H4.bytes32dec_seg_nop` (`DdSegNop.lean`).
Also size reject, codec equivalence, specification alignment, `reject_complete`, witness `WitDdA` (receiver in Go layout), `WitDdR`.
We could not prove the PendingPartialWithdrawal accept theorem. It hit the limit of 3 attempts (term shape of `ecancel` at the last frame).
For PendingPartialWithdrawal, we kernel-checked only size reject, codec equivalence, the reject side of the specification and witness `WitPwR`.
`pw_e2e_reject_complete` is only a fact on the specification side (EthLib reject → size ≠ 24).
We did not exclude the two other error returns of this decoder (wrapped errors of the called decoders) (S4).
Hand lines (count without blank lines and comment lines): Deposit_Data accept path 336 (DdAccept 148, DdSegNop 188), H4Stmt 112. H3: BlobIdentifier 210, DepositMessage 464.
The types are different. We do not claim a cause from these line counts.
It is not a comparison under the same conditions. 336 excludes the statement module `H4Stmt.lean` (112), and the 210 and 464 of H3 include the statements (S3).
The tools are in no count: `h4link.py` 159, `h4diff.py` 71, `h4check-main.go.txt` 74, `negcases-h4.json` 271.
Executed checks: link check PASS (`h4/link/RESULT`), negative tests 30/32, Go differential 12/12 (Go semantics on arm64, not the ELF).
In the negative tests, 1 memory cap kill and 1 heartbeat timeout do not count as a pass.
30/32 includes cases that changed after the first run (S6). `dd-segnop-stmt-ret` ran again after the case text was fixed.
The four retracted `dd-acc-*` cases were changed to code mutations of the generated sections after the results were seen.
Axioms gate PASS (5007 declarations, 0 nonstandard), only ADDED 281 against the dump of the `--gen2` fix-unit review.
The declaration comparison control of the evaluator was an edit of the dump text. It tests only `decl_drift.py` (S5).
The review of H4 ran the Lean-level planted control. Both the axioms gate and the declaration comparison caught it.
Gate seconds: Deposit_Data 294.2, PendingPartialWithdrawal 36.5, shared 224.1, base build 86.7.
Limit of H4: two types, one time. There is no claim of generality, superiority or speed.
The review of H4: 0 required fixes. Items to fix S1–S7 were closed with documents in the integration of `--gen2` and H4 (`scal/RESULT.json` `H4.review_h4_r1`).
Not confirmed by the review of H4: Go differential, 20 of the 32 negative tests, cold build from an empty `.lake`, x86-64, runtime contracts.
Records: sections 16 and 17 of `scal/CONTAMINATION.md`, `H4` of `scal/RESULT.json`, FINDINGS SG-3.

Integration of the `--gen2` work and H4 (merges `claude/ssz-fv-h4` `fae7d6f`, merge commit `56e0c88`, the review of this integration approved `6a78c59`):
The merge tree id is the same as the tree id of `fae7d6f`. We did not change proof text, statements, generators or checkers.
Executed checks (inside the gate and the 6 GiB cap): `lake build E2e E2eAd E2eScal` exit 0, only the 35 new modules were built.
`E2eScal.P2EncCp` was not built again. `lake build --no-build` exit 0.
Axioms gate PASS, 5007 declarations. The output is byte-identical to the committed `axioms-gate.json`.
Declaration comparison against the dump of the H4 review: CHANGED 0, REMOVED 0, ADDED 0. The dump-level planted control was caught (exit 1).
`regen_check.sh` 16/16 SAME (old 8, `--gen2` 6, partial output 2). It is not an H4 run. It is an integration check.
`kindcheck.py --selftest` 70 PASS, `p2dec_test.py` 51/51.
Not run (integrator): Lean-level planted control, cold build, link check, Go differential, negative tests, x86-64.
Records: `integration_int4` of `scal/RESULT.json`.
The review of this integration: 0 required fixes, items to fix S1–S3. S1 and S2 were closed with documents in the integration of `--gen3` and H5. S3 is a record only.

`--gen3` generator unit (base `f5c5f52`, proof generator change, development data only, the review of this unit approved `6dc0e2a`):
`scalgen.py p2dec --gen3` produces the three shapes of the `--gen3` lemma unit. The default mode and `--gen2` outputs are unchanged.
The three shapes: call fields of callee decoders that have a proved specification, two-directive uint64 reads, padding `nop` before makeslice.
In-sample coverage: PendingPartialWithdrawal 3/3, Deposit_Data 4/4, BeaconBlockHeader 5/5, AttestationData 3/5.
With `--gen2` it was 0/3, 3/4, 3/5, 1/5. This is not transfer. The hold-out measurement is H5.
For Deposit_Data, it also generated the composition (`Gen3DdAccept2.lean`). The statement check is the kind `decAcceptKind` and the identity with `H4.dd_accept_stmt`.
`--compose` rejects types that have call fields. Their accept theorems are hand compositions that call the generated theorems (`PwAcceptG3`, `BhAcceptG3`).
The types of the two hand compositions are equal by `rfl` to the existing hand theorems. The head, the tail and the BeaconBlockHeader pointer tail are hand steps.
Hand lines (count rule: lines without blank lines and comment lines): proof body PendingPartialWithdrawal 98 → 75, Deposit_Data 136 → 0.
The BeaconBlockHeader head body is 159 → 140 (includes hand steps), and the accept body is 150 → 150. For the full module, it did not decrease.
The `--gen3` lemma modules (written by hand once) are 905 lines. There is no speed claim.
Composition run 1 was a syntax error (generator bug). We keep the raw output in `scal/gen3/` and used the fixed run 2.
Executed checks: `regen_check.sh` old 16/16 SAME, the 5 new ones are deterministic. The default/`--gen2` differential is 30/30 same.
`kindcheck.py --selftest` 114 cases and 4 exit-code cases PASS, 15/15 checkers that we broke on purpose fail. `p2dec_test.py` 88/88.
Negative tests 17/17 (4 controls, 13 fail in the theorem, 0 timeouts). Axioms gate PASS, 5463 declarations, 0 nonstandard.
The declaration comparison against the dump of the review of the `--gen2` and H4 integration is only ADDED 456. The planted control was caught. `lake build --no-build` exit 0.
Not run: cold build, link check, Go differential, x86-64. Records: CONTAMINATION section 19, `gen3` of `scal/RESULT.json`.
The review of the `--gen3` generator unit: 0 required fixes, items to fix S1–S6. The document items were closed in the integration of `--gen3` and H5 (`gen3.review_g3g_r1`).
"n/m covered" means that the template directives of n fields are proved. It is not a decoder proof (S1).
The first-field argument shape has no SSZ offset parameter. It does not read directives outside the template section.
Shapes that it does not cover further (S3): plain uint64 at offset 0, the `lea` shape without the two-directive read of the earlier field.
In the differential, the bytes are the same in all outputs. Only the usage text is different, because `[--gen3]` was added (S6).
Checkpoint is 2/2 with a composition reject in the reviewer run (S5). There is no committed file.
S2 (`kindcheck.py` requires the coverage header and removes strings in rule 6a) is a checker change. It stays an open proposal.
The review of the `--gen3` lemma unit (`f5c5f52`): APPROVE, 0 required fixes, items to fix S1–S5.
S1: we observed the `nop` of the pointer tail (BeaconBlockHeader.ParentRoot, Checkpoint.Root) and do not cover it. The generator unit closed S4 and S5.
Open: S2 `maxHeartbeats 16000000` of `pw_e2e_accept_main` (it elaborates at 4000000). S3 there is no statement mutation for that theorem.
Both need a `.lean` edit or a negative test. We did not do them in the integration.

Hold-out H5 (method frozen at `6dc0e2a`, opening record commit `3762644`, 2026-11-11T11:25:14Z, the review of H5 approved `1fec11e`):
The types are `UnmarshalSSZ` of SyncCommitteeMessage (C) and PendingConsolidation (D). Two types, one time.
By field kind, the two types are close to the sample (selection record H5-A3). Only the order of the kinds is new.
The hand Desc (`08adf1d`) and the hand statements `H5.sm_accept_stmt`, `H5.pc_accept_stmt` (`3c4625c`) were committed before the generator run.
Segment result (S): SyncCommitteeMessage 2/4 (exit 3, Slot, Signature), PendingConsolidation 1/2 (exit 3, SourceIndex).
Reasons it could not cover: BlockRoot reads the receiver again into rax. ValidatorIndex is an argument shape that was not observed.
TargetIndex has a `nop` after the call. The raw output was not touched. `kindcheck.py --partial` is exit 3 (success code).
Composed result (C): both rejected (exit 2, "all fields must be covered"). This result was known before the freeze. The identity check did not run.
The generated `_call` theorems have `hC : U64CalleeAcc` as a premise. They are conditional.
Hand work (only new H5 modules): we kernel-checked the two accept theorems. Only the three standard axioms.
`sm_e2e_accept_main` calls three generated theorems (two for Slot, one for Signature). The `hC` of Slot is filled with `sl_uacc_holds`.
`pc_e2e_accept_main` calls two generated theorems (SourceIndex). `hC` is filled with `vi_uacc_holds`.
The rest are hand lemmas (`SmSeg.lean`, `calldec_nop_seg`) and existing `--gen3` lemmas (`calldec_seg`, `callarg_reload_seg`).
We also kernel-checked size reject, codec sameness with the checker Desc, specification alignment, `reject_complete` and four witnesses.
The accept witnesses `WitSmA` and `WitPcA` show that the premises of the hand statements are satisfiable (receiver in Go layout).
Hand lines (count rule, full module): SyncCommitteeMessage accept path 549 (SmAccept 199, SmSeg 350), PendingConsolidation 271 (PcAccept).
The statement module `H5Stmt.lean` is 114 (two types) and is not in the counts above. Proof bodies only: 188, 69.
For reference (no causal claim, different types): H4 Deposit_Data 336 (statement 112 separate), H3 210 and 464 (statements included), `--gen3` PwAcceptG3 87.
Executed checks: link check PASS (bundle `d532fc57`). Negative tests 37/41 (12 controls, 25 fail in the theorem).
4 cases ended with a heartbeat timeout (spec_k postcondition mutations). They do not count as a pass.
No mutation targets `sm_e2e_accept_main` or `pc_e2e_accept_main` (item S3 of the review of H5).
Because of the 4 timeouts, `pc_e2e_accept_spec_k` has no counted mutation.
Axioms gate PASS, 5841 declarations, 0 nonstandard. The declaration comparison against the dump of the `--gen3` generator review is only ADDED 378. The planted control was caught.
The planted control of the evaluator was an edit of the dump text. The review of H5 ran the Lean-level planted control (S5).
Go differential 12/12 (Go semantics, linux/arm64, not the ELF). The planted control gives 2 mismatches.
Not proved: callee error paths, morestack, `writeBarrier ≠ 0`, the Lean Go value predicate, the `Pm` witness of spec_k, x86-64.
`*_reject_complete` proves only "EthLib reject → size ≠ N" (N = 144, 16).
In its doc comment, "reaches the `ssz.ErrSize` site" says more than the theorem (S4). It is a `.lean` edit, so we keep it open.
Attempts: SyncCommitteeMessage accept theorem 3 (the last succeeded), SmSeg 2, reject 2, the rest 1. It did not reach the limit.
Task 22 tested a candidate fix separately together with a reproduction. It is not an attempt on the obligation itself (S5).
Gate seconds (gate record, item S2 of the review of H5): SyncCommitteeMessage 365.0, PendingConsolidation 261.4, shared 315.0, base build 19.7.
Total 961.1 s, 77 gate tasks. The shared 191.7 of the evaluator excluded tasks 84 and 85.
Limit: two types, one time. There is no claim of generality, superiority or speed. We did not change the H4 record.
Records: section 20 of `scal/CONTAMINATION.md`, `H5` of `scal/RESULT.json`, FINDINGS SG-4 (coverage of the `--gen3` generator on H5).
The review of H5: 0 required fixes, items to fix S1–S7. The six except S4 were closed with documents in the integration of `--gen3` and H5 (`H5.review_h5_r1`).
Not confirmed by the review of H5: Go differential, 29 of the 41 negative tests, cold build from an empty `.lake`, x86-64, runtime contracts.

Integration of the `--gen3` work and H5 (merges `claude/ssz-fv-h5` `1fec11e`, merge commit `2bedf6d`, the review of this integration approved `fbbc382`):
The merge tree id is the same as the tree id of `1fec11e`. We did not change proof text, statements, generators or checkers.
Executed checks (inside the gate and the 6 GiB cap): `lake build E2e E2eAd E2eScal` exit 0, only the 39 new modules were built.
`E2eScal.P2EncCp` was not built again. `lake build --no-build` exit 0.
Axioms gate PASS, 5841 declarations. The output is byte-identical to the committed `axioms-gate.json`.
Declaration comparison against the dump of the H5 review: CHANGED 0, REMOVED 0, ADDED 0. The dump-level planted control was caught (exit 1).
`regen_check.sh` 23/23 SAME (16 of the previous integration, `--gen3` 5, H5 partial output 2). It is not an H5 run. It is an integration check.
`kindcheck.py --selftest` 114 cases and 4 exit-code cases PASS, `p2dec_test.py` 88/88.
Not run (integrator): Lean-level planted control, cold build, link check, Go differential, negative tests, x86-64.
Records: `integration_int5` of `scal/RESULT.json`. The table of consecutive hold-out results is in section 4 of `prysm/BASELINE.md`.

`--gen4` generator unit (base `718e023`, proof generator change, development data only, the review of this unit is REQUEST_CHANGES, fixed by the first `--gen4` fix below):
The new mode is `p2dec --gen4`. The default, `--gen2` and `--gen3` outputs are byte-identical (old commands 23/23 SAME).
The match is data flow, not a template. The generator produces a block only when its walk trusts the entry state.
"Covered" is a claim of the generator. See the first-fix paragraph below.
It produces one step theorem and one kind line per instruction. `nop` goes into the window.
In-sample coverage (`--gen4` / `--gen3`): Checkpoint 2/2 / 2/2, AttestationData 3/5 / 3/5, BeaconBlockHeader 5/5 / 5/5.
Eth1Data 3/3 / 3/3, BlobIdentifier 2/2 / 2/2, DepositMessage 3/3 / 3/3, Deposit_Data 4/4 / 4/4.
PendingPartialWithdrawal 3/3 / 3/3, SyncCommitteeMessage 4/4 / 2/4, PendingConsolidation 2/2 / 1/2.
Fields not covered: AttestationData Source, Target. The class is "new field kind".
This is not transfer. All types are development data. The hold-out measurement is H6.
`--gen4 --compose` rejects. Field composition, head and epilogue have no kind.
We proved three accept theorems as hand compositions of generated chains: `sm_e2e_accept_g4gen`, `pc_e2e_accept_g4gen`, `pw_e2e_accept_main_g4gen`.
Their types are the frozen hand statements. There was 1 attempt per theorem.
Hand lines (count rule, module / proof body): SyncCommitteeMessage 355 / 217, PendingConsolidation 150 / 91, PendingPartialWithdrawal 163 / 102.
The per-type hand head and epilogue lemmas are not in the counts above: 114, 121, 121. The `--gen4` lemmas (written once) are 1640 lines.
Generated lines (code): Gen4SmDec 457, Gen4PcDec 213, Gen4PwDec 268.
The SyncCommitteeMessage generated chain is more than 400 lines. By the honesty condition of the plan, we record it as a problem.
No module takes more than 120 s. The longest is 3.6 s. There is no speed claim.
`kindcheck.py`: selected tests 157+4, broken-on-purpose copies 14/14 fail. `p2dec_test.py` 134/134.
Negative tests 17/17, axioms gate PASS (7080 declarations), declaration comparison only ADDED 1239, the planted control was caught.
Records: section 22 of `scal/CONTAMINATION.md`, `gen4` of `scal/RESULT.json`, FINDINGS, `gen/scal/README.md`.

First `--gen4` fix (after the review of the generator unit, REQUEST_CHANGES, base `21b8aab`, the review of this fix is REQUEST_CHANGES, fixed by the second fix):
"Covered" (`--gen4`) is a claim of the generator.
Each produced theorem gets a kernel check, one by one.
The kernel does not check whether the step chain makes the block entry state.
It also does not check whether a call block belongs to the named IR field.
Only the hand field composition checks that. Three types have a composition.
So the hold-out result (S) is "the walk covered + each theorem builds". It is not "field proved".
On 7 review inputs, the earlier walk said "covered" without an entry state. All theorems built.
Fixed rule: head directives 2–10 must be the same as the `decpro_seg` head.
Stack stores must be multiples of 8 and inside the frame or the argument save slots. If not, the walk stops.
If it writes to rbp or r14, the walk stops.
50 review inputs: safe 50/50, 7/7 dangerous inputs rejected, 11/11 valid variants covered.
The 10 committed `Gen4*.lean` files are byte-identical. Old commands 23/23 and `--gen4` 10/10 are SAME.
`p2dec_test.py` 160/160, `kindcheck.py` selected tests 157+7 PASS. The declarations did not increase.
Not checked: after the last field event (epilogue). The head position is fixed (`cmp` at 9, `jne` at 10).
Fields after a miss are `reached: false`. We did not resume the walk after a miss (there is no sound basis).
Records: the first-fix section of `gen/scal/README.md`, section 23 of `scal/CONTAMINATION.md`.
Second fix (after the review of the first fix, the review of this fix is REQUEST_CHANGES, fixed by the third fix): it compares the immediate of the head `cmp $size,%rcx` with the IR SSZ fixed size.
Second fix: it now checks the epilogue. After the last field event, it refuses stores, calls and other frame sizes (a34 reject).
Second fix: the "does not check the epilogue" above changed to this rule. It does not yet look at the targets of the head `jbe` and `jne`.
Second fix: all 83+50 review inputs are safe. `p2dec_test.py` 169/169. Records: README second-fix section, CONTAMINATION section 24.
The "checks the epilogue" of the second fix went too far. It accepted a `jmp` to a label that is not in the file (item M4 of the review of the second fix).
Third fix (after the review of the second fix, the review of this fix approved `0e775ac`, the H6 method freeze): that `jmp` is now an epilogue miss. Exit 2, not all fields covered.
Third fix: the result logic is fail-closed. Exit 0 comes from only one place.
Third fix: that place is reached only when all three success flags (head, all fields, epilogue) are set.
Third fix: any other exception at any step is exit 2. The injection tests (`fc-*`) confirm this.
Third fix: not checked: the return value (nil error), makeslice type literals, optional nil checks, duplicate labels, the head `jbe` / `jne` targets.
Third fix: all 50+83+89 review inputs are safe (x35 counts with the true value that the reviewer fixed). `p2dec_test.py` 262/262.
`--gen4` review results (added in the integration of `--gen4` and H6): the review of the lemma unit approved `718e023`. The review of the generator unit is REQUEST_CHANGES (`21b8aab`).
Why three fixes: each review found one path where `--gen4` produced "covered" without a check.
Item M1 of the generator-unit review: overlapping stack stores and a different head. Item M3 of the first-fix review: the head size immediate was not compared with the IR.
Item M4 of the second-fix review: an epilogue `jmp` to a label that is not in the file.
So the third fix changed the result logic to fail-closed. The review of the third fix approved it (0 required fixes).
The items to fix of the third-fix review are S6–S9. S7 and S8 are document items, and S6 and S9 are generator changes.
S6: a `NoMatch` inside a step can leave "covered" in the summary (not reachable with the current code).
S7: on exit 3, it does not check the code after the stop. S8: the summary of head and epilogue exceptions has no `fail_closed` key.
S9: on exit 0 / 2, a stale `--partial-out` file stays.
S7 and S8 are written in this paragraph and in `gen/scal/README.md` (closed). S6 and S9 are open proposals (not done).
Items S1–S4 of the lemma-unit review and S1–S3 of the generator-unit review were closed or recorded in the generator unit and the first fix (`gen/scal/README.md`, `scal/RESULT.json`).

Hold-out H6 (method frozen at `0e775ac`, opening record commit `dcc71a8`, 2026-11-11T17:18:33Z, the review of H6 approved `8ce5dda`):
The batch is all 7 types of the frozen rule. The scope is `UnmarshalSSZ`. The hold-outs of this population are now all used.
By field kind, several types are close to the development types (selection record H6-A5). So it measures only compiler variation of known kinds.
The hand Desc (`c7ebeee`) and the hand statements `H6.pd_accept_stmt`, `H6.pb_accept_stmt` (`0ad71a7`) were committed before the generator run.
Segment result (S), one `--gen4` per type: PendingDeposit 5/5, PowBlock 3/3, HistoricalSummary 2/2, SigningData 2/2.
SyncAggregatorSelectionData 2/2, ValidatorBalance 2/2, VoluntaryExit 2/2. Total 18/18, reached 18/18.
All runs are exit 0. The head and the epilogue are also covered. There is no miss, so there is no miss classification.
The raw output was not touched. All of it builds and passes the full mode of `kindcheck.py`.
"Covered" is a claim of the walk. It is not a field proof. Only the two types below have a composition.
Composed result (C): reject by design. By the freeze record, we did not run it.
We kernel-checked two accept theorems: `pd_e2e_accept_g4gen`, `pb_e2e_accept_g4gen`. Only the three standard axioms.
All 8 generated chains (PendingDeposit 5, PowBlock 3) closed in the hand composition as produced. There were 0 fixes.
For those 8 fields, the kernel confirmed the "covered" claim of the walk. The other 10 fields have no composition.
The `hC` of Slot is filled with `sl_uacc_holds`. There is no new contract form.
What stays by hand: field composition, the head and epilogue of PendingDeposit (from `decpro_seg`, `kstep_st`, `kstep_add`, `decret_seg`), connecting text.
The head and epilogue of PowBlock are the existing `dechead_seg` and `decepi_seg`.
We also kernel-checked size reject, specification alignment, `reject_complete` and four witnesses.
PowBlock: `total_difficulty` in the specification is `uint256`, and the producer Desc is 32 bytes. The bytes on the wire are the same.
So instead of Desc sameness, we proved the same accept inputs and the number / little-endian byte correspondence.
Hand lines (count rule, module / proof body): PendingDeposit 470 / 262 (includes 91 of per-type lemmas), PowBlock 259 / 132.
The statement module `H6Stmt.lean` is 133 (two types) and is not in the counts above. The PendingDeposit hand module is more than 400 lines.
Generated lines (code): Gen4H6PdDec 522, Gen4H6PbDec 348. For reference (no causal claim): SmAcceptG4gen 355 / 217.
Executed checks: link check PASS (bundle `eb1d6846`, 7 types). Negative tests 36/36 (9 controls, 27 fail in the theorem).
Axioms gate PASS, 7650 declarations, 0 nonstandard. The declaration comparison against the dump of the first-fix review is only ADDED 570. The planted control was caught.
Go differential 12/12 (Go semantics, linux/arm64, not the ELF). The planted control gives 2 mismatches.
Not proved: Slot error path, morestack, `writeBarrier ≠ 0`, the Lean Go value predicate, the `Pm` witness of spec_k, x86-64.
Attempts: 2 for each of the two accept theorems (the first was a connecting-text error), PbSpec 2, the rest 1. It did not reach the limit.
Gate seconds: part 1 16.5, PendingDeposit 100.4, PowBlock 60.4, shared 265.8.
Limit: one measurement. There is no claim of generality, superiority or speed. We did not change the earlier hold-out records.
Records: section 26 of `scal/CONTAMINATION.md`, `H6` of `scal/RESULT.json`, FINDINGS SG-5 (coverage of the `--gen4` generator on H6).
The review of H6 (added in the integration of `--gen4` and H6): APPROVE, 0 required fixes, items to fix S1–S9 (`H6.review_h6_r1`).
S1: (S) 18/18 is a claim of the walk. The types are close to the development types (H6-A5), and there is no similarity filtering. We wrote this in section 0.
S2: H3 1/2, 1/3, H4 3/4, 0/3, H5 2/4, 1/2, H6 18/18 have different populations and filtering. They are not a trend.
S2: H5 had a similarity record, and H6 has no filtering. We do not write the causal sentence "coverage went up".
S2: not covered yet: nested containers (`*Checkpoint`), lists, bitfields, other sizes, callees without a proved specification, encoders.
S3: the gate seconds are 642.5 s for 84 tasks. Shared is 464.5 s with tasks 89 and 90 included. The 265.8 above excluded those two.
S4: `PdAccept.lean`, `PbAccept.lean` and the two `*SpecK.lean` are outputs of the per-type template script of the evaluator.
S4: the script is not in the repository. "hand-written" in the header means "not the generator".
S4: so the hand line counts are not counts of lines that a person typed. They measure the amount of text outside the generator.
S5: theorems with no mutation in 36/36: the two accept theorems, the two `*_accept_spec_k`, the files of the 5 types with only (S).
S6: the doc comment of `*_reject_complete` says "reaches the `ssz.ErrSize` site". The proved fact is only `size ≠ N`. We did not fix the comment (`.lean` edit, open).
S7: the declaration comparison control of the evaluator was an edit of the dump text. The Lean-level control of the reviewer covers it.
S8: four commit types `spec(kraken)` and one `test(link)` are scope names. Record only. S9: a curator temporary script was in `/tmp`. Record only.
Not confirmed by the review of H6: Go differential rerun, 21 of the 36 negative tests, cold build from an empty `.lake`, kernel composition of the 10 fields with only (S), x86-64.

Integration of the `--gen4` work and H6 (merges `claude/ssz-fv-h6` `8ce5dda` on top of `3e1cedc`, merge commit `9d8aaf9`, the review of this integration approved `c29ebdc`):
The conflicts were in 8 record files, one hunk each. We kept both sides (our side first). We did not change the numbers.
All `.lean` files are the same as `8ce5dda`. The exception is `E2eScal/P2EncCp.lean`, which is the same as `74cc9ca`.
This is the first build of the tree that contains the ARM task B fix (AU-07). We did not change proof text, statements, generators or checkers.
Executed checks (inside the gate and the 6 GiB cap): `lake build E2e E2eAd E2eScal` exit 0, 1164 jobs, 124.7 s.
53 modules were built: the 52 new modules of the stream and `E2eScal.P2EncCp`.
`E2eScal.P2EncCp` was built again here in 10 s (Lake display, n = 1). We do not make a speed claim.
The maximum memory is the value for the full build: process 3.40 GiB, session 2.66 GiB. We did not measure the value of one module.
`lake build --no-build` exit 0.
Axioms gate PASS: 7649 declarations, 6440 theorems, 280 modules, hand list 1186, 0 nonstandard, 0 sorryAx.
We made the committed `axioms-gate.json` again in this tree (7650 → 7649).
Declaration comparison against the dump of the H6 review: only `cp_e2e_marshal_main_s._proof_1_23` REMOVED and `_proof_1_13`–`_22` CHANGED.
For n = 13…22, the head `_proof_1_n` is the same in all columns as the base `_proof_1_(n+1)`. The main theorem row and all other rows are the same.
We allowed those 11 lines by name and reason (ARM task B fix). The planted control (dump level) is exit 1.
`regen_check.sh` 40/40 SAME (the earlier 23, `--gen4` 10, H6 segment results 7). It is not an H6 run. It is an integration check.
`kindcheck.py --selftest` 157 cases and 7 exit-code cases PASS, `p2dec_test.py` 262/262.
Not run (integrator): Lean-level planted control, cold build from an empty `.lake`, link check, Go differential, negative tests, x86-64.
Records: `integration_int6` of `scal/RESULT.json`.

`--gen5` generator unit (base `94fd8a6`, the review of the `--gen5` lemma and generator units is REQUEST_CHANGES, records only, closed by step 0 of the close-out unit): `p2dec --gen5` produces the full accept theorem of flat decoders.
Produced theorems: head, one per field, epilogue, accept, size reject. Each theorem has a kind line of the `--gen5` lemma unit.
The result is fail-closed. Exit 0 comes only from the one place where all five success flags are set.
The committed run is once per type (gate task 04). We committed the raw output first, without edits (`8192427`).
Before that, there were five scratch test runs. All five ran without the gate (procedure violation, CONTAMINATION section 30).
Generated accept theorems: 15 of the 17 flat development types. All build and use only standard axioms.
Refused: PendingPartialWithdrawal (mixed fields), AttestationData (nested field).
Statement check: kind lines and `kindcheck.py` rule 12. Rule 12 computes the kind parameters again from the IR and the `.S`.
For the 9 types with a hand statement, the generated theorem is equal by `rfl` to that hand statement.
Checkpoint is only a kind instance. Its layout `layCp` and chunk order are different from those of the implication `cp_accept_of_kind`.
For the frame `0x38` shape of SyncAggregatorSelectionData and ValidatorBalance, there was no hand-bound statement at the time of the generator unit.
The two independent hand statements of the close-out unit are equal by `rfl` to the generated accept theorems (below).
`kindcheck.py` does not bind the constant `C` to the `.S` of the head. `C` freezes only the Lean code facts.
The statements of the 5 types without a hand statement (HistoricalSummary, SigningData, SyncAggregatorSelectionData, ValidatorBalance, VoluntaryExit) are kind instances.
With the generator unit alone, these 5 were not complete decoder proofs. The close-out unit added reject completeness, Desc, specification and witnesses (below).
Finding SG-6: the accept kind does not read `L.frame`. Rule 12c compares the `L` of all kind lines.
Module elaboration is 2.1–8.6 s (n = 2). No module takes more than 120 s. There is no speed claim.
`regen_check.sh` 55/55 SAME (old 40, `--gen5` 15). `p2dec_test.py` 394/394, `kindcheck.py` selected tests PASS.
22 of the 25 negative tests pass (4 controls, 18 fail in the theorem). 1 timeout, 1 no-error and 1 outside error are not counted.
Axioms gate PASS (9139 declarations), declaration comparison only ADDED 1490, the planted control was caught. `--no-build` exit 0.
Not run: cold build, link check, Go differential, x86-64. Records: CONTAMINATION section 29, `gen5` of `scal/RESULT.json`.

Close-out of the five remaining flat decoders (close-out unit, base `ea6a0c6`, the review of this unit is REQUEST_CHANGES, inventory only, proof checks passed): HistoricalSummary, SigningData, SyncAggregatorSelectionData, ValidatorBalance, VoluntaryExit.
Accept and size reject are the generated theorems of the `--gen5` generator unit. The others are new modules.
The three independent hand statements (SyncAggregatorSelectionData, ValidatorBalance, VoluntaryExit) are equal by `rfl` to the generated accept theorems. The hand statements were committed before the generated files were opened.
Proved per type: codec sameness of the hand Desc and the checker Desc, `accept_spec_k`, `reject_size_spec`, `reject_complete`, accept witness, reject witness.
`reject_complete` is only the size path condition. It does not cover callee error returns.
ValidatorBalance has no consensus-specs container. The Desc comes from the Prysm proto.
We added `pw_e2e_accept_spec_k` of PendingPartialWithdrawal.
43 of the 46 negative tests pass (10 controls, 33 fail in the theorem). The 3 heartbeat timeouts are not counted.
Go differential 30/30 (Go semantics on linux/arm64, not an ELF run). The planted control was caught.
Link check PASS. RESULT is byte-identical to the H6 record.
Axioms gate PASS (9758 declarations), declaration comparison only ADDED 619. The planted control was caught. `--no-build` exit 0.
The verification inventory is `prysm/INVENTORY.md`. Its source is `gen/tools/inventory.py` (the inventory fix unit fixed items M1–M3 of the close-out review).
The review of the inventory fix unit approved `be21280`. That review made the counts below again and they were the same.
There are three denominators. Do not mix them.
(1) SSZ methods of the target: 1292 for 211 types. The source is `prysm/go1.26.10/ssz-methods.json`.
This file is made from the nm list of the pinned ELF. The nm sha256 is the same as in `build-ids.txt`. The nm list is not committed.
(2) Dumped functions (`functions.json`): 641. 639 SSZ methods and 2 runtime helpers.
(3) The development population of the `--gen5` work: 16 flat types (`FLAT16`). It is not all flat fixed-size types of the target.
| Method | Target | `functions.json` | Matching rows | Complete | Partial |
| --- | --- | --- | --- | --- | --- |
| `UnmarshalSSZ` | 211 | 211 | 21 | 17 | 4 |
| `MarshalSSZTo` | 211 | 211 | 3 | 0 | 3 |
| `MarshalSSZ` | 211 | 6 | 0 | 0 | 0 |
| `SizeSSZ` | 211 | 211 | 1 | 0 | 1 |
| `HashTreeRoot` | 211 | 0 | 0 | 0 | 0 |
| `HashTreeRootWith` | 211 | 0 | 0 | 0 | 0 |
| `ProgressiveHashTreeRoot`, `…With` | 10, 10 | 0 | 0 | 0 | 0 |
| `MaxSizeSSZ` | 6 | 0 | 0 | 0 | 0 |
"Complete" is defined only for `UnmarshalSSZ`. For the other methods, one theorem or more makes it "partial".
For the decoder, 17 of the 211 target `UnmarshalSSZ` are complete. Complete has the meaning defined in the inventory.
HashTreeRoot, HashTreeRootWith and MarshalSSZ are in the target. There are no theorems. The HashTreeRoot family was not dumped.
The decoders of the 16 types of the development population are 16/16 complete (defined meaning). They are in-sample.
By the IR rule, the target has 40 flat fixed-size types. 24 of them are not started. The names are in `INVENTORY.md`.
What the inventory cannot catch is in "What this table cannot detect" of `INVENTORY.md`.
`codec` and `reject_complete` are not bound to the type of the row. It checks only existence, kind and axioms.
Each line of the table uses the target count of the method kind as the denominator. 1292 is the sum of all kinds (item N3 of the review of the inventory fix).
Not in "complete": morestack, `writeBarrier ≠ 0`, runtime callee bodies (contracts), callee error returns, growslice / T-7, x86-64.
The work of the Go 1.26.3 phase is a different binary. We do not count it in this inventory.
Reproduction (in `fv/kraken`, `$NM` is the nm list of the ELF, `$O` is an empty directory, lean inside the gate):

```sh
python3 -I -B gen/tools/inventory.py methods "$NM" "$O/ssz-methods.json" && cmp "$O/ssz-methods.json" prysm/go1.26.10/ssz-methods.json
python3 -I -B gen/tools/inventory.py names "$O/names.txt"
(cd lean && lake env lean --run ../gen/tools/inventory_decls.lean "$O/names.txt" $(ls E2e/*.lean E2eAd/*.lean E2eScal/*.lean | sed 's/\.lean$//; s#/#.#g')) > "$O/decls.tsv"
python3 -I -B gen/tools/inventory.py run "$O/decls.tsv" "$O/I.md" "$O/I.json" && cmp "$O/I.md" prysm/INVENTORY.md
```

Not run: cold build, x86-64, `regen_check.sh` (no generator change). Records: CONTAMINATION sections 31 and 32, `gen5-close` of `scal/RESULT.json`.

`--gen5` review results (added in the `--gen5` integration):
One review looked at the lemma unit (`94fd8a6`) and the generator unit (`ea6a0c6`) together. The verdict is REQUEST_CHANGES, records only.
Statement trust, fail-closed, preservation and the lemma-unit checks (bound chain, no limit increase, binding) all passed.
An earlier review of the lemma unit ended in the middle because of the usage limit. We do not use its partial verdict as a result.
Step 0 of the close-out unit closed items M1 and M2 of that review (CONTAMINATION section 30). The review of the close-out unit confirmed that closure.
Items to fix of the lemma and generator review: S1 and S4 were recorded. The independent hand statements of the close-out unit closed S3.
Its item S2 is open. `kindcheck.py` rule 12 does not bind `C` to the `.S` of the head. A checker change is necessary.
The review of the close-out unit (`c4e1d74`): REQUEST_CHANGES, only inventory wording and script limits. All proof checks passed.
The inventory fix unit fixed its items M1–M3. The review of the inventory fix approved `be21280`. It made the counts again and they were the same.
Items to fix of the close-out review: the inventory fix unit applied S1. S4 was recorded.
Its item S2 is open (`VbDesc.lean` comment, `.lean` edit).
Its item S3 is open. 19 matching names are not in the `AxiomsScal.lean` hand list. `inventory_decls.lean` looks at the axioms on each run.
Items to fix N1–N4 of the review of the inventory fix:
N1 (open, script): `inventory.py run` trusts `ssz-methods.json` for methods that were not dumped.
N1: if you delete a line of that file and the sha cell stays the same, it is exit 0. Only the `methods` run and `cmp` bind that list.
N2 (open, script): a development-population type with no matching row ends with a KeyError, not a FAIL line. Exit 1, and no files are written.
N3 (open, script text): denominator 1 of `INVENTORY.md` says "1292 is the total of all lines below".
N3: in fact, each line uses the target count of the method kind (211, 10, 6). `INVENTORY.md` is script output, so we did not fix it.
N4 (closed here): the flat rule of the inventory is wider than the hold-out population rule. It includes all uint, bool and byte vectors of all lengths.
N4: with the narrow rule (uint64 as is or overlaid, byte vectors 32 / 48 / 96), there are 24 flat types: development 16, not started 8.

Integration of the `--gen5` work (merges `claude/ssz-fv-gen5` `be21280` on top of `c29ebdc`, merge commit `03cf086`, the review of this integration approved `93dae89`):
The stream is linear on top of `c29ebdc`. There were no conflicts. The merge tree id is the same as the tree id of `be21280`.
We did not change proof text, statements, generators, checkers, inventory scripts or pinned versions.
Executed checks (inside the gate and the 6 GiB cap): `lake build E2e E2eAd E2eScal` exit 0, 1284 jobs, 80.0 s.
60 modules were built. This is the same as the 60 `lean/` modules that the stream added.
`E2eScal.P2EncCp` was not built again. The `.olean` sha256 is the same before and after the build.
The maximum memory is the value for the full build: process 2.09 GiB, session 2.73 GiB. `lake build --no-build` exit 0.
Axioms gate PASS: 9758 declarations, 8134 theorems, 340 modules, hand list 2200, 0 nonstandard, 0 sorryAx.
The new gate JSON is byte-identical to the committed `axioms-gate.json`. So we did not write the record again.
Declaration comparison against the dump of the close-out review: 0 CHANGED, 0 REMOVED, 0 ADDED. The two dumps are byte-identical.
Planted control (dump level): a copy with a changed type hash of `G5C.vb_e2e_reject_complete` gives exit 1, CHANGED 1.
`regen_check.sh` 55/55 SAME (the earlier 40, `--gen5` 15). It is an integration check and not a new generator result.
`kindcheck.py --selftest` PASS (157 cases and 47 cases including rule 12), `p2dec_test.py` 394/394.
Inventory rerun: the output of `inventory.py methods` is byte-identical to the committed `ssz-methods.json`.
The outputs of `inventory_decls.lean` (inside the gate) and `inventory.py run` are byte-identical to the committed `INVENTORY.md` and `INVENTORY.json`.
That declaration table is also byte-identical to the table of the review of the inventory fix.
Not run (integrator): Lean-level planted control, cold build from an empty `.lake`, link check, Go differential, negative tests, x86-64.
Items to fix of the review of the `--gen4` and H6 integration (`c29ebdc`, APPROVE): S2 was closed by changing the status cell of that integration.
S1 was closed by appending dated text to `opt-r1/MANIFEST.md` and `opt-r1/RESULT.json`.
S3 (the two "21." sections of CONTAMINATION) is explained in section 27. We do not change the numbers.
S4 stays open: item S6 of the review of H6, items S6 and S9 of the third-fix review, item S4 of the review of the `--gen3` and H5 integration.
S5 record: the commit type `merge` is not in the type list. The `--gen5` merge also used `merge(kraken)`, like the earlier integrations. We do not rewrite history.
Remaining work (not started in this tree, or partial): encoders of flat types, nested containers, lists, vectors and bitfields, growslice and T-7, hash tree root.
The list and vector work on the other machine is not in this tree. We do not claim it here.
We did not adopt the OPT-R1 pilot. T-7 is deferred. Records: `integration_int7` of `scal/RESULT.json`.

`--gen6` encoder generator unit (base `d1e30ca`, the review of this unit approved `dcc6e80`): `p2enc --gen6` produces the fast path theorems of flat encoders.
The premises are `len + SizeSSZ ≤ cap` and the exact length of the byte vector fields. It is not a complete encoder result.
We did not prove the growslice branch, length reject or morestack. It does not step the growslice directives.
One module has the head, one theorem per field, the epilogue and the fast path theorem. Each theorem has a `_kind` line.
The kinds are `encHeadKindN`, `encFieldKindN`, `encEpiKindN` and `encFastKindN` of the flat-encoder lemma unit. The code is `gen/scal/gen6enc.py`.
Fail-closed: `p2enc_gen6` returns text from only one place. All five flags must be set. Any other case is exit 2.
One run (gate e2g 06, raw output `e426d84`): it generated all 16 flat types. 0 rejects. All 16 modules build.
Earlier test runs: gate 01 (scratch), 03 and 05 (`p2enc_test.py`), 04 (debug). All are recorded.
Hand statement binding: for BeaconBlockHeader and Eth1Data, `_stmt` proves the declared type of the hand theorem (definitional identity, the same as `rfl`).
Checkpoint goes through the implication `cp_marshal_of_kind`. The statements of the other 13 types are kind instances.
The statement check is the kind and `kindcheck.py` rule 13. Rule 13 computes the parameters again from the `.S` and the IR with its own parser.
What it computes again: the field list, the 9 layout cells, all boundary states. It also checks whether the code constant contains that `.S`.
The elaboration time (per file, n = 2) is from 2.2 s to 9.2 s (PendingDeposit). There is no speed claim.
`kindcheck.py` 16/16 PASS, selected tests PASS (157 cases and 85 cases), all 12 broken copies fail.
`p2enc_test.py` 322/322: 50 adversarial inputs (all rejected, 0 bytes of standard output), 4 valid variants (covered), 252 fault-injection rows.
Breakdown of the 252 fault-injection rows (item S1 of the review of the generator unit): 225 injections reached and rejected, 18 unreachable steps, 4 controls, 5 harness rows.
Negative tests 20/20: 4 controls, 16 fail in the target theorem (statement 5, IR versus code statement 3, kind parameter 4, code 4).
Axioms gate PASS: 11011 declarations, 0 nonstandard, 0 sorryAx. We added 421 new declarations of the preparation, lemma and generator units to the hand list.
Against the dump of the review of the `--gen5` integration (9758 rows): ADDED 1253, CHANGED 0, REMOVED 0. The planted control was caught (gate exit 1, CHANGED 1, ADDED 1).
`regen_check.sh` 71/71 SAME (old 55, new 16). `lake build --no-build E2e E2eAd E2eScal` exit 0.
Not run: cold build, link check, Go differential, x86-64, witnesses of the generated theorems, specification-conformance theorems (the work of the flat-encoder close unit).
All types are development data (in-sample). Records: `enc2-gen` of `scal/RESULT.json`, section 35 of `scal/CONTAMINATION.md`.


Flat-encoder close unit (base `dcc6e80`, approved by the review of the generator unit, the review of this unit is REQUEST_CHANGES, inventory only, fixed by the encoder inventory fix unit, the review of that fix approved `eec1d4f`): we closed the encoder fast path of the 16 flat types.
The premises are always `len + SizeSSZ ≤ cap` and the exact length of the byte fields. No encoder is complete.
We committed the four independent hand statements (`E2eScal/E2cStmt.lean`) before we read the generated theorems (`0d25193`).
The four are PowBlock (frame test), SyncCommitteeMessage (overlay uint64, 96 bytes, large guard), PendingPartialWithdrawal and Deposit_Data (48 and 96 bytes).
For all four, type of generated theorem = hand statement closed with `rfl` (`E2cSame.lean`, first attempt).
Witnesses (`WitE2c<X>.lean`): for all 16 types, they are bound to the generated fast path theorem itself. The receiver is the Go layout of the IR.
Each witness has two cases: empty prefix with `cap = SizeSSZ`, and 3-byte prefix with 5 spare bytes.
Specification-conformance theorems (`E2cSpec<X>.lean`, `<x>_e2c_spec_k`): output = prefix ++ `serialize` of the independent Desc.
The Desc is the one that the decoder specification conformance uses. The Desc of ValidatorBalance comes from the Prysm proto.
The evidence tool of the unit, `scal/e2c/e2cemit.py`, produced the witness and specification-conformance text. It is not the generator.
We did not try decode ∘ encode consistency (optional item).
Negative tests 96/96 as expected (6 per type: 2 controls, 1 fast path statement, 2 specification conformance, 1 witness). We did not count timeouts.
Link check: enc2 bundle PASS all, RESULT byte-identical (`scal/e2c/LINK-CHECK.txt`).
Go differential 192/192 (Go semantics, linux/arm64, not an ELF run). It caught the 2 planted mismatches.
We ran again the non-author recomputation script of the review of the generator unit: 16/16 same.
Reproduction: `python3 -I -B prysm/go1.26.10/e2e/scal/e2c/own_layout_e2g_r1.py` (from `fv/kraken`, pure Python).
Axioms gate PASS: 12177 declarations, 0 nonstandard, 0 sorryAx. We made the record again and added 270 to the hand list.
Against the dump of the generator-unit review: ADDED 1166, CHANGED 0, REMOVED 0.
The planted control was caught in a scratch copy: gate exit 1, CHANGED 1, ADDED 1, REMOVED 2 (auxiliary declarations). The copy was deleted.
Inventory (`prysm/INVENTORY.md`, source `gen/tools/inventory.py`): encoder fast path complete 16 / 211.
Fast path complete = fast path theorem + specification-conformance theorem + witness. Decoder complete is 17 / 211.
The 24/24 failure controls of the inventory script are as expected (earlier 15, encoder 5, per-type rules 4, encoder inventory fix unit).
The paths that are not proved are in the NOT proved column of `INVENTORY.md`, per type (per-type rules, encoder inventory fix unit).
All types: morestack. The 14 types without a reject theorem: all growslice branches.
The 9 of those 14 types that have byte fields: all length rejects. The inventory column also writes length reject only for those 9 types (item N2 of the review of the encoder inventory fix).
The 5 types without byte fields: PendingConsolidation, PendingPartialWithdrawal, SyncAggregatorSelectionData, ValidatorBalance, VoluntaryExit.
BeaconBlockHeader: the growslice branch, and the length reject with `cap < len + 112`.
All three reject theorems of BeaconBlockHeader have the premise `len + 112 ≤ cap`.
Checkpoint: the paths outside the `GrowsliceC`·`MemmoveC` contracts and the heap budget, and the T-7 remaining path.
PowBlock, HistoricalSummary, SigningData: the `moveSliceNoCapNoScan` branch of the epilogue frame test.
We showed that this branch is not taken under the fast path premise. We did not prove the branch itself.
Also not proved: the justification of the frame separation premise for all Go callers.
T-7 is deferred. The AttestationData encoder is not in this tree (other work).
All types are development data (in-sample). Records: `enc2-close` of `scal/RESULT.json`, section 36 of `scal/CONTAMINATION.md`.
The review of the close unit (`5072b63`): REQUEST_CHANGES, records only. All proof checks passed.
The encoder inventory fix unit fixed its item M1 (inventory script and records only, the review of the fix approved `eec1d4f`). Records: `fix_e2c2` of `enc2-close`.
Its items S1, S2 and S4 were applied. S3 is partial: the reproduction line is above. The gate script connection is open.

Flat-encoder review results (added in the flat-encoder integration):
One review looked at the preparation unit (`e1fd7c0`) together with the lemma unit. The link re-extraction and the survey rerun were byte-identical.
That review (`d1e30ca`): APPROVE, 0 required fixes. The declaration comparison is ADDED 570, CHANGED 0, REMOVED 0.
Its item S1 (stale `axioms-gate.json` at the lemma-unit head) was closed when the close unit made the record again. The gate of the flat-encoder integration confirmed it.
Its item S2: `WitVbM.lean` uses `maxHeartbeats 16000000` on two theorems.
S2: that value is the value of the model `WitE1M`. There is no profile record for the increase.
Its item S3 is open. The macro `eb` is declared with the top-level name `tacticEb` (`EncFieldN.lean`, `.lean` edit).
Its item S4: `enc2-lemmas.L2.moveSliceNoCapNoScan` of `scal/RESULT.json` names three types.
S4: the lemma unit proved only HistoricalSummary. For PowBlock and SigningData, the fast path theorems of the close unit showed it.
The correction for S4 is in the key `enc2-lemmas.correction_e2l_r1_S4`. We did not change the original value.
Its item S5 (witnesses of DepositMessage and HistoricalSummary) was closed by the close unit (`WitE2cDm`, `WitE2cHs`).
Its item S6: attempt A5 of ValidatorBalance was the third attempt on one item. Before it, there was no separate reproduction run.
The review of the generator unit (`dcc6e80`): APPROVE, 0 required fixes. The generator-unit paragraph above fixed S1 (fault-injection count 252).
Its items S2–S5 are open (checker and test code).
S2: rule 13 does not bind the `.S` label to `ir_type`. It also does not restrict import and open lines.
S3: one broken copy fails with a KeyError. `g6_ir` accepts an unmarked 8-byte field as u64.
S4: the IR versus code negative test changes only one theorem. There is no full-file mutation.
S5: for adversarial inputs, the survival check reports the reject reason first.
The review of the close unit (`5072b63`): REQUEST_CHANGES, only one inventory cell (M1). All proof checks passed.
What that review passed to the integration: the specification-conformance theorems discard the frame (`⋆ True`). The frame claim cites the fast path theorems.
The witnesses use `rt_memmove` and `S = 0` on a two-function host. This is satisfiability, not the linked ELF layout.
All statements have the premise `cap < 2^63`. They also have the separation of fields, receiver, stack and `dst[len:cap]` as premises.
The gate script connection of its item S3 is open. The flat-encoder integration ran that script once as a gate task.
The review of the encoder inventory fix (`eec1d4f`): APPROVE, 0 required fixes. It compared 16 cells with the dump, made the counts again and they were the same.
Its item N1 is open (script). The T-7 remaining text of the Checkpoint cell relies on `E2e.cp_e2e_marshal_grow_any_sharp`.
N1: the script does not check that name.
Its item N2 was closed here. We fixed the "14 types without a reject theorem" line above and the BASELINE cell by the byte field criterion.
Its item N3 is open (script text). The cell text "1 byte fields" is script output.

Integration of the flat-encoder work (merges `claude/ssz-fv-enc2` `eec1d4f` on top of `93dae89`, merge commit `e70492d`, the review of this integration approved `0923998`):
The stream is linear on top of `93dae89`. There were no conflicts. The merge tree id is the same as the tree id of `eec1d4f`.
We did not change proof text, statements, generators, checkers, inventory scripts or pinned versions.
Executed checks (inside the gate and the 6 GiB cap): `lake build E2e E2eAd E2eScal` exit 0, 1412 jobs, 296.3 s.
64 modules were built. This is the same as the 64 `lean/` modules that the stream added.
`E2eScal.P2EncCp` was not built again. The `.olean` sha256 is the same before and after the build.
The maximum memory is the value for the full build: process 2.22 GiB, session 3.59 GiB. `lake build --no-build` exit 0.
Axioms gate PASS: 12177 declarations, 10199 theorems, 404 modules, hand list 2891, 0 nonstandard, 0 sorryAx.
The new gate JSON is byte-identical to the committed `axioms-gate.json`. So we did not write the record again.
Declaration comparison against the dump of the close-unit review: 0 CHANGED, 0 REMOVED, 0 ADDED. The encoder inventory fix unit did not change declarations.
Planted control (dump level): a copy with a changed type hash of `E2eScal.E2c.pw_e2c_spec_k` gives exit 1, CHANGED 1.
`regen_check.sh` 71/71 SAME (the earlier 55, `--gen6` 16). It is an integration check, not a new generator result.
`kindcheck.py --selftest` PASS, `p2dec_test.py` 394/394, `p2enc_test.py` 322/322.
Non-author layout recomputation `own_layout_e2g_r1.py`: 16/16 OK, 0 layouts differ from the reviewer's recomputation or are not disjoint.
Inventory rerun: the output of `inventory.py methods` is byte-identical to the committed `ssz-methods.json`.
The outputs of `inventory_decls.lean` (inside the gate) and `inventory.py run` are byte-identical to the committed `INVENTORY.md` and `INVENTORY.json`.
Not run (integrator): Lean-level planted control, cold build from an empty `.lake`, link check, Go differential, negative tests, x86-64.
Items to fix of the review of the `--gen5` integration (`93dae89`, APPROVE):
S1 was closed by writing the published state and the exclusions of "complete" in section 0.
S2 was closed by changing "15 of 17 flat" in BASELINE to "17 development types = 16 flat + nested AttestationData".
S3 was closed by replacing the "before review" text of the `--gen5` integration with that review. We did not change the dated text.
S4 is open. The text of denominator 1 in `INVENTORY.md` is script output. This unit does not change the script.
S5 record: the flat-encoder merge also used `merge(kraken)`. We did not touch the local ref `refs/remotes/offchainlabs/main`.
Remaining work: the growslice branch, length reject and morestack of the encoders. Also nested containers, lists, vectors and bitfields, hash tree root.
The 24 flat fixed-size types of the target were not started at the time of the flat-encoder integration (H7 later opened 8 types). The AttestationData encoder is work on another machine.
The list and vector work on the other machine is not in this tree. We do not claim it here.
We did not adopt the OPT-R1 pilot. T-7 is deferred. Records: `integration_int8` of `scal/RESULT.json`.

Conditions:

1. The runtime contracts `MakesliceC` (uint8, esz 1, cnt 32), `MemmoveC`, `GrowsliceC` (uint8, esz 1, first and second encoder sites), `ConvT64C` and `FmtErrorfDDC` (Epoch format, `type:int`) are hypotheses. We read the Go 1.26.10 source again and they did not change (`prysm/go1.26.10/e2e/RUNTIME-1.26.10.md`). There is no refinement proof.
2. Premises: stack guard, `runtime.writeBarrier` = 0, heap space, label freshness, global addresses (link check (a)–(f) PASS), initialized values of `ssz.ErrSize` and `ssz.ErrBytesLength` (the package init writes the values. The theorem returns the two words unchanged, and non-nil is not a conclusion. Only `errors.Is` of the Go differential looks at non-nil and distinctness).
3. We did not run on x86-64 hardware. The Go differential check is an arm64 build of the same source.
4. For the run that needs a second growslice after the first growslice (first growth capacity `< len + 40`), we proved up to the return if the remaining heap is at least the budget of the second call (`cp_e2e_marshal_grow_any_sharp` (B)). If it is smaller than the budget, we proved only up to the entry of the second call ((C)). The existing `GrowsliceC` form has no lower bound of the remaining heap (T-7). That area has only the Go differential check (blocked, waiting for a user decision). The witness model `rt_growslice` (new capacity `2·newLen + 192`) does not run this branch. The witness conclusion states the capacity range that is reached (`WitCpWF`). A witness theorem cannot decide which of (3A)/(3B)/(3C) applies. The result of `GrowsliceC` gives the new capacity and the remaining heap only as ranges. So with any runtime model, a witness that goes through the contract cannot tell these three apart (item S2 of the third review of the Checkpoint proofs: partly done, the reason is in OUTBOX 009). We did not prove non-nil of the error words (differential only).

The existing contract form `StaticBox` of the Epoch length reject reads `staticuint64s` and `staticuint64s_addr` of `Fk.Data` (Go 1.26.3 namespace). `E2e.ep_static_table` (2048 bytes the same) and `E2e.ep_static_addr` (same address, both the `runtime.staticuint64s` label) connect this to the Go 1.26.10 include. We do not use Go 1.26.3 facts (item N3 of the second review of the Checkpoint proofs, section 2 of `RUNTIME-1.26.10.md`).
The hand-written `(*primitives.Epoch).UnmarshalSSZ` is proved with the function specification `EpUAccC` (`ep_uacc_holds`). The decoder main theorem has no hypothesis about Epoch.
`Epoch.MarshalSSZTo` is inlined into the encoder (`-gcflags=-m=2`, `prysm/go1.26.10/e2e/CALLGRAPH.md`). The inlined body is proved inside the encoder theorem.
The specification is `E2e.prysmCpDesc`, written by hand from consensus-specs. It differs from the Desc of the Desc checker only in field names (`prysmCpDesc_checker`). EthLib `serialize`/`deserialize` do not use container field names, so the serialization and deserialization of the two Descs are the same for all values and all byte arrays (`prysmCpDesc_serialize_checker`, `prysmCpDesc_deserialize_checker`, review S1).
We did not move the Go 1.26.3 proofs. We derived all directive indexes, offsets, labels and frames again from the Go 1.26.10 `.S`.

A program makes the table from `prysm/go1.26.10/e2e/e2e.json`, `negative/result.json`, `differential.json` and `axioms.json`.
The rows of the table count each negative test case exactly once. In session 5, we added rows for the A2/A3 units (Slot, CommitteeIndex, AttestationData decoder, specification bridge) and for the unreachability lemmas (item S5 of the third review of the Checkpoint proofs). The table sum 98 of 7b5e956 was the 96 cases of the E2e modules without the 2 `cpu-*` cases, plus the 4 `cps-*` cases of E2eAd.
The AttestationData encoder (A4–A6) is not started.
Audit AU-11: `gen/e2e/table.py` reads the "remainder" column from the theorem statement. `⋆ True` means that the conclusion does not state the remaining memory. There are 5 such theorems: `cp_e2e_marshal_decoded_receiver`, `cp_e2e_marshal_spec_k`, `cp_e2e_unmarshal_then_marshal`, `cp_e2e_marshal_cover`, `cp_e2e_marshal_reject_cover`. The exact frame is in each component theorem and in the `*_framed` cover theorems. The composition `cp_e2e_unmarshal_then_marshal` has no version that states the frame.
Audit AU-06 (commit `301300f`): the 4 cover witnesses use the E2e-side tactic `wit_split_n` (`E2e/WitSplit.lean`). `Fk/WHost.lean` is unchanged. Elaboration times, measured once each with the same method: WitCpW 265.6→39.2 s, WitCpWF 262.7→35.0 s, WitCpWR 517.7→47.7 s, WitCpWRF 590.8→43.4 s (`opt1/AU-06.json`). The statements and axioms of the named declarations are the same.
Audit AU-07: we found the position of the slow omega and fixed it (`opt1/AU-07.json` attempt 4).
The position is the `bv_omega` of the argument `hLo` of `E2eScal.rootenc_seg`, line 163 of `E2eScal/P2EncCp.lean`.
The basis for the position is the trace log of task B.
The independent review of task B (REVIEW-B) confirmed this position.
That record is outside the repository.
The fix target is that one `by` block.
The changed block is `(by rw [show rsp.toBitVec - 8#64 - 104 - 8 = rsp.toBitVec - 120 by bv_omega])`.
The theorem statement is the same.
The file check time went from 1022.9 s to 8.3 s (macOS arm64, n = 1 each, separate runs).
The first value was measured without the profiler, and the second with `-Dprofiler=true`.
We did not measure again on the original machine or on x86-64.
Implementer executed checks: the incremental rebuild of the existing `.lake` (rebuild of one module, 7.3 s) is exit 0 (912 jobs).
In that incremental rebuild, Lake recorded 4.0 s for this module.
`lake build --no-build E2e E2eAd E2eScal` is exit 0.
Axioms gate PASS: 4518 declarations, 3812 theorems, hand list 315, 0 nonstandard, 0 `sorryAx` (`axioms-gate.json`).
The `Quot.sound,propext` set went from 2085 to 2084.
The declaration comparison (against the `71161fa` dump of the same day) is 11 lines, and all are `E2eScal.cp_e2e_marshal_main_s._proof_1_*`.
By name, `_proof_1_13`–`_22` are CHANGED (type hash) and `_proof_1_23` is REMOVED.
By content (kind, type hash, axioms), the base row with no head match is `_proof_1_13` (type hash `00000000e439c2be`).
For n = 13…22, the head `_proof_1_n` is the same as the base `_proof_1_(n+1)`.
Limit: the type hash is a 32-bit structural hash.
A same hash is not a proof of definitional equality.
All other rows are the same.
The type hash and axiom set of `E2eScal.cp_e2e_marshal_main_s` are also the same.
Review: the verdict of the independent review REVIEW-AU07 (2026-11-11) is APPROVE.
There are 0 required fixes and 7 recommended fixes (RA-1–RA-7).
The review target is the base `71161fa` and the diff sha256 prefix `6b056f2a`.
That review record is outside the repository.
Applying RA-1–RA-7 changes only documents.
This application needs a separate check.
Reviewer executed checks: the reviewer ran `lake build E2e E2eAd E2eScal` from an empty `.lake` in a new copy.
The result is exit 0, 489.4 s, 912 jobs (macOS arm64, n = 1).
Before the fix, the same kind of build in task B took 1209.1 s (n = 1).
We do not claim a cause for the difference between the two values.
The gate of that copy is PASS 4518 / 3812 / 315.
The comparison with the changed record is `DIFF []`.
All 11 lines of the declaration comparison were accepted.
The negative control (dump level) is exit 1.
The record before the fix and the first build of task B are in the 2026-11-11 paragraph of `HISTORY.md`.
Integration note (2026-11-11): all values in the audit AU-07 paragraph above are values of the task B tree (`71161fa` + fix, macOS arm64).
This branch only merged that fix. On the merged tree, we did not run a build, the axioms gate, a declaration comparison, time measurement or a new review.
The committed `axioms-gate.json` of this branch (5841 declarations) is the record from before the merge.
Addendum of the `--gen4` and H6 integration (2026-11-11): we built the merged tree for the first time in that integration. `P2EncCp` was built again in 10 s (n = 1).
Addendum of the same integration: axioms gate PASS, 7649 declarations. The only difference in the declaration comparison is the 11 lemma lines above. See the paragraph of that integration above.
Audit AU-12: `cp_e2e_marshal_decoded_receiver` is a corollary and has no witness of its own. `WitCpM` runs `cp_e2e_marshal_main`. `*_spec_here` (`ep`, `sl`, `ci`, `cpu`, `cpm`) show that the specification holds on that host. The execution witnesses (`*_runs`) show the satisfiability (non-vacuity) of the main theorem premises.

| Theorem | Obligation | Statement | Witness | Machine-code theorem | Remainder | Link | Negative tests | Go value |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| `E2e.ep_unmarshal_accept_main` | callee accept (function spec source) | done | done | done | exact frame | done | 5/5 passed | differential only (uint64 receiver; no GoVal theorem; epoch-len8 cases) |
| `E2e.ep_uacc_holds (EpUAccC)` | function spec | done | done | done | n/a | done | via ep_unmarshal_accept_main | differential only (uint64 receiver; no GoVal theorem) |
| `E2e.cp_e2e_accept_main (+ cp_e2e_accept_tail)` | accept | done | done | done | exact frame | done | 9/9 passed | before: witCpA_recv_pre (witness block); after: cp_after_decode_goValue on the conclusion fragments, every p ≠ 0 (MakesliceC does not state non-nil) + witCpA_recv_post; IR layout (not ELF abi.Type) + differential |
| `E2e.cp_e2e_reject_size_main` | reject (ssz.ErrSize) | done | done | done | exact frame | done | 4/4 passed | differential only (receiver unchanged; no GoVal theorem) |
| `E2e.cp_e2e_reject_complete + cp_e2e_reject_size_spec` | reject_complete / reject_spec | done | done (WitCpRS.cp_reject_spec_runs on Array.replicate n 0x11, n = 39, 41, 0) | done | n/a (cp_e2e_reject_complete); exact frame (cp_e2e_reject_size_spec) | n/a | 2/2 passed | n/a (spec level) / differential |
| `E2e.cp_e2e_accept_spec_k` | accept against EthLib | done | done (WitCpAS.cp_accept_spec_runs on pcpEnc g0 for 3 closed g0) | done | exact frame | done | 2/2 passed | via cp_e2e_accept_main (witCpA_recv_pre/post) |
| `E2e.cp_e2e_marshal_main` | marshal (fast path) | done | done | done | exact frame | done | 7/7 passed | witCpM_recv (witness block, offset 8); IR layout + differential |
| `E2e.cp_e2e_marshal_decoded_receiver` | encoder on a decoded-form receiver (not compose_hupd) | done | corollary with no own witness (WitCpM runs cp_e2e_marshal_main on a decoded-form receiver) | done | `⋆ True` | done | 3/3 passed | witCpM_recv (witness block) + differential |
| `E2e.cp_e2e_marshal_reject_main` | marshal_reject | done | done (WitCpMR: empty prefix rl 31/33/0, WitCpMR.P5: 5-byte prefix rl 31/0) | done | exact frame | done | 4/4 passed | witCpMR_recv (witness blocks, len(Root) 31/33/0); IR layout + differential |
| `E2e.cp_e2e_marshal_grow_main` | marshal (capacity too small: first growslice site; GrowsliceC esz 1, premise len + 40 ≤ nextSliceCap (len + 8) cap) | done | done (WitCpG: len 30, cap 36, rt_growslice + rt_memmove, 3 value instances) | done | exact frame | done | 9/9 passed | witCpG_recv (witness block, offset 0x20a0); IR layout + differential (enc-grow-cap0, enc-grow-len30-cap36) |
| `E2e.ep_unmarshal_reject_len_main` | callee reject (standalone) | done | done (WitEpR: len 7 and 9 static box, len 300 heap box) | done | exact frame | done | 7/7 passed | differential (epoch-len7/9) |
| `E2e.cp_e2e_marshal_spec_k + cp_e2e_size_main (+ size_spec)` | marshal against EthLib / size | done | done (WitCpS; spec_k via WitCpM) | done | `⋆ True` (cp_e2e_marshal_spec_k); exact frame (cp_e2e_size_main) | done | 8/8 passed | n/a (size) / via marshal |
| `E2e.cp_layout / cpGoValue (Go-value element)` | go value | done | evaluated on WitCpA/WitCpM/WitCpMR receivers; WitCpW/WitCpWR receivers (GoValW) | done | n/a | n/a | 7/7 passed | this is the Go-value predicate (slice-header sanity only; IR layout, not ELF abi.Type) |
| `E2e.cp_e2e_unmarshal_then_marshal` | compose_hupd / compose_witness (decoder entry → cp_e2e_accept_main → hupd → cp_e2e_marshal_main) | done | done (WitCpC: one Host with CpUnmarshal, EpUnmarshal, BumpAlloc1, RtCopy, CpMarshal; real middle memory by storeInt) | done | `⋆ True` | done | 7/7 passed | witCpC_recv: before from the witness block, after = cp_after_decode_goValue (every p ≠ 0) + differential roundtrip |
| `E2e.prysmCpDesc_serialize_checker / deserialize_checker` | spec bridge: codec equality with the checker Desc | done | n/a (spec level) | done | n/a | n/a | 4/4 passed | n/a |
| `E2e.cpw_head_fit / cpw_head_grow (prefixes to L_7b)` | segment lemmas (first capacity test; first growslice, GrowsliceC esz 1) | done | via WitCpW / WitCpWR (cover instances) | done | exact frame | done | 4/4 passed | n/a (segment) |
| `E2e.cpw_tail_fit / cpw_tail_rej / cpw_tail_grow / cpw_tail_grow_call (tails from L_7b)` | segment lemmas (second capacity test; second growslice; ErrBytesLength) | done | via WitCpW / WitCpWR; cpw_tail_grow via cp_e2e_marshal_grow2_main | done | exact frame | done | 9/9 passed | n/a (segment) |
| `E2e.cp_e2e_marshal_grow2_main` | marshal: first append fits, second grows (len + 8 ≤ cap < len + 40; GrowsliceC esz 1) | done | done (WitCpW.cov_runs n = 8, 39 through the cover) | done | exact frame | done | 2/2 passed | differential (enc-w-len30-spare8/20/39); witness receiver: GoValW.witCpW_recv |
| `E2e.cp_e2e_marshal_grow_any_main` | marshal: first append grows, every cap < len + 8 (no nextSliceCap premise); left: returns; right: reaches the 2nd growslice call — the run after it is NOT proved (GrowsliceC does not chain) | done | done (WitCpW.cov_runs n = 0, 3 and cov_runs_nil: left disjunct; right disjunct not exercised by the model) | done (partial: right disjunct ends at the call) | exact frame | done | 2/2 passed | differential (enc-w-len30-spare0/3, enc-w-len10-spare0, enc-grow-cap0); witness receiver: GoValW.witCpW_recv |
| `E2e.cp_e2e_marshal_grow_any_sharp` | marshal: first append grows, every cap < len + 8 (same premises as grow_any_main; GrowsliceC esz 1, MemmoveC). (A) returns through the first block; (B) returns through the second growslice when the heap left av1 ≥ 2·nextSliceCap(len+40, C1) + 8192; (C) entry of the second call with Heap av1 and av1 below that budget — the run after (C) is NOT proved (no lower bound on the remaining heap in GrowsliceC, blocked / differential only pending a user decision) | done | premises: WitCpW / WitCpWF (n = 0, 3, nil dst) through the covers; which of (A)/(B)/(C) a run takes is not decidable through GrowsliceC (it hides the returned capacity and heap); the witness model takes (A) | done (partial: (C) ends at the call) | exact frame | done | 4/4 passed | differential (enc-w-len30-spare0/3, enc-w-len10-spare0, enc-grow-cap0); witness receiver: GoValW.witCpW_recv |
| `E2e.cp_e2e_marshal_reject_grow_main` | marshal_reject after the first growslice (cap < len + 8, len(Root) ≠ 32, epoch bytes written to the new block before the reject) | done | done (WitCpWR.rej_runs n = 0, 3; rej_runs_nil) | done | exact frame | done | 2/2 passed | differential (enc-w-rej-len30-spare0/3: caller array unchanged); witness receivers: GoValW.witCpWR_recv (rl 0/31/33/48), rl 49 not a Go value (witCpWR_recv_bad); rej_runs allows any rl ≠ 32, a Go caller only rl ≤ 48 |
| `E2e.cp_e2e_marshal_cover` | case cover len(Root) = 32 × every len ≤ cap, against EthLib (dst ++ serialize; ⋆ True remainder) or at the 2nd growslice call | done | done (WitCpW: cap = len, len+3, len+8, len+39, len+40, nil dst) | done | `⋆ True` | done | 2/2 passed | differential; witness receiver: GoValW.witCpW_recv |
| `E2e.cp_e2e_marshal_reject_cover` | case cover len(Root) ≠ 32 × every len ≤ cap (ErrBytesLength words; some block holds pre ++ epoch) | done | done (WitCpWR: cap = len, len+3, len+8, len+40, nil dst; rl 31/0/33) | done | `⋆ True` | done | 2/2 passed | differential; witness receivers: GoValW.witCpWR_recv (rl 0/31/33/48), rl 49 not a Go value (witCpWR_recv_bad); rej_runs allows any rl ≠ 32, a Go caller only rl ≤ 48 |
| `E2e.cp_e2e_marshal_cover_framed` | case cover len(Root) = 32 × every len ≤ cap with the exact frame (no ⋆ True): disjunction of the member postconditions (1) cp_e2e_marshal_main, (2) cp_e2e_marshal_grow2_main, (3A)/(3B)/(3C) cp_e2e_marshal_grow_any_sharp; returned block pre ++ bs with serialize = .ok bs (EthLib); (3C) is the entry of the second growslice call | done | done (WitCpWF.covf_runs: cap = len, len+3, len+8, len+39, len+40 with the reached capacity range in the conclusion; covf_runs_nil) | done (partial: (3C) ends at the call) | exact frame | done | 4/4 passed | differential (accept cases); witness receiver: GoValW.witCpW_recv |
| `E2e.cp_e2e_marshal_reject_cover_framed` | case cover len(Root) ≠ 32 × every len ≤ cap with the exact frame: len + 8 ≤ cap: epoch in the caller's array (blk = dst); cap < len + 8: caller's array pre ++ spare unchanged, epoch in the new block only | done | done (WitCpWRF.rejf_runs: cap = len, len+3, len+8, len+40, nil dst; rl 31/0/33/48) | done | exact frame | done | 3/3 passed | differential (reject cases); witness receivers: GoValW.witCpWR_recv (rl 0/31/33/48), rl 49 not a Go value (witCpWR_recv_bad); rej_runs allows any rl ≠ 32, a Go caller only rl ≤ 48 |
| `E2eAd.sl_unmarshal_accept_main + sl_uacc_holds (SlUAccC)` | callee accept primitives.Slot (function spec source) | done | done (WitSl, 3 values) | done | exact frame (sl_unmarshal_accept_main); n/a (sl_uacc_holds) | done | 5/5 passed | n/a (uint64 receiver) |
| `E2eAd.ci_unmarshal_accept_main + ci_uacc_holds (CiUAccC)` | callee accept primitives.CommitteeIndex (function spec source) | done | done (WitCi, 3 values) | done | exact frame (ci_unmarshal_accept_main); n/a (ci_uacc_holds) | done | 5/5 passed | n/a (uint64 receiver) |
| `E2eAd.ad_e2e_head / ad_e2e_root / ad_e2e_src / ad_e2e_tgt` | segment lemmas of the AttestationData decoder (size test, Slot, CommitteeIndex, Root, Source, Target) | done | via WitAdA | done | exact frame | done | 13/13 passed | n/a (segment) |
| `E2eAd.ad_e2e_accept_main` | accept v1alpha1.AttestationData (callees via sl/ci/cp_uacc_holds; Source/Target always new) | done | done (WitAdA, 3 inputs) | done | exact frame | done | 5/5 passed | partial (full receiver and both 72-byte objects in the conclusion; no Lean Go-value predicate for AttestationData) |
| `E2eAd.ad_e2e_reject_size_main` | reject (ssz.ErrSize) | done | done (WitAdR len 127/129/0) | done | exact frame | done | 2/2 passed | n/a (receiver unchanged; error words as they are) |
| `E2eAd.ad_e2e_accept_spec_k (+ reject_size_spec, reject_complete)` | accept / reject against EthLib | done | via WitAdA / WitAdR | done | exact frame | done | 2/2 passed | via ad_e2e_accept_main |
| `E2e.prysmAdDesc_serialize_checker / deserialize_checker / pad_spec_accepts_iff` | spec bridge AttestationData (codec equality with the checker Desc) | done | n/a (spec level) | done | n/a | n/a | 6/6 passed | n/a |
| `E2e.cp_e2e_epoch_err_unreachable; E2eAd.ad_e2e_{slot,ci,source,target}_err_unreachable` | unreachable_mc (own column; not reject coverage) | done | n/a (local lemmas) | done | exact frame | done | 4/4 passed | n/a |

The unreachable_mc theorems state a conditional skip. If rax = 0 after the call returns, it reaches the label after the wrap, and the registers and memory do not change.
Unreachability for all inputs holds only together with the callee specifications (`EpUAccC`, `SlUAccC`, `CiUAccC`, `ViUAccC`, `CpUAccC`) (review of session 10).

| unreachable_mc row | Theorem | Status | Counted in reject coverage |
| --- | --- | --- | --- |
| phase0.ssz.go:1988 fmt.Errorf("Epoch: %w") (decoder) | E2e.cp_e2e_epoch_err_unreachable | done | No |
| phase0.ssz.go:1964 fmt.Errorf("Epoch: %w") (encoder) | none needed: removed by the compiler (inlined Epoch.MarshalSSZTo cannot fail; no fmt.errorf call in the machine code, CALLGRAPH.md) | absent from the code | No |
| AttestationData decoder fmt.Errorf("Slot: %w") | E2eAd.ad_e2e_slot_err_unreachable | done | No |
| AttestationData decoder fmt.Errorf("CommitteeIndex: %w") | E2eAd.ad_e2e_ci_err_unreachable | done | No |
| AttestationData decoder fmt.Errorf("Source: %w") | E2eAd.ad_e2e_source_err_unreachable | done | No |
| AttestationData decoder fmt.Errorf("Target: %w") | E2eAd.ad_e2e_target_err_unreachable | done | No |
| BeaconBlockHeader decoder fmt.Errorf("Slot: %w") (hold-out H1) | E2eScal.Bh.bh_e2e_slot_err_unreachable (witness WitBhU) | done | No |
| BeaconBlockHeader decoder fmt.Errorf("ValidatorIndex: %w") (hold-out H1) | E2eScal.Bh.bh_e2e_vi_err_unreachable (witness WitBhU) | done | No |

Full axioms check (fix of audit finding AU-10, a gate that checked a hand list only): `gen/e2e/axioms_gate.py` lists the 95 modules of E2e, E2eAd and E2eScal with a program. The axiom sets of all 3125 declarations (2621 theorems) are standard, and there are 0 `sorryAx` (gate task 377 at commit `6dfc8b5`, `axioms-gate.json`, the counts are the output of that command). The 169 names of the hand list stay as a "must exist" check. 0 names are missing. Negative control: if we add a temporary theorem `E2e.sorry_ctl'` that uses `sorry`, it is FAIL (task 256).
Negative tests total: 154/154 passed (`negative/result.json`). Go differential: 59 cases, 0 mismatches (`differential.json`). Axioms: 79 names, verdict PASS (`axioms.json`).

Cost record (PROOF-PLAN §4): `gen/e2e/cost.py` makes `prysm/go1.26.10/e2e/COST.json` from the gate record (`records.jsonl`) and the task logs. Per module and per theorem, it has wall-clock seconds inside the gate, the run count, the failed run count, the maximum process RSS and the memcap kill count. Time outside the gate (thinking, editing) is not in it. Audit AU-16: the `gate_s` of a module is "cumulative gate seconds". It is the sum of all attempts, failures and successes together, and it is not a build time. `last_ok_run_gate_s` is the gate seconds of the last successful run, and it is not a controlled cold build. We write cold build seconds only where we measured them separately. `cost.py` and `tcost.py` take the last task number as an argument and write it into `source` of the output. So the output is the same while the stream continues. `COST.json` has the upper bound 213 (212 tasks, 15151.6 s), and it is the same as the committed value. `TEMPLATE-COST.json` is tasks 214–247.

Negative test classes (item N1 of the second review of the Checkpoint proofs): `negative.py` writes a `class` for each result. The Lean "(deterministic) timeout" error is `timeout_heartbeat`, and going over the per-case limit (300 s) is `timeout_wall`. The Lean "maximum recursion depth" error is `recursion_limit`. The three resource classes are not a pass. We changed the 2 statement mutations that were heartbeat timeouts to mutations that fail clearly: `cpmr-stmt-noown` (removes ownership of `dst[len..len+8]` from the premise, fails at the C-1 store step), `cpg-stmt-growle` (`cap < len + 8` to `≤`). We also added the code mutation `cpg-oldcap` (the growslice oldCap argument of the first site). We tried `cpg-stmt-noroot`, but it hit the 300 s limit, so we did not include it (gate task 126). The full run of session 3 (gate task 139, 300 s per case): 73/73, 0 timeouts. `cpg-newptr` (failed in the theorem after 489.7 s in task 125) went over 300 s, so we removed it. The class is decided by the first error line. For `ep-load8`, the first error is an `ecancel` failure inside the theorem, and one later error is a heartbeat timeout (written in `later_resource_error`). `sl-load8` and `ci-load8` are the same.
Audit AU-04: if the first error is a syntax error or a name resolution error, the class is `wrong_target`. The list was extracted from the error texts in the pinned toolchain source (`negative.py` `WRONG_TARGET`: unknown tactic/identifier/constant/namespace and others, Invalid field … environment does not contain, ambiguous, unexpected token and others, item M1 of the review of the audit fixes). Item N1 of the second review of the audit fixes added `Unknown option` and `Case tag … not found`. This list is not complete. A syntax error or name error that is not in the list is classified as `inside`. So we read the first error of each row. It is not a pass. It means that the mutation did not reach the target. After the reclassification, 3 cases changed from `inside` to `wrong_target`: `cps-stmt-u-rax`, `cps-stmt-m-mm`, `ada-m-nohms`. `scal/negative-result.json` (18 cases) did not change.
Reclassification after item M1 of the review of the audit fixes: 154/154, 20/20, 0 changes. A call with an id that matches no case runs nothing and exits 2 (S7).
Generated statement check (items M2 and S1 of the review of the audit fixes): for each generated theorem `t`, `t_kind` matches the full declared type of `@t` with the hand kind (`E2eScal/Kind.lean`) by `rfl`. This includes the binders before the colon. A hand theorem is not necessary.
The earlier `exact` check looked only after the colon. The 5 mutations that add a premise before the colon fail only at the `_kind` line. The scal negative tests are 28/28 (gate tasks 288–291).
Conclusion constant mutations now fail inside the theorem in 1.4 s (S2, earlier they went over the 300 s wall clock). The basis and the limits are in `gen/scal/README.md` and section 2 of `scal/CONTAMINATION.md`.
We changed those 3 cases to type-weakening mutations. They keep the name and change the type of the premise to `True`. There is one gate task per case (tasks 251–253). All three are `inside`. The first error is "Application type mismatch" at the place that uses that premise (type `True` of `hms`/`hmm`, expected type `MakesliceC …`/`MemmoveC S`). This shows that the proof uses the premise at that place. It does not show that the theorem is false without the premise.
Audit AU-05: `lake env lean` does not check the trace. So `negative.py` and `axioms.py run` first run `lake build --no-build <imported modules>`. If the exit code is not 0, they run no case. Gate task 248 `lake build --no-build E2e E2eAd E2eScal` exit 3 (stale trace of 5 E2eAd modules), task 249 `lake build E2eAd` exit 0, task 250 the same check exit 0.
In session 4 task 202, 3 cases (`cpw-tr-jne`, `cpw-tc-lea`, `cpw-hg-jae`) were "outside". The reason is that an earlier theorem in the same file goes through the same directive. The mutations failed. In task 203, we changed them to `cpw-tr-err1`, `cpw-tc-stmt-num`, `cpw-hg-spill` (item S6 of the third review of the Checkpoint proofs, `e2e.json` `negative_suite.removed`).
`ci-load8` was not in the session 4 result file. We ran it again in session 5 task 213: fails inside, and a heartbeat error comes after it (item S4 of the third review of the Checkpoint proofs).
The result file combines the results of several tasks by case id. All cases ran with the 300 s per-case limit. We did not run all of them in one run (gate limit of 20 minutes per run).

Handling of the first review of the Checkpoint proofs (session 2): M1 fix (real composition `cp_e2e_unmarshal_then_marshal`), S1 proof (`E2e.SpecEq`), S2 wording kept (`cp_e2e_epoch_err_unreachable` is a local lemma that says if rax = 0 at directive 18, it reaches directive 47, and `ep_uacc_holds` gives rax = 0. We did not write a single theorem that connects the two), S3 recorded the sha256 of the E2e include files and `e2e/AXIOMS.txt` in `e2e.json` `e2e_include_sha256`, S4 reproduction line, S5 adjustframe row, S6 witnesses `WitCpAS`·`WitCpRS`, S7 ran all negative tests with a 900 s per-case limit (gate task 125: 73 cases. After reclassification by item N1 of the second review: 53 fail inside, 18 controls, 2 Lean heartbeat timeouts: `cpmr-stmt-dst-unchanged` 482 s, `cpg-stmt-e8off` 480 s), S8 differential extension (receiver unchanged, error identity and not the opposite error, Epoch error text, C-1 bytes observed in the caller array), S9 reference rows G-2 and G-3 (known Prysm test failures that are not generator defects).

Receiver note: the receiver layout of the theorems is `prysm/ir/ir-mainnet.json` `go_fields` (gc amd64 rule). `state` 0, `Epoch` 8, `Root` 16, `unknownFields` 40, `sizeCache` 64, size 72.
Go value element: we checked the witness receivers with `cpGoValue` of `E2e.GoVal`. The receivers before the decoder and of the encoder witnesses are read from the witness block (`recvAt`). The receiver after the decoder is not written by hand: `cpAfterDecode` is the fragments that the conclusion of `cp_e2e_accept_main` writes at `rax .. rax + 72`, and `cp_after_decode_goValue` proves that it is a Go value for all Go-value receivers before, all 8 input bytes and all `p ≠ 0`. `MakesliceC` does not state `p ≠ 0`, so this is a condition (item N4 of the second review of the Checkpoint proofs). The predicate looks only at the soundness of the slice header (it does not look at the Epoch value or the Root content). The two Epoch rows and `cp_e2e_reject_size_main` have no GoVal theorem: the Go value cell is "differential only". The layout comes from the IR (go/types). We did not read the ELF abi.Type because it has no named symbol (trust item).
Bytes 8–31 of the 32-byte encoder stack temporary area are the X15 content. We do not assume X15 = 0, so it is existentially quantified in the conclusion.
We divided the decoder theorem in two at `L_b4` (directive 47) so that it fits inside the 6 GiB memory cap (`cp_e2e_accept_tail`).
Composition E5: the saved rbp (x − 8), the saved rbx (x + 16), `p` (x − 32) and the two zero words (x − 48, x − 40) that the decoder leaves are the `fp`, `s2`, `l32` and `t30` of the encoder (x = rsp of the two entries). The encoder slots x − 16, x − 24 and x − 64…x − 49 are outside the decoder footprint, so the caller gives them together with dst. The encoder return slot x − 120 and the scratch below it are the lower part of the decoder scratch (`S ≥ 24`, encoder `S − 24`, two instances of `MemmoveC`). The composition theorem has no code mutation negative tests. The last 4 code mutations (`cpx-dec-cmp41`, `cpx-ep-load8`, `cpx-enc-len33`, `cpx-enc-newlen16`) failed with a type mismatch in the application of the imported main theorems because of constant renaming. The unchanged copy also fails in the same way, so they are not evidence for the directives (item N2 of the second review of the Checkpoint proofs). So we removed them. The directive evidence of the two halves is the `cpa-*` and `cpm-*` code mutations. The negative tests of the composition are 6 statement mutations and 1 control.

Reproduction (all inside the gate and memcap 6 GiB):
No command in this block ran on the reduced tree (2026-11-12). The `lake build` check of section 0 covers the E2e libraries.

```sh
python3 -I -B fv/kraken/gen/e2e/callgraph.py <objdump> prysm/go1.26.10/e2e/callgraph.json <m2.log>
python3 -I -B fv/kraken/gen/e2e/e2elink.py filter <out> <objdump> <elf> <nm>
mkdir -p <out>/norm && python3 -I -B fv/kraken/link/conv.py <out>/target.objdump <out>/p1bin-amd64.nm <out>/norm --norm
python3 -I -B fv/kraken/gen/e2e/e2elink.py data <out> && python3 -I -B fv/kraken/link/check.py <out>
# <nm> = p1bin-amd64.nm, sha256 88ee8b9a…40ac (e2e.json link_check_inputs; not committed, audit AU-17)
GOROOT=$(go env GOROOT) go test -count=1 ./ssz/ ./sszgen/...    # checkpoint gate list (audit AU-17). ./fv/kraken/semtest/ was removed on 2026-11-12
(cd fv/kraken/lean && lake build E2e.<module>)            # one module at a time: Epoch WitEp Spec CpAccept WitCpA CpReject WitCpR CpSpecK CpMarshal WitCpM Compose CpCompose WitCpC CpMarshalG WitCpG CpMarshalR WitCpMR CpSpecM WitCpS EpReject WitEpR GoVal CpWTail CpWTailG CpWHead CpWGrow CpWGrowAny CpWCover WitCpW WitCpWR CpWSharp CpWCoverF WitCpWF WitCpWRF GoValW
python3 -I -B fv/kraken/gen/e2e/axioms.py run fv/kraken/gen/e2e/Axioms.lean prysm/go1.26.10/e2e/axioms.json   # lake build --no-build first (audit AU-05)
python3 -I -B fv/kraken/gen/e2e/axioms_gate.py run prysm/go1.26.10/e2e/axioms-gate.json <dump.tsv>   # all declarations of E2e/E2eAd/E2eScal (audit AU-10)
python3 -I -B fv/kraken/gen/e2e/negative.py fv/kraken/gen/e2e/negcases.json <work> prysm/go1.26.10/e2e/negative/result.json
python3 -I -B fv/kraken/gen/e2e/differential.py cases <c.json>; go run ./fve2e/cpcheck <c.json> > <o.json>   # Prysm temporary tree, Go 1.26.10
python3 -I -B fv/kraken/gen/e2e/differential.py check <c.json> <o.json> prysm/go1.26.10/e2e/differential.json
# T-9 (BeaconBlockHeader encoder fast path): modules StackGuard BhEncHead BhEncRoots BhEncMain BhSpecM WitBhM (lake build E2eScal.<module>)
python3 -I -B fv/kraken/gen/e2e/negative.py fv/kraken/gen/scal/negcases-t9.json <work> prysm/go1.26.10/e2e/scal/negative-t9.json <case-id>   # one gate task per case
python3 -I -B fv/kraken/gen/e2e/bhmdiff.py cases <c.json>; go run -overlay <overlay.json> ./fve2e/bhmcheck < <c.json> > <o.json>   # Prysm temporary tree, Go 1.26.10; the overlay gives bh/bhmcheck-main.go.txt as main.go
python3 -I -B fv/kraken/gen/e2e/bhmdiff.py check <c.json> <o.json> prysm/go1.26.10/e2e/bh/differential-enc.json
# ENC stream: modules EncBlock BhEncBlock E1EncMain E1SpecM WitE1M EncReject BhEncReject WitBhMR (lake build E2eScal.<module>)
python3 -I -B fv/kraken/gen/e2e/negative.py fv/kraken/gen/scal/negcases-enc.json <work> prysm/go1.26.10/e2e/scal/negative-enc.json <case-id>   # one gate task per case
# SG-1 extension: modules P2DecZ KindZ GenE1Dec E1GenSame (lake build E2eScal.<module>)
(cd fv/kraken && sh ../../.claude/skills/maintaining-methodical-fv/scripts/regen_check.sh <file> -- sh -c "<that command of gen/scal/gen.sh> > $REGEN_OUT")   # for each gen.sh command
python3 -I -B fv/kraken/gen/scal/kindcheck.py --selftest; python3 -I -B fv/kraken/gen/scal/kindcheck.py fv/kraken/lean/E2eScal/Gen*.lean
python3 -I -B fv/kraken/gen/scal/p2dec_test.py <work> <result.json>   # generator test, one gate task
python3 -I -B fv/kraken/gen/e2e/negative.py fv/kraken/gen/scal/negcases-sg1.json <work> prysm/go1.26.10/e2e/scal/negative-sg1.json <case-id>   # one gate task per case
# H3 holdout: link table, generator once (per type), modules, negative tests, Go differential
python3 -I -B fv/kraken/gen/e2e/h3link.py callgraph <objdump> <out.json>; python3 -I -B fv/kraken/gen/e2e/h3link.py filter <out> <objdump> <elf> <nm>
python3 -I -B fv/kraken/link/conv.py <out>/target.objdump <out>/p1bin-amd64.nm <out>/norm --norm; python3 -I -B fv/kraken/gen/e2e/h3link.py data <out> prysm/go1.26.10/e2e/link prysm/go1.26.10/e2e/ad/link; python3 -I -B fv/kraken/link/check.py <out>
(cd fv/kraken && python3 -I gen/scal/scalgen.py p2dec --S prysm/go1.26.10/e2e/h3/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlobIdentifier.UnmarshalSSZ.S --const BiUnmarshal --ir prysm/ir/ir-mainnet.json --type v1alpha1.BlobIdentifier --prefix bi_dec --imports E2eScal.P2Dec,E2eScal.P2DecZ,E2eScal.H3Code --open E2eScal.H3Code)   # DepositMessage: --const DmUnmarshal --type v1alpha1.DepositMessage --prefix dm_dec
# 20 modules: H3Code BiDesc DmDesc GenBiDec GenDmDec BiAccept BiReject BiSpec BiSpecChecker BiSpecK WitBiA WitBiR DmSeg0 DmAccept DmReject DmSpec DmSpecChecker DmSpecK WitDmA WitDmR (lake build E2eScal.<module>)
python3 -I -B fv/kraken/gen/e2e/negative.py fv/kraken/gen/scal/negcases-h3.json <work> prysm/go1.26.10/e2e/scal/negative-h3.json <case-id>   # one gate task per case
python3 -I -B fv/kraken/gen/e2e/h3diff.py cases <c.json>; go run -overlay <overlay.json> ./fve2e/h3check < <c.json> > <o.json>   # Prysm temporary tree, Go 1.26.10; the overlay gives h3/h3check-main.go.txt as main.go
python3 -I -B fv/kraken/gen/e2e/h3diff.py check <c.json> <o.json> prysm/go1.26.10/e2e/h3/differential.json
# OPT-R1 test (test ELF 3ef7ac89…f602; prysm/go1.26.10/opt-r1/MANIFEST.md section 4): build generator ca191bb with Go 1.26.10, -trimpath
OPTR1_GEN=<generator> sh fv/kraken/gen/prysm-gen.sh <prysm-tree> fv/kraken/prysm/go1.26.10/opt-r1/gen-wrap.sh <out> gen
# put <out>/gen/*/phase0*.ssz.go into a copy of the base temporary tree (prysm/go1.26.10/MANIFEST.md section 3), and build ./fvphase1c/p1cbin with the flags above
# the object dump is the same as the regex of fv/kraken/gen/prysm-elf.sh
python3 -I -B fv/kraken/gen/e2e/e2elink.py filter <link-out> <objdump> <elf> <nm>
mkdir -p <link-out>/norm && python3 -I -B fv/kraken/link/conv.py <link-out>/target.objdump <link-out>/p1bin-amd64.nm <link-out>/norm --norm
python3 -I -B fv/kraken/gen/e2e/e2elink.py data <link-out> && python3 -I -B fv/kraken/link/check.py <link-out>
# 11 modules: Code Head HeadG Main MainG Spec Tail TailR WitO WitOW WitOWR (lake build E2e.OptR1.<module>)
python3 -I -B fv/kraken/gen/e2e/negative.py fv/kraken/prysm/go1.26.10/opt-r1/negcases.json <work> fv/kraken/prysm/go1.26.10/opt-r1/negative.json <case-id>   # one gate task per case; WRITES the result file
# Go differential (arm64, Go semantics only): fv/kraken/prysm/go1.26.10/opt-r1/diff/; benchmarks (arm64 only): fv/kraken/prysm/go1.26.10/opt-r1/bench/
# GEN2 generator (unit G2-G): last 6 commands of gen.sh, once per type; modules Gen2E1Dec Gen2BiDec Gen2DmDec BiAcceptG2 DmAcceptG2 Gen2BiAccept Gen2DmAccept Gen2E1Accept (lake build E2eScal.<module>)
(cd fv/kraken && python3 -I gen/scal/scalgen.py p2dec --gen2 --summary <s.json> --S prysm/go1.26.10/e2e/h3/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DepositMessage.UnmarshalSSZ.S --const DmUnmarshal --ir prysm/ir/ir-mainnet.json --type v1alpha1.DepositMessage --prefix dm_g2dec --imports E2eScal.P2Dec,E2eScal.SegN,E2eScal.U64Inline,E2eScal.H3Code --open E2eScal.H3Code)   # other types and --compose: gen.sh
python3 -I -B fv/kraken/gen/scal/p2dec_test.py <work> <result.json>; python3 -I -B fv/kraken/gen/scal/kindcheck.py fv/kraken/lean/E2eScal/Gen2*Dec.lean fv/kraken/lean/E2eScal/Gen2*Accept.lean
python3 -I -B fv/kraken/gen/scal/kindcheck.py --partial fv/kraken/lean/E2eScal/Gen2BhDecPartial.lean   # exit 3 = kind PASS for the theorems that are there, not full coverage
# GEN3 generator (unit G3-G): last 5 commands of gen.sh, once per type; modules Gen3PwDec Gen3DdDec Gen3BhDec Gen3AdDecPartial Gen3DdAccept2 PwAcceptG3 BhAcceptG3 (lake build E2eScal.<module>)
python3 -I -B fv/kraken/gen/scal/kindcheck.py fv/kraken/lean/E2eScal/Gen3PwDec.lean fv/kraken/lean/E2eScal/Gen3DdDec.lean fv/kraken/lean/E2eScal/Gen3BhDec.lean fv/kraken/lean/E2eScal/Gen3DdAccept2.lean; python3 -I -B fv/kraken/gen/scal/kindcheck.py --partial fv/kraken/lean/E2eScal/Gen3AdDecPartial.lean
python3 -I -B fv/kraken/gen/e2e/negative.py fv/kraken/gen/scal/negcases-g3g.json <work> prysm/go1.26.10/e2e/scal/negative-g3g.json <case-id>   # one gate task per case
# GEN4 generator (unit G4-G): last group of gen.sh (once per type); modules Gen4CpDec Gen4AdDecPartial Gen4BhDec Gen4E1Dec Gen4BiDec Gen4DmDec Gen4DdDec Gen4PwDec Gen4SmDec Gen4PcDec SmAcceptG4gen PcAcceptG4gen PwAcceptG4gen (lake build E2eScal.<module>)
python3 -I -B fv/kraken/gen/scal/kindcheck.py --selftest; python3 -I -B fv/kraken/gen/scal/kindcheck.py fv/kraken/lean/E2eScal/Gen4*Dec.lean; python3 -I -B fv/kraken/gen/scal/kindcheck.py --partial fv/kraken/lean/E2eScal/Gen4AdDecPartial.lean
python3 -I -B fv/kraken/gen/scal/p2dec_test.py <work> <result.json>
python3 -I -B fv/kraken/gen/e2e/negative.py fv/kraken/gen/scal/negcases-g4g.json <work> prysm/go1.26.10/e2e/scal/negative-g4g.json <case-id>   # one gate task per case
python3 -I -B fv/kraken/gen/e2e/negative.py fv/kraken/gen/scal/negcases-g2g.json <work> <result.json> <case-id>   # one gate task per case
# H4 holdout: link table, generator (S) and (C) once per type, modules, negative tests, Go differential
python3 -I -B fv/kraken/gen/e2e/h4link.py callgraph <objdump> <out.json>; python3 -I -B fv/kraken/gen/e2e/h4link.py filter <out> <objdump> <elf> <nm>
mkdir -p <out>/norm && python3 -I -B fv/kraken/link/conv.py <out>/target.objdump <out>/p1bin-amd64.nm <out>/norm --norm; python3 -I -B fv/kraken/gen/e2e/h4link.py data <out> prysm/go1.26.10/e2e/link prysm/go1.26.10/e2e/ad/link; python3 -I -B fv/kraken/link/check.py <out>
(cd fv/kraken && python3 -I gen/scal/scalgen.py p2dec --gen2 --summary <s.json> --partial-out <partial.lean> --S prysm/go1.26.10/e2e/h4/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Deposit_Data.UnmarshalSSZ.S --const DdUnmarshal --ir prysm/ir/ir-mainnet.json --type v1alpha1.Deposit_Data --prefix dd_g2dec --imports E2eScal.P2Dec,E2eScal.P2DecZ,E2eScal.SegN,E2eScal.U64Inline,E2eScal.H4Code --open E2eScal.H4Code)   # exit 3; PendingPartialWithdrawal: --const PwUnmarshal --type v1alpha1.PendingPartialWithdrawal --prefix pw_g2dec (exit 2)
(cd fv/kraken && python3 -I gen/scal/scalgen.py p2dec --gen2 --compose --name dd_e2e_accept_main_gc --same-as-prop E2eScal.H4.dd_accept_stmt --S <same as above> --const DdUnmarshal --ir prysm/ir/ir-mainnet.json --type v1alpha1.Deposit_Data --prefix dd_g2dec --imports E2eScal.Compose,E2eScal.Gen2DdDecPartial,E2eScal.E1Accept,E2eScal.H4Stmt --open E2eScal.H4Code)   # exit 2 (reject); pw: --name pw_e2e_accept_main_gc --same-as-prop E2eScal.H4.pw_accept_stmt
python3 -I -B fv/kraken/gen/scal/kindcheck.py --partial fv/kraken/lean/E2eScal/Gen2DdDecPartial.lean   # exit 3 = kind PASS for the theorems that are there
# 18 modules: H4Code H4Stmt DdDesc PwDesc Gen2DdDecPartial DdSegNop DdAccept DdReject PwReject DdSpecChecker PwSpecChecker DdSpec PwSpec DdSpecK PwSpecK WitDdA WitDdR WitPwR (lake build E2eScal.<module>)
python3 -I -B fv/kraken/gen/e2e/negative.py fv/kraken/gen/scal/negcases-h4.json <work> prysm/go1.26.10/e2e/scal/negative-h4.json <case-id>   # one gate task per case
python3 -I -B fv/kraken/gen/e2e/h4diff.py cases <c.json>; go run -overlay <overlay.json> ./fve2e/h4check < <c.json> > <o.json>   # Prysm temporary tree, Go 1.26.10; the overlay gives h4/h4check-main.go.txt as main.go
python3 -I -B fv/kraken/gen/e2e/h4diff.py check <c.json> <o.json> prysm/go1.26.10/e2e/h4/differential.json
```

Hold-out H7 (branch `claude/ssz-fv-flat24`, the review of H7 approved `6f20eef`): we measured once the 24 flat fixed-size types outside the development population.
We did not change the generator. Decoders 7/24 and encoders 8/24 were generated, built and passed the kind check.
The rest were rejected because of new field kinds (byte20 in 8 types, byte4 in 5 types, byte1 in 1 type, bool in 2 types) and a new callee (Gwei in 1 type).
We closed the generated types in the same unit. The numbers are by the inventory script (`gen/tools/inventory.py`).
Decoder complete 18/211, partial 10. Encoder fast path complete 24/211 (premises: len + SizeSSZ ≤ cap, exact field length).
Only the DepositRequest decoder is complete. The other 6 decoders have no Desc checker record, so codec is missing.
Evidence: negative tests 67/67, Go differential 138/138 (Go semantics on linux/arm64, not an ELF run), axioms gate PASS 14415.
Records: `flat24` of `scal/RESULT.json`, section 39 of `scal/CONTAMINATION.md`, `prysm/go1.26.10/e2e/f24/`.

H7 review results and items to fix (added in the H7 integration):
The review of H7 (`6f20eef`, APPROVE): 0 required fixes, 7 items to fix. No item changes the numbers.
S1: three of the generated types are close variants of development types: BuilderDepositRequest (decoder and encoder have the same code as Deposit_Data), BlobSidecarsByRangeRequest and ExecutionPayloadEnvelopesByRangeRequest (the encoder has the same code as SyncAggregatorSelectionData, the decoder differs only in 2 lines of the error path).
So 3 of the 7 generated decoders and 3 of the 8 generated encoders are close variants.
The others (DepositRequest, BeaconBlocksByRangeRequest, PartialDataColumnGroupID, ValidatorIdentity, BuilderPreferences encoder) have no development type of the same kind.
S2: we changed the committed `axioms-gate.json` to the `run` format (includes `modules`, `precheck`, `dump`). The 11 shared keys have the same values.
S3: field cover 34/86 is a lower bound after the stop. It is not a cover ratio. 13 of the 34 are walk claims without produced theorems.
S4: we added the H7 reject classification table to the inventory script (text and cells only, the status rules and totals are the same). BuilderPreferences decoder = reject (Gwei callee).
S5: before the statement commit, the author saw one line of the kindcheck record. That line lists only the names of the BeaconBlocksByRange walk theorems. It has no statement text.
S6: the DepositRequest `desc.json` was copied from the scratch of other work. The sha256 `489fe67a…` is the same as the committed checker record (`gen/desc/results/main.result.json`).
S6: the path in the header of `F24DprSpecChecker.lean` is missing `f24/`. The real file is `prysm/go1.26.10/e2e/f24/engine_v1.DepositRequest.desc.json`. It is a generated file, so we did not fix it.
S7: we added 12 negative tests (`f24/negcases-f24-int9.json`, `f24/negative-f24-int9.json`). Result: 12/12 as expected (4 controls pass, 8 mutations fail inside the target theorem, 0 timeouts, 0 wrong targets).
Targets: `reject_size_spec` (DepositRequest, BeaconBlocksByRange), `reject_complete` (the same two types), the Desc and length of the encoder specification conformance (the same two types).

Integration of H7 (merges `claude/ssz-fv-flat24` `6f20eef` on top of `0923998`, merge commit `e6b46fd`, no review yet):
The stream is linear on top of `0923998`. There were no conflicts. The merge tree id is the same as the tree id of `6f20eef`.
We did not change proof text, statements, generators, checkers, lemmas or pinned versions. The changes are the text of the inventory script (S4) and the new negative tests (S7).
Executed checks (inside the gate and the 6 GiB cap): `lake build E2e E2eAd E2eScal` exit 0, 1542 jobs, 211.7 s.
65 modules were built. This is the same as the 65 `lean/` modules that the stream added. No existing `.olean` changed.
`E2eScal.P2EncCp` was not built again. Maximum memory: process 2.15 GiB, session 2.94 GiB. `lake build --no-build` exit 0.
Axioms gate PASS: 14415 declarations, 12020 theorems, 469 modules, hand list 5085, 0 nonstandard, 0 sorryAx.
Declaration comparison against the dump of the H7 review: 0 CHANGED, 0 REMOVED, 0 ADDED.
Planted control (dump level): a copy with a changed type hash of `E2eScal.F24.dpr_e2e_reject_size_spec` gives exit 1, CHANGED 1.
`regen_check.sh` 86/86 SAME (the earlier 71, H7 generated files 15). It is an integration check, not a new generator result.
`kindcheck.py --selftest` PASS, `p2dec_test.py` 394/394, `p2enc_test.py` 322/322, `own_layout_e2g_r1.py` 16/16 OK.
Inventory rerun (before S4): `INVENTORY.md`, `INVENTORY.json` and `ssz-methods.json` are byte-identical to the committed versions.
We ran it again after S4. The totals are the same. Planted controls 6/6 exit 1, clean input exit 0.
Inventory counts (script output): decoder complete 18/211, partial 10, none 183. Encoder fast path complete 24/211, complete 0.
HashTreeRoot family 0. Types not started 182/211.
Items to fix of the review of the flat-encoder integration (`0923998`, APPROVE):
S1 was closed by appending the premises to the flat-encoder integration line of FINDINGS and to the inventory cell of BASELINE section 3.
S2 was closed by writing the `moveSliceNoCapNoScan` branch and the frame separation premise in section 0.
S3 is open. There is no record of the profiled cause of the limit options (`maxHeartbeats 16000000`, `4000000`, `maxRecDepth 100000`). We wrote the counts in BASELINE section 6.
S4 was closed by replacing the "no INT8 review" text with that review. We did not change the dated text.
S5 record: this merge used `chore(kraken)`. We did not touch the local ref `refs/remotes/offchainlabs/main`.
Not run (integrator): Lean-level planted control, cold build from an empty `.lake`, link check, Go differential, the 67 existing negative tests, x86-64.
The AttestationData encoder is work on another machine. The list and vector work on the other machine is not in this tree. We do not claim it here.
We did not adopt the OPT-R1 pilot. T-7 is deferred. Records: `integration_int9` of `scal/RESULT.json`.
