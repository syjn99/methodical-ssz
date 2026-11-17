# Findings

This file lists the limits that are open at this commit.
Each entry says what does not hold, what it means for a theorem or a check, and where it is.
A change that removes a limit also removes its entry.
How to handle a new finding is in `../README.md` section 7.
Paths are relative to `fv/kraken/`, unless they start with `sszgen/`, `ssz/` or `.github/`.

## Generator and runtime library

### The generator IR gives the fields of a nested container the wrong keys

- What does not hold: a nested container field in the generator IR does not have its own name as key.
  The key is the name of the container type, for example `Checkpoint` for the fields `Epoch` and `Root` of `Source`.
- Effect: the generated Go code does not change.
  A tool that reads these IR keys gets wrong names.
- Where: the `case *types.Struct:` branch of `FieldParser.expand` in `sszgen/representer.go`.
  It writes `f.name`, not `field.Name()`.

### The generator log does not name the package

- What does not hold: a log line of the generator does not show the package path.
  An example is `Generating methods for /StatusV2`.
- Effect: none on the output files.
- Where: `packages.Config.Mode` in `sszgen/importer.go` has no `NeedName`, so `PkgPath` is empty.

### The SSZ methods of the primitive types are not generator output

- What does not hold: the SSZ methods of `Slot`, `Epoch`, `ValidatorIndex`, `Gwei` and `CommitteeIndex` are not generated.
  They are hand-written Prysm code in `consensus-types/primitives`.
  The generated code of many types calls them.
- Effect: each of these methods needs its own specification and proof.
  A generated decoder that calls one depends on the function specification of that method.
- Where: `lean/Prysm/Epoch/`, `lean/Prysm/Slot/`, `lean/Prysm/CommitteeIndex/` and `lean/Prysm/ValidatorIndex/`.
  `prysm/proof-inventory.md` gives the theorems of each method.

### An encoder reject does not keep the spare bytes of the caller array

- What does not hold: on a length reject, the bytes of `dst` beyond `len(dst)` do not stay unchanged.
  The encoder appends the earlier fields before it tests the length of a later field.
- Effect: a reject theorem states the written bytes.
  Only `dst[:len(dst)]` stays unchanged.
  SSZ has no rule for a Go value with a wrong field length, so this is not a specification violation.
- Where: `(*v1alpha1.Checkpoint).MarshalSSZTo` (`Prysm.Checkpoint.Encode.reject_length`).
  `(*v1alpha1.BeaconBlockHeader).MarshalSSZTo` (`lean/Prysm/BeaconBlockHeader/EncodeRejectLength.lean`).

### The AttestationData encoder writes the receiver

- What does not hold: the encoder does not leave a nil `Source` or `Target` unchanged.
  It stores a new zero `Checkpoint` in the receiver.
  The encoder of that zero `Checkpoint` then fails with `ErrBytesLength`.
- Effect: an encoder theorem of this type must state this change of the receiver.
  No such theorem exists.
- Where: `(*v1alpha1.AttestationData).MarshalSSZTo`.

### The bitlist encoder error text differs from some Prysm tests

- What does not hold: some Prysm tests do not get their expected error text from the bitlist length reject.
  The rejected inputs are the same.
- Effect: these Prysm tests fail with the generated code.
  This is a compatibility issue, not a generator defect.
- Where: the Prysm `consensus-types/blocks` tests `TestMarshalPartsMetadata/available_too_large` and `/requests_too_large`.
  Also `TestPartialDataColumn_PartsMetadata/marshal_error_due_max_bitlist_size`.

### The in-place hash call needs an aliasing premise

- What does not hold: `merkleizeChunks` calls `gohashtree.Hash(elements, elements)` with one slice as input and output.
  No proof covers this aliasing.
- Effect: a hash tree root theorem must state the aliasing premise.
- Where: `merkleizeChunks` in `ssz/htr.go`.
  No test of `ssz/` pins the aliasing.

## Tools and machine model

### Kraken cannot parse `bsr`

- What does not hold: the Kraken parser has no `bsr` instruction.
- Effect: `ssz.ValidateBitlist` uses `bsr` for `bits.Len8` in the `GOAMD64=v1` build.
  So the bitlist validation can only be a contract.
- Where: `prysm/go1.26.10/parser-result.json` lists the functions that the parser rejects.

### Kraken cannot parse some operand and padding forms

- What does not hold: the Kraken parser does not read the SIB index `%riz` or multi-byte padding `nop` forms.
- Effect: `link/convert_objdump.py --norm` drops `%riz` and writes the padding as `nop`.
  The link check accepts such a `nop` where its bytes differ from the ELF bytes.
- Where: `link/convert_objdump.py`, the reassembly check of `link/check.py`, and `include_x64_code` in `lean/Machine/Include.lean`.

### The converter does not handle every displacement form

- What does not hold: `link/convert_objdump.py --norm` does not handle the SIB form without a base or the segment form.
  `link/check.py` has no range check of a displacement.
- Effect: none on the pinned ELF, because its link set has none of these forms.
  A new ELF can need a converter change.
- Where: `link/convert_objdump.py`, `link/check.py`.

### Growslice contract gives no lower bound on the remaining heap

- What does not hold: `GrowsliceContract` gives the remaining heap only as an upper bound.
  A second growth call needs a lower bound as its budget premise.
- Effect: in `Prysm.Checkpoint.Encode.grow_any_site_three_cases`, one case ends at the entry of the second growth call.
  The run after that state is not proved.
  The growth branches of the other encoders are not proved.
- Where: `lean/Runtime/Contracts.lean`.
  A new contract form needs a user decision.

### The `ecancel` tactic fails on some atom forms

- What does not hold: `ecancel` does not close some goals.
  It fails when two atoms print the same but elaborate differently, with a trailing `⋆ emp`, and with some atom orders.
  It times out on `uintBytes` of a symbolic value.
  An atom such as `StaticBox (-4 + rcx)` hits the recursion limit.
- Effect: proofs use `generalize` of the byte lists, `rw [show a = a from rfl]`, or `simp only [sep_assoc, sep_emp]` before a sort.
- Where: the separation tactics of Kraken.
  The causes are not known.

### Other tactic gaps

- What does not hold: `address_equation` (`lean/Machine/Step.lean`) does not reduce `Width.W64.bits`.
  A `grind` timeout inside `kstep` cannot be caught.
  `trivial` or `rfl` inside `first` on register goals with symbolic `BitVec` can use more than 6 GiB.
- Effect: proofs use the macro `segment_addr` (`lean/Codec/SegmentAddress.lean`), `load_step` and `store_step`.
  Register goals close with `exact trivial`, `with_reducible rfl` or `toBitVec_inj`.
- Where: `lean/Machine/Step.lean`.

### The content of a format string is not checked

- What does not hold: Lean binds a format string only by its length and by the absence of `%`.
  No check compares its verbs with `FmtErrorfWrapContract`, `FmtErrorfDecimalWrapContract` or `FmtErrorfDecimalDecimalContract`.
- Effect: the agreement of the verbs with the contract is a contract hypothesis.
- Where: `lean/Runtime/Contracts.lean`, `link/README.md` section 6.

### The allocation type argument is not connected to the size

- What does not hold: `MakesliceContract` and `NewobjectContract` do not connect the type descriptor argument to the size.
  For example, the object size 120 of the `Deposit_Data` allocation is a premise.
  No theorem ties it to the data file of the type descriptor.
- Effect: the size is a contract hypothesis.
- Where: `lean/Runtime/Contracts.lean`, `lean/Runtime/NewobjectContract.lean`.

### The proof generator covers only some code forms

- What does not hold: `gen/generator/generator.py` does not cover every field form.
  It covers 8-byte `uint64` fields and byte vectors of 32, 48 and 96 bytes.
  It covers the callees `Slot`, `CommitteeIndex`, `ValidatorIndex` and `Epoch`.
  It refuses byte vectors of other sizes, `bool` fields, the `Gwei` callee, interleaved fields and nested containers.
  On the encoder side, the compiled sites that append a 32-byte field have different instruction texts.
  Only the call step is shared between them.
- Effect: a refused type needs hand proofs.
  A type whose rows in `gen/generator/types.tsv` are all refuse rows has only `Code.lean`.
- Where: `gen/generator/whole_accept.py`, `gen/generator/fast_path.py`.
  The last line of the standard error of a run gives the reason of a refusal.
  A generator change needs user approval.

### The generator summary can be incomplete

- What does not hold: an internal refusal inside one phase can report full coverage in the summary.
  An interrupted run writes no summary.
- Effect: read the exit code of a run, not only its summary.
- Where: the `--summary` output of `gen/generator/generator.py`.

### The accept kind does not constrain the frame size

- What does not hold: `Codec.decodeAcceptKindAnyFrame` does not read the field `frame` of its layout `L`.
  So Lean accepts the `_kind` line of a generated accept theorem with any frame value.
  For example, the frame 104 changed to 96 in `Prysm.BeaconBlockHeader.Decode.generated_accept_kind` still passes Lean.
- Effect: Lean does not check the frame of a generated accept statement.
  `gen/generator/kindcheck.py` rule 12c recomputes the layout from the `.S` file and fails on such a file.
  A hand instance of the kind has no such text check.
  The head, field and epilogue kinds read the frame.
- Where: `decodeAcceptKindAnyFrame` and `decodeFinalStatePredicate` in `lean/Codec/Kind/DecodeAcceptAnyFrame.lean`.
  `check_whole_accept` in `gen/generator/kindcheck.py`.

### `kindcheck.py` binds the code constant to the `.S` file only for the encoder fast path

- What does not hold: rule 13c of `gen/generator/kindcheck.py` binds the code constant to the `.S` file of the header.
  This rule applies only to the encoder fast-path files (`GeneratedEncodeFastPath.lean`).
  No check binds the code constant of a decoder file (`GeneratedDecodeAccept.lean`) to its `.S` file.
  This holds for the step chain, the whole-accept block and the `uint64` file.
  `kindcheck.py` does not check the `.S` label against the IR type.
- Effect: the kind parameters of a decoder file come from the `.S` file of the header.
  Its theorems can name another code constant.
  A reader checks the `Code.lean` include of each generated decoder file.
- Where: `check_fast_path` and `check_whole_accept` in `gen/generator/kindcheck.py`.

### Open items of the encoder checker

- What does not hold: the macro `encoder_address_equation` has no namespace.
  The negative tests that compare the IR with the code change one theorem only.
  No mutant changes a whole file.
- Effect: each item needs a checker or a test change.
- Where: `lean/Codec/EncodeFieldHelpers.lean`, `gen/checks/fast_path_layout.py`, `gen/checks/negative-cases/`.

## Proofs and checks

### CI does not run the Python checks

- What does not hold: the CI workflow runs only the Lean build and the axioms gate.
  It does not run `kindcheck.py`, `regenerate_and_compare.py` or `gen/checks/python_checks.sh`.
- Effect: the statement check of a generated theorem holds only after a run of `kindcheck.py` by hand.
- Where: `.github/workflows/fv-lean.yaml`.

### The negative suite with Lean runs only on Linux

- What does not hold: `gen/checks/negative.py` does not run its cases on a system without `/proc`, for example macOS.
  It runs each case under `gen/tools/memory_limit.py`.
  Both programs read `/proc`.
- Effect: on macOS, the suite runs in a Linux container with the toolchain of `lean/lean-toolchain`.
- Where: `gen/checks/negative.py`, `gen/tools/memory_limit.py`.

### The negative classifier sees only the error text

- What does not hold: `gen/checks/negative.py` does not see whether an error comes from the mutated text.
  It classifies a mutant by the text and the line of the Lean errors.
  A first error that is a parse error or an unknown name gets the class `wrong_target`.
  The pattern list `WRONG_TARGET` can be incomplete.
- Effect: an `inside` result can come from an error that does not test the code.
  Read the first error of each result row.
- Where: `classify` and `WRONG_TARGET` in `gen/checks/negative.py`.

### No negative case changes a memory word of some accept post-states

- What does not hold: no negative case covers a changed memory word in the post-state of `Decode.accept_spec` of these types.
  The types are SyncCommitteeMessage, PendingConsolidation, SyncAggregatorSelectionData, ValidatorBalance, VoluntaryExit and Deposit_Data.
  Lean does not refute such a statement mutant within the heartbeat limit.
- Effect: no case shows that a wrong memory word in these post-states fails.
  The generated accept theorems that these proofs use keep their own mutants.
- Where: `lean/Prysm/<GoTypeName>/DecodeSpec.lean` of these types, `gen/checks/negative-cases/`.

### The Go value check exists only for Checkpoint

- What does not hold: only Checkpoint has a Lean predicate for a valid Go value of the receiver.
  For the witnesses of the other types, no theorem shows that the receiver is a Go value of the type.
- Effect: for these witnesses, a reader checks the receiver block against the Go layout.
- Where: `lean/Prysm/Checkpoint/GoValue.lean`, `lean/Prysm/Checkpoint/GoValueWitness.lean`.

### Some code constants have no theorem

- What does not hold: `Prysm.AttestationData.Code.marshalSSZTo` and `Prysm.AttestationData.Code.sizeSSZ` have no theorem.
  The constants of a type directory that holds only `Code.lean` have no theorem.
  These are the types that the generator refuses (the refuse rows of `gen/generator/types.tsv`).
  Some `.S` files of the link set have no constant: no `include_x64_code` line of `lean/` names them.
  The rule to find them: a file of `prysm/go1.26.10/link-set/norm/`, other than `all.S`, whose name no `include_x64_code` line names.
  They are the encoder and size functions of the primitive types of `consensus-types/primitives`.
- Effect: the functions of these constants and files are not proved.
  The link check covers their `.S` files.
- Where: `lean/Prysm/AttestationData/Code.lean`, `lean/Prysm/<GoTypeName>/Code.lean` of the types with only that module, `prysm/go1.26.10/link-set/norm/`.

### Slot and CommitteeIndex have no size-reject theorem

- What does not hold: `Prysm.Slot.Decode.reject_size` and `Prysm.CommitteeIndex.Decode.reject_size` do not exist.
  The two decoders have no `DecodeRejectSize.lean` and no witness of the reject path.
  ValidatorIndex and Epoch have these modules.
- Effect: the reject path `len(buf) ≠ 8` of the two decoders is not proved.
- Where: `lean/Prysm/Slot/`, `lean/Prysm/CommitteeIndex/`.

### Some lemmas and tactics exist two times

- What does not hold: the tree does not have one copy of each of these items.
  - `lean/Codec/Segment/ByteSliceList.lean` and `lean/Codec/Segment/Bytes32LoopProof.lean` hold the loop lemmas for any count.
    `lean/Prysm/HistoricalBatch/DecodeLoopLemmas.lean` and `lean/Prysm/SyncCommittee/DecodeLoopLemmas.lean` hold the same lemmas for one count.
  - `lean/Codec/Segment/SizeReject.lean` and `lean/Codec/DecodeRejectSizeAnyFrame.lean` both give a size reject for any frame.
  - `lean/Machine/WitnessSplit.lean` is the macro of `lean/Machine/WitnessHost.lean` with a larger simp set.
  - Checkpoint has two forms of its encoder covers: `EncodeCover.lean` and `EncodeCoverFramed.lean`.
- Effect: none on a theorem.
  A new proof must use the general form in `Codec` and `Machine/WitnessHost.lean`.
- Where: the files above.
  Before a proof moves to the general form, show that its statement stays the same.

### Some witness modules do not follow the name rule

- What does not hold: the rule of `lean/README.md` section 8 is "`Witness` + the module of the theorem", with the same namespace.
  `lean/Prysm/Checkpoint/WitnessDecodeAcceptSpec.lean` and `WitnessDecodeRejectSizeSpec.lean` use the namespace of another witness module.
  `lean/Prysm/DataColumnsByRootIdentifier/WitnessDecodeRejectSize.lean` has one more namespace level, `RejectSize`.
  `gen/tools/proof_inventory.py` has one extra name for that module (`WIT_REJECT_DEFAULT`).
- Effect: none on a theorem.
  A reader cannot find these witnesses by the rule.
- Where: the files above.

### Two bump allocator models differ only in a label

- What does not hold: `Prysm/RuntimeModel/BumpMakesliceUint64DispatchForDataColumnsByRootIdentifier.S` is `Prysm/RuntimeModel/BumpMakesliceUint64Dispatch.S` with another label.
  `diff` of the two files shows only the label `L_model_bump_uint64` and `L_model_bump_uint64_columns`.
  Each has its own module with the same two theorems.
  No witness host holds both models, so the tree shows no reason for two labels.
- Effect: an open duplicate of a runtime model and of its proofs.
- Where: `lean/Prysm/RuntimeModel/BumpAllocatorUint64DispatchForDataColumnsByRootIdentifier.lean`, `lean/Prysm/RuntimeModel/BumpAllocatorUint64AndStructDispatch.lean`.

### The broken copies of `kindcheck.py` cover only some checks

- What does not hold: `gen/generator/kindcheck_broken_copies_test.py` switches off only the sub-rules of its table `BROKEN`.
  All of them are sub-rules of rule 13.
  These checks of rule 13 have no broken copy:
  - 13b: the layout name, the layout field line, the top-level line, the namespace, the count of layout defs, the `hk` binder and the first binder line;
  - 13c: the proof line, the tail and the `sep` of a kind line, the count of boundary states, the layout field set and the missing layout def;
  - 13e: the identity form of the `_statement`;
  - the one valid `FAST-PATH-JSON` line.
  Rules 2 to 12 have no broken copy.
  The selftest has no case for a wrong order of the theorem list of rule 13b.
- Effect: no test shows that the selftest fails when one of these checks is switched off.
- Where: `gen/generator/kindcheck_broken_copies_test.py`, `check_fast_path` and the selftest of `gen/generator/kindcheck.py`.

### Some result files need the ELF, Go or Lean to make them again

- What does not hold: these tracked files cannot be made again from tracked files alone.
  - They need the Prysm ELF: the link set `prysm/go1.26.10/link-set/**` with its `RESULT`, `build-ids.txt`, `functions.json` and `ssz-methods.json` of `prysm/go1.26.10/`.
  - They need the ELF and Lean: `prysm/go1.26.10/parser-result.json` (a log of `gen/kraken-parser/ParserRun.lean`).
  - They need Lean: `gen/desc/results/main.result.json` and `prysm/proof-inventory.md`, `prysm/proof-inventory.json`.
  - They need a Prysm tree and Go: `prysm/_generated/**`, `prysm/ir/*.json` and `prysm/diff/generated-go-diff.json`.
- Effect: `gen/checks/regenerate_and_compare.py` and `gen/checks/python_checks.sh` do not cover them.
  A check of these files needs the tools of `README.md` sections 3 and 5.
- Where: `README.md` section 7 gives the command of each file.

### A Lean error does not stop the file

- What does not hold: Lean does not stop at a failed proof.
  It registers the theorem with `sorryAx` and continues.
  `case tag => tac` logs an error, admits the goal and continues.
- Effect: a file can look clean when one of its theorems is not proved.
  A result counts only when `#print axioms` of every theorem that it uses has no `sorryAx`.
  A job command must end with the Lean exit code.
  A command that ends with `echo` hides a failure.
- Where: every Lean run.
  The axioms gate (`gen/checks/axioms_gate.py`) checks the built tree.

### Limit options without a profiled cause

- What does not hold: many files set `maxHeartbeats` or `maxRecDepth` above the default without a written, profiled cause.
  Generated files and the files that the tools of `gen/flat-types/` write do this too.
- Effect: these values are not a model for new work.
  They stay until a profile exists or the user accepts them.
- Where: `grep -rn "set_option max" lean/Prysm lean/Codec`.

### Recursion depth limits without a located cause

- What does not hold: some witness examples raise `maxRecDepth`, and the cause is not located.
- Effect: the rule asks for a profiled cause for each raised limit.
- Where: `lean/Prysm/DataColumnsByRootIdentifier/WitnessEncodeFastPath.lean` (limit 4000).
  `lean/Prysm/DataColumnsByRootIdentifier/WitnessEncodeGrowFirstSite.lean` (limit 8000).
  The comment at each place gives the measured values.

### Theorems that end with `⋆ True`

- What does not hold: these Checkpoint theorems do not state the rest of memory.
  They are `Prysm.Checkpoint.DecodeThenEncode.encode_decoded_receiver` and `Prysm.Checkpoint.Encode.fast_path_spec`.
  They are also `Prysm.Checkpoint.DecodeThenEncode.round_trip`, `Prysm.Checkpoint.Encode.cover` and `Prysm.Checkpoint.Encode.reject_length_cover`.
- Effect: the component theorems and the `*_framed` cover theorems state the exact frame.
  The composition has no framed version.
  `Prysm.BeaconBlockHeader.Decode.generated_accept` hides three argument-area slots in one 24-byte existential.
  They are dead stack only.
- Where: `lean/Prysm/Checkpoint/`, `lean/Prysm/BeaconBlockHeader/GeneratedDecodeAccept.lean`.

### Docstrings that say more than their theorem

- What does not hold: some docstrings of `Decode.reject_complete` say more than the theorem.
  They say that the input reaches the `ssz.ErrSize` site.
  The theorem proves only `size ≠ N`.
- Effect: a reader must take the statement, not the docstring.
- Where: `lean/Prysm/<GoTypeName>/DecodeSpec.lean` of `PendingDeposit`, `PowBlock`, `SyncCommitteeMessage` and `PendingConsolidation`.
  The fix is a `.lean` edit.

### Unreachable error wraps hold only with the callee specifications

- What does not hold: an unreachable error wrap theorem does not say that the wrap is unreachable for every input.
  They state a conditional skip: if the callee returns `rax = 0`, the code skips the wrap.
- Effect: unreachability for every input holds only with the callee specifications.
  Examples are `Prysm.Slot.Decode.accept_function_spec` and `Prysm.ValidatorIndex.Decode.accept_function_spec`.
- Where: `lean/Prysm/BeaconBlockHeader/DecodeErrorUnreachable.lean`.

### No check shows that a hand `Desc` is independent of the checker `Desc`

- What does not hold: no check shows that a hand `Desc` was written without the checker `Desc`.
  The independence is by content only: most hand `Desc` copy the consensus-specs definition.
  Some hand `Desc` are written from the Prysm proto definition, not from consensus-specs.
  `grep -l 'from the Prysm proto' lean/Prysm/*/SpecDescription.lean` lists them.
  Such a `Desc` has the same source as the `Desc` producer, so it is not independent of the checker `Desc`.
  The tree does not record whether consensus-specs defines these containers.
- Effect: the specification side of a theorem rests on a review of the hand `Desc` against consensus-specs.
  For a type with a hand `Desc` from the proto, no theorem compares the code with an independent specification.
  Its codec equality with the checker `Desc`, where one exists, compares two descriptions of one source.
- Where: `lean/Prysm/<GoTypeName>/SpecDescription.lean`.

### Only three generated encoders have a hand statement

- What does not hold: the tree gives no reason why only some generated encoder fast paths have a hand statement.
  Deposit_Data, PowBlock and SyncCommitteeMessage have `EncodeFastPathStatements.lean` and a statement tie.
  The other generated encoder fast paths have only the kind check, and Checkpoint has a hand theorem.
- Effect: none on a theorem.
  For the other types, only the kind and `gen/generator/kindcheck.py` check the generated statement.
- Where: `lean/Prysm/<GoTypeName>/EncodeFastPathStatements.lean` and `EncodeFastPathStatementTie.lean`.

### Some companion files of generated types are written by a person

- What does not hold: a tool of `gen/flat-types/` writes a file only for a row with the companion of the file.
  The rows are in `gen/generator/types.tsv`.
  For some types with a generated decoder or encoder, a person writes `DecodeSpec.lean`, `Spec.lean` or `WitnessGeneratedDecodeAccept.lean`.
  The rules and the types:
  - `Spec.lean` of HistoricalSummary and SigningData: these types have no uint64 field.
    The text of `flat_types_spec.py` for a type without a uint64 field does not build.
  - `Spec.lean`, `DecodeSpec.lean` and `WitnessGeneratedDecodeRejectSize.lean` of PowBlock: its field `totalDifficulty` is a `Fin (2 ^ 256)`.
    The table `SPEC_TYPES` of `flat_types_spec.py` has no field kind for it, and the three tools read that table.
  - `Spec.lean` of Checkpoint: other modules use declarations that the tool does not write.
    An example is `Prysm.Checkpoint.SszValue.toValue_surjective` in `lean/Prysm/AttestationData/Spec.lean`.
  - `WitnessGeneratedDecodeAccept.lean` of the `decoder --whole-accept` rows without the companion `accept-witness`.
    These types are BeaconBlockHeader, Eth1Data, BlobIdentifier, DepositMessage, SyncCommitteeMessage, PendingConsolidation, PowBlock, HistoricalSummary, SigningData, ValidatorBalance and VoluntaryExit.
    The memory block or the program of the hand witness differs from the forms of `flat_types_witness.py`.
    For example, the witness of ValidatorBalance calls ValidatorIndex, and the form `frame_0x38` calls Slot.
  - `WitnessGeneratedDecodeAccept.lean` of the `uint64` rows (ValidatorIndex, Epoch, Slot and CommitteeIndex): `flat_types_witness.py` has no form for the `uint64` decoder.
- Effect: `gen/checks/regenerate_and_compare.py` does not compare these files with a tool output.
  The build and the axioms gate check them, and a reviewer reads them.
- Where: `lean/Prysm/<GoTypeName>/` of these types, the tools of `gen/flat-types/`, the column `companions` of `gen/generator/types.tsv`.

### The proof inventory trusts its method list

- What does not hold: `gen/tools/proof_inventory.py run` does not bind `prysm/go1.26.10/ssz-methods.json` to the ELF.
  Only the `methods` mode and a comparison of its output bind that file to the ELF.
  The tool derives a row for each type directory whose name is a type of that file.
  A type directory with another name gives a `FAIL` line.
- Effect: the inventory table is correct only for a method list that matches the ELF.
- Where: `gen/tools/proof_inventory.py`.

### Paths that the proofs do not cover

- What does not hold: no theorem covers these paths.
  - The stack growth path and the write barrier path of every function, which the premises exclude.
  - The encoder growth branches (see the growslice entry) and the length rejects with a small capacity.
  - The `moveSliceNoCapNoScan` branch of `PowBlock`, `HistoricalSummary` and `SigningData`.
  - The hash tree root methods of every type.
- Effect: the frame separation premise of the encoders is not justified for every Go caller.
  The `IndexedAttestation` alignment and overflow rejects are proved only with the premise that the error word is not zero.
- Where: `prysm/proof-inventory.md` lists the paths not proved for each method.

## Target and environment

### No run on x86-64 hardware

- What does not hold: no test compares Kraken with an x86-64 CPU.
- Effect: the Go differential checks run on the host.
  They check Go semantics, not the amd64 machine code.
- Where: `gen/checks/differential.py`.

### The Go layout comes from `go/types`

- What does not hold: the proofs do not read the receiver layout from the ELF.
  The layout comes from the gc amd64 size rules of `go/types` (`prysm/ir/ir-mainnet.json`, `go_fields`).
  The ELF `abi.Type` of a receiver type has no named symbol.
- Effect: the receiver layout is a trust item.
  No amd64 run confirms it.
- Where: `prysm/ir/ir-mainnet.json`, `lean/Prysm/Checkpoint/Layout.lean`, and the layout comments of the hand proofs.

### The runtime contracts are not proved on the compiled runtime

- What does not hold: no proof shows that the compiled Go runtime satisfies the contracts.
  The contracts come from a reading of the Go 1.26.3 runtime source.
  `gen/checks/runtime_diff.py` compares the sources of the functions behind each contract in Go 1.26.3 and Go 1.26.10.
  No check compares the compiled runtime code.
- Effect: the contracts are an accepted trust item.
  They also assume no garbage collection during a call and a successful allocation.
- Where: `lean/Runtime/Contracts.lean`, `gen/checks/runtime_diff.py`.

### A pinned record holds a container path

- What does not hold: `prysm/go1.26.10/prysm-go.mod.diff` is not free of absolute paths.
  Its `replace` line names the container path `/workspace/methodical-ssz-generator`.
- Effect: the ELF records this path, so the line must keep it.
  A rebuild needs the generator tree at this path.
- Where: `prysm/go1.26.10/prysm-go.mod.diff`, `README.md` section 3.
