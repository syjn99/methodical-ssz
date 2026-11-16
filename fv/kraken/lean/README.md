# lean: specifications, contracts and machine-code proofs

This is the Lake project of the proofs.
The libraries are in `lakefile.toml`.
The toolchain is in `lean-toolchain`.
Kraken and EthLib are Lake dependencies at pinned commits.
The design principles are in `../../README.md`.
The build commands are in `../README.md` section 5.

## 1. Libraries

The libraries `Spec`, `Machine`, `Runtime` and `Codec` are the shared layer.
The library `Prysm` holds the proofs of the Prysm types, one directory for each type.
`../README.md` section 7 gives who writes each kind of file and what checks it.
`../NEW-TYPE.md` gives the steps to prove a new type.

**`Spec`.** The general lemma `Spec/DeserializeOfSerialize.lean` and the specifications of the hand test types (`Spec/Test*.lean`).
The lemma: if `serialize` of every Go value `g` gives `enc g`, every accepted input is `enc g` of one value.
So a machine proof says what the code does on `enc g`, and that the code rejects every other input.
The hand test types have no ELF.
The `Desc` checker `../gen/desc-checker/DescChecker.lean` imports them for its tests.
`Spec/TestCheckpointAndAttestationData.lean` specifies reduced `Checkpoint` and `AttestationData` types without the protobuf fields.
`Spec` imports only EthLib and `Spec`.
It holds no machine code and no Prysm type.

**`Machine`.** Helpers on the Kraken machine model.
They are the one-instruction step lemmas and tactics (`Machine/Step.lean`), and the stack frame, byte, label and flag lemmas.
It also has the commands that read code and data files (`Machine/Include.lean`).
It has the witness host builder and tactics (`Machine/WitnessHost.lean`, `Machine/WitnessSplit.lean`).
It holds no runtime contract and no Prysm type.

**`Runtime`.** The contracts of the Go runtime callees (`Runtime/Contracts.lean`, `Runtime/NewobjectContract.lean`) and their models.
A model is a small assembly program (`Runtime/*.S`) with theorems that it satisfies its contract.
Examples are a bump allocator, a memory copy and error formatting.
A runtime model that reads ELF data of the link set is in `Prysm/RuntimeModel/`.
`Runtime` does not import `Prysm`.

**`Codec`.** Lemmas and statement kinds that name no single Prysm type.
Examples are the `uint64` decoder pattern (`Codec/Uint64Decoder.lean`) and the fixed-bytes field patterns (`Codec/FixedBytesDecode*.lean`).
Others are the encoder step lemmas (`Codec/Encode*.lean`, `Codec/Bytes32Encode.lean`) and the stack guard lemma (`Codec/StackGuard.lean`).
`Codec/Kind/` holds the statement kinds of the generated proofs (`../gen/README.md` section 4).
The whole accept kind is in `Codec/Kind/DecodeAcceptAnyFrame.lean` and the encoder fast-path kind in `Codec/Kind/EncodeFastPathAnyFrame.lean`.
Their field list is in `Codec/Kind/ContainerField.lean`.
The statement kind of a callee call is in `Codec/CalleeDecodeWindow.lean`.
`Codec/Segment/` holds segment and loop lemmas for any size or element count.
A lemma that only one type uses belongs in the directory of that type, not in `Codec`.

**`Prysm`.** One directory for each Prysm type, `Prysm/<GoTypeName>/`, namespace `Prysm.<GoTypeName>`.
A type directory holds only the modules of that type.
Section 8 gives the role names of its modules.
Two directories of `Prysm/` are not types:

- `Prysm/ElfData/PrysmTarget.lean` holds the ELF data of the link set `../prysm/go1.26.10/link-set` (namespace `ElfData.PrysmTarget`).
  The command `data_include` (`Machine/Include.lean`) reads each data file.
  The table `runtime.staticuint64s` of the same link set is `Runtime.Data.staticuint64s` (`Runtime/StaticUint64s.lean`).
- `Prysm/RuntimeModel/` holds witness-only models of runtime functions that read ELF data of the link set.
  An example is a bump allocator that dispatches on a type word.

The data namespace has the root `ElfData`, not `Prysm`, because of the order of names in `simp`.
`simp` with `Std.ExtHashMap.sep_comm` and `sep_comm_l` orders the parts of a separating conjunction by constant names.
The order is Lean `Name.cmp`, with the root component first.
The root `ElfData` sorts before `HAdd`, `HSub`, `Host`, `Int`, `List` and `Eq`.
The root `Prysm` sorts after them.
Some `simp` proofs depend on that order, so a data name with another root can make them fail.
A data name is the id of its data file, and the id names the ELF item.
Examples: `sszErrSize` is the address of the global `ssz.ErrSize`, `typeUint8` the type descriptor of `uint8`.
`formatSlot` is the format string `Slot: %w`.
The item table `../prysm/go1.26.10/link-set.tsv` gives each id.
The lemmas `<id>_addr_eq` restate an address.

The types of `../gen/generator/gen.sh` and `../gen/flat-types/run_generators.sh` have generated modules `Prysm/<GoTypeName>/Generated*.lean`.
Section 8 tells which of them a generator writes.
A type directory with only `Code.lean`, or with `Code.lean` and `Statements.lean`, holds a type that the generator refuses.
No theorem proves those statements.

### Dependencies

The import lines of the tree give these relations:

```text
EthLib -> Spec -> Machine -> Runtime
Codec <-> Prysm (at module level, both directions)
```

- `Spec` imports only EthLib and `Spec`.
  `Machine` imports only Kraken, Std, Lean and `Machine`.
  (`Machine/Include.lean` has `public meta import Lean` for its elaborators.)
  `Runtime` imports only Kraken, `Machine` and `Runtime`.
  So these three libraries import only libraries to their left, and Lean itself.
- `Codec` and `Prysm` import each other at module level.
  Some `Codec` modules import a `Prysm` module, and many `Prysm` modules import a `Codec` module.
  Lean forbids a cycle of modules, so the module graph has no cycle.
  Only the libraries have no order.
- A `Codec` module that imports `Prysm` uses code or data of a type in a general lemma or kind.
  An example is `Codec/CalleeDecode.lean`, which uses the decoder specifications of `Prysm/Slot/`, `Prysm/Epoch/` and `Prysm/ValidatorIndex/`.
  `Codec/Segment/SizeRejectInstances.lean` ties a general lemma to the lemmas of types.
- `Prysm/Deposit/` imports modules of the flat type `Prysm/Deposit_Data/`.

A new type gets its own directory `Prysm/<GoTypeName>/`.
Do not change a reviewed module to add a new type.

## 2. How machine code enters Lean

1. `../link/convert_objdump.py` converts the disassembly of one function into a labeled `.S` file.
2. `include_x64_code "<path>.S"` (`Machine/Include.lean`) parses the file with the Kraken parser when Lean elaborates it.
   The result is a `Program` constant, for example `Prysm.SyncAggregate.Code.unmarshalSSZ`.
3. A data file holds the bytes or the address of one ELF data item.
   Examples are a format string and a type descriptor.
   `data_include <id>` (`Machine/Include.lean`) reads it from the Prysm link set.
   It defines `<id> : List UInt8` and `<id>_addr : BitVec 64`.
   No byte or offset is written by hand.
4. `../link/check.py` compares the `.S` files and the data files with the ELF.

The `.S` and data files are not Lean imports.
So `lakefile.toml` declares their directories as `input_dir` entries in the `needs` of each library.
Lake then puts the file contents into the input hash, and a changed file makes Lake build the proofs again.
When you add a code directory, add it as an `input_dir` of the library.
A `lakefile.toml` change needs user approval.

## 3. Shape of a main theorem

The statement of a hand main theorem is often a `def` of type `Prop` in a `Statements` module.
The theorem then has that type.
This example is the size reject of the SyncAggregate decoder (`Prysm/SyncAggregate/Statements.lean`).
Its proof is `Prysm.SyncAggregate.Decode.reject_size` in `Prysm/SyncAggregate/DecodeRejectSize.lean`.

```lean
def Prysm.SyncAggregate.Decode.reject_size_statement : Prop :=
  ∀ (k : Nat) (hk : unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh unmarshalSSZ k)
    (s : MachineData) (ra guard e0 e1 : UInt64) (fp s2 : List UInt8) (hfp : fp.length = 8) (h2 : s2.length = 8)
    (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At ElfData.PrysmTarget.sszErrSize_addr)
      ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrSize" + 8).toBitVec) ⋆ R)
    (hguard : guard.toNat < s.regs.rsp.toNat) (hlen : s.regs.rcx ≠ 160),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = e0 ∧ st.data.regs.rbx = e1
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14
        ∧ (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At ElfData.PrysmTarget.sszErrSize_addr)
          ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrSize" + 8).toBitVec) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩
```

Line by line:

- `hk`: the converted function sits at index `k` of the host program.
  `hf`: no label of the function occurs before it in the program.
- `s` is the machine state at entry.
  `ra` is the return address, and `guard` is the stack limit of the goroutine.
  `e0` and `e1` are the two words of the error value `ssz.ErrSize`.
- `fp` and `s2` are the old bytes of the saved `rbp` slot and of one register spill slot.
  Only their length is given.
- `R` is the frame: all other memory of the caller, the receiver and the input included.
- `h_mem` gives the memory as separate fragments (`⋆`).
  They are the return address at `rsp`, the two stack slots, the guard word, the error value and `R`.
  The address of the error value comes from the data include.
  It is not a hand number.
- `hguard`: the guard is below `rsp`, so the stack growth branch is not taken.
- `hlen`: the input length (register `rcx` in the Go register ABI) is not 160.
- The conclusion says that every execution from the entry reaches a state with these properties.
  The program counter is `ra`, and `rax`, `rbx` hold the error words.
  `rsp` is entry `rsp + 8`, and `rbp` and `r14` are unchanged.
- The final memory names every fragment of the premise again.
  Only the two stack slots changed.
  `R` is unchanged, and there is no `⋆ True`.

A specification theorem extends a machine theorem.
For example, `Prysm.SyncAggregate.Decode.reject_size_spec_statement` adds the premise `rcx = bs.size` and the conclusion that EthLib `deserialize` returns an error.
An accept theorem adds the contract hypotheses, for example `MakesliceContract` and `MemmoveContract`.
It also adds the heap budget `Heap avail`, the receiver fragments and a stack window `S` for the callees.

## 4. Contracts and function specifications

A contract describes a callee at its label, for every machine state, return address and frame `F`.
It gives the argument registers and the stack window of `S` scratch bytes below the return slot.
It gives the spill slots that the callee can write.
It also gives the heap budget and the result.
Its conclusion keeps `rsp + 8`, `r14`, `rbp` and the frame `F`.
The forms are in `Runtime/Contracts.lean` and `Runtime/NewobjectContract.lean` (runtime functions).

| Contract | Callee |
| --- | --- |
| `MakesliceContract` | `runtime.makeslice`: a zero block of `esz · cnt` bytes from the heap |
| `NewobjectContract` | `runtime.newobject`: a zero block of `sz` bytes |
| `GrowsliceContract` | `runtime.growslice`: a new block that holds the old bytes |
| `MemmoveContract` | `runtime.memmove`: copy between disjoint ranges only |
| `ConvT64Contract` | `runtime.convT64`: an 8-byte box, or an entry of the static table for values below 256 |
| `FmtErrorfNilContract`, `FmtErrorfWrapContract`, `FmtErrorfDecimalWrapContract`, `FmtErrorfDecimalDecimalContract` | `fmt.Errorf` with no argument, `%w`, `%d %w` and `%d %d` |

A hand-written callee, for example `(*primitives.Epoch).UnmarshalSSZ`, gets a function specification of the same form.
Examples are `Prysm.Epoch.Decode.accept_function_spec` and `Prysm.Slot.Decode.accept_function_spec`.
A theorem about the callee code (`*_holds`) proves the specification.

A contract is a hypothesis because no proof covers the compiled Go runtime.
The proof uses the contract at each call site and continues from any state that satisfies its conclusion.
If the conclusion decides a branch (for example `rax ≠ 0`), the proof follows that branch.
Otherwise the proof covers both branches.
A contract can be contradictory.
Its form is not evidence.
Only a runtime model that satisfies it and a witness show that it can hold.
The contracts assume that no garbage collection runs during the call, and that allocation succeeds.

## 5. The specification side

A Prysm type has a hand `Desc`.
It also has a checker `Desc` when the `Desc` checker accepted a producer file for it.

- The hand `Desc` `Prysm.<GoTypeName>.desc` is written by hand from the consensus-specs definition.
  It does not use the checker `Desc`.
  It is in `Spec.lean`, `SpecDescription.lean` or `SpecDefinitions.lean` of the type.
  Example: `Prysm.Checkpoint.desc` in `Prysm/Checkpoint/Spec.lean`.
- The checker `Desc` `Prysm.<GoTypeName>.checkerDesc` is in `SpecChecker.lean`.
  `../gen/checks/desc_to_lean.py` or `../gen/checks/list_desc_to_lean.py` writes it from a file of `../prysm/go1.26.10/evidence/`.
  The checker in `../gen/desc-checker/` accepted that file.
  A type without such a file has no `SpecChecker.lean`.
- Codec equality theorems show that both give the same `serialize` and `deserialize`.
  Example: `Prysm.Checkpoint.desc_serialize_checker` in `Prysm/Checkpoint/SpecEquivalence.lean`.
  A type without `SpecEquivalence.lean` has these theorems in `Spec.lean`.

The theorems use the hand `Desc`.
For a Prysm type, the checker compares the `Desc` file only with the inventory.
It does not compare it with the specification.
A structure such as `Prysm.Checkpoint.SszValue` holds the SSZ content of a Go value.
`toValue` maps it to an EthLib value, and an `enc` function such as `Prysm.Checkpoint.SszValue.encode` gives its bytes.
Fields without an SSZ value (the protobuf fields `state`, `unknownFields`, `sizeCache`) stay as unchanged memory in the machine theorems.

The connection to EthLib has these theorem forms:

- decoder accept: if EthLib accepts the input as `v`, there is a Go value `g` with `toValue g = v`.
  The machine code writes `g` to the receiver (`Decode.accept_spec`).
- decoder reject: on an input that EthLib rejects, the machine code returns the Go error (`Decode.reject_<cause>_spec`).
- reject completeness: every input that EthLib rejects falls in a proved reject path (`Decode.reject_complete`).
- encoder: the code writes the bytes of `serialize desc (toValue g)` (`Encode.fast_path_spec`, `Encode.generated_fast_spec`).

## 6. Witnesses

A witness module builds one concrete `Host` with `Machine.Witness.mkHost` (`Machine/WitnessHost.lean`).
The program is the data labels, the real converted function and the runtime models.
A theorem `runs` (or `runs_<case>`) applies the main theorem to a concrete memory block and discharges every premise.
The runtime models discharge the contract hypotheses.
Example: `Prysm.SyncAggregate.Witness.DecodeAccept.runs`.
For a variable length, the witnesses cover the empty value, one element and the maximum.
The receiver in a witness must be a Go value of the type.
`Prysm/Checkpoint/GoValue.lean` gives a Lean predicate for this check.
Use one witness host for each file.
Two `Host` instances in one file make instance resolution choose the wrong host.

The name rule is in section 8: `Witness` + the module of the theorem, namespace `Prysm.<GoTypeName>.Witness.<that module>`.
A witness of a theorem that shares its module with other main theorems takes the role of that theorem.
Examples: `WitnessGeneratedDecodeRejectSize` applies `Decode.generated_reject` of `GeneratedDecodeAccept.lean`.
`Prysm/Checkpoint/WitnessSize.lean` applies `Size.result` of `EncodeSpec.lean`.
`WitnessBumpAllocator.lean` is not a witness of a theorem.
It holds the bump allocator model that the witnesses of its type use, with a `.S` file.

## 7. Proof conventions

- Do not use `sorry`, `admit`, a new `axiom`, `native_decide` or `bv_decide`.
- Do not change a committed statement.
  Add a new statement with a new name and a reason.
- Keep `maxHeartbeats` and `maxRecDepth` at the default.
  If a proof needs more, profile the declaration first.
  Then write the measured cause in words in a comment above the `set_option` line.
  `Prysm/IndexedAttestation/DecodeAccept.lean` has an example.
- Many files have limit options without such a comment (`../FINDINGS.md`).
  Do not copy them as a model for new work.
- Use `Machine.cmp_be_false` or `Codec.lea_cmp_be_false` for the stack guard branch.
  A `simp` and `omega` proof of that branch can use too much kernel memory.
- Split a long straight-line proof into segments over the fragments that each segment touches, then compose them.
- A scratch result is closed only when `#print axioms` of every theorem that it uses has no `sorryAx`.
  The list must also not hold the theorem itself.
- Build one heavy job at a time.
  After a failed build, run `lake build --no-build` before you trust any `.olean`.

## 8. Names

A module of a Prysm type is `Prysm/<GoTypeName>/<Role>.lean` in the library `Prysm`.
Its namespace is `Prysm.<GoTypeName>`.
`<GoTypeName>` is the Go type name as the Go source writes it.
It is never an abbreviation.
A declaration of the type uses a dotted name for the function part.
An example is `theorem Decode.reject_size` inside `namespace Prysm.Checkpoint`.
External names keep the form of their source: ELF symbols and `.S` labels, Go names, and the names of Kraken, Lean and EthLib.
Examples are `Deposit_Data`, `ENRForkID` and the label `runtime.makeslice`.

| Role | Content of the module |
| --- | --- |
| `Code` | Program constants read from the converted `.S` files (hand) |
| `Layout` | Go struct layout from the IR: offsets and sizes (`../gen/checks/layout.py`, `attestation_data_layout.py`) |
| `EncodeLayout` | Hand encoder frame layout that `gen.sh` gives the generator with `--hand-layout` |
| `GoValue`, `GoValueWitness` | Validity of the Go value of the receiver, and its witness |
| `Spec` | The `SszValue` structure, its bridge lemmas to EthLib and, for some types, the hand `Desc` |
| `SpecDescription` | The hand `Desc` alone |
| `SpecDefinitions` | The hand `Desc` and the definitions that the frozen statements use |
| `SpecChecker` | The checker `Desc` (`../gen/checks/desc_to_lean.py`, `list_desc_to_lean.py`) |
| `SpecEquivalence` | Codec equality of the hand `Desc` and the checker `Desc` |
| `SpecDecodeBridge` | Decoder-side lemmas of the specification bridge |
| `Statements`, `Statements` + qualifier | Statement definitions `<theorem>_statement : Prop` |
| `EncodeFastPathStatements` | Hand statements of the encoder fast path, for an identity with the generated theorem |
| `DecodeAccept` | Decoder accept path |
| `DecodeAccept` + part | A part of a long accept proof (`DecodeAcceptHead`, `DecodeAcceptSource`) |
| `DecodeAcceptFunctionSpec` | The function specification of a callee decoder and its proof |
| `DecodeRejectSize`, `DecodeRejectOffset`, `DecodeRejectAlignment`, `DecodeRejectOverflow` | Decoder, one reject path |
| `DecodeErrorUnreachable` | Decoder, an error wrap that the accept path skips |
| `DecodeLoop`, `DecodeLoop` + qualifier, `DecodeLoopLemmas` | Decoder, a loop of the accept path |
| `DecodeFieldSegments` | Decoder, the field segments of the accept path |
| `DecodeSpec`, `DecodeSpecAccept`, `DecodeSpecReject` | Decoder, connection to EthLib (one module, or split by path) |
| `EncodeFastPath` | Encoder, path with no slice growth |
| `EncodeGrowFirstSite`, `EncodeGrowSecondSite` | Encoder, growth at the first or second append site only |
| `EncodeGrowOneSite`, `EncodeGrowAnySite` | Encoder, growth at any one site, or at any site |
| `EncodeRejectLength` | Encoder, the length rejects |
| `EncodeSpec`, `EncodeSpec` + path | Encoder, connection to EthLib |
| `Encode` + part | Encoder, a part of a long proof (`EncodeHead`, `EncodeTail`, `EncodeCover`, `EncodeLoop`) |
| `DecodeThenEncode`, `DecodeThenEncode` + qualifier | Decode then encode: round trip and composition |
| `FunctionSpecsAsNestedField` | Function specifications for a caller that holds the type as a nested field |
| `<Role>Instances`, `<Role>KindInstances` | Instances of a general lemma or kind for the type |
| `GeneratedDecodeAccept` | Generator output: the decoder step chain, accept and size reject theorems |
| `GeneratedEncodeFastPath` | Generator output: the encoder fast-path theorem |
| `GeneratedEncodeFastPathSpec` | The generated fast path against the hand `Desc` (`../gen/flat-types/flat_types_encode_spec.py`) |
| `GeneratedEncodeFastPathSameAsHand` | Hand identity of the generated fast-path theorem with a hand statement |
| `Uint64DecoderKindSameAsHand` | Hand identity of the `uint64` decoder kind with a hand theorem |
| `Witness` + module | A witness of a theorem of that module (section 6) |
| `WitnessBumpAllocator` | A bump allocator model for the witnesses of the type, with its `.S` file in the type directory |

A plain qualifier after a role narrows it, for example `EncodeGrowAnySiteThreeCases` or `DecodeSpecRejectErrorWordNonzero`.
If no role fits, the module name uses plain words that say what the module holds.
A module that holds several roles has the name of its main role.
`../README.md` section 7 tells which modules a tool writes.

The main theorems inside `Prysm.<GoTypeName>` have these names:

- decoder: `Decode.accept`, `Decode.reject_size`, `Decode.reject_offset`, `Decode.accept_spec`,
  `Decode.reject_size_spec`, `Decode.reject_offset_spec`, `Decode.reject_complete`;
- a suffix in words states an added premise, for example `Decode.reject_alignment_error_word_nonzero`;
- encoder: `Encode.fast_path`, `Encode.grow_first_site`, `Encode.grow_second_site`, `Encode.grow_one_site`,
  `Encode.grow_any_site`, `Encode.reject_length`, `Encode.reject_too_big`, `Encode.fast_path_spec`,
  `Encode.grow_first_site_spec`, `Encode.grow_one_site_spec`;
- `SizeSSZ`: `Size.result`, `Size.result_spec`; decode then encode: `DecodeThenEncode.round_trip`;
- the statement of a theorem is the `def` or `abbrev` with the name of the theorem + `_statement`;
- program constants: `Code.unmarshalSSZ`, `Code.marshalSSZTo`, `Code.sizeSSZ`, `Code.marshalSSZ`;
  descriptions: `desc`, `checkerDesc`;
- a function specification of a method: `Decode.accept_function_spec` or `Encode.fast_path_function_spec`.
  The lemma that it holds has the suffix `_holds`;
- a witness module has the namespace `Prysm.<GoTypeName>.Witness.<Module>`, for example `Witness.GeneratedDecodeAccept`.
  Its main theorem is `runs`, with a plain qualifier for the case (`runs_empty`, `runs_one_element`, `runs_maximum`).

The generators write the names `Decode.generated_*` and `Encode.generated_*` (`../gen/README.md`).
Examples are `Decode.generated_accept`, `Decode.generated_reject` and `Encode.generated_fast`.
Each generated theorem `t` has a theorem `t_kind`.
`../gen/flat-types/flat_types_encode_spec.py` writes `Encode.generated_fast_spec`.
