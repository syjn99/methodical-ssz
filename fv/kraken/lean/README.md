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
A hand test type is a small type with a hand `Desc`, its Go value and its encoding.
It has no ELF.
`Spec/TestCheckpointAndAttestationData.lean` holds reduced forms of the Prysm `Checkpoint` and `AttestationData`, without the protobuf fields.
The `Desc` checker `../gen/desc-checker/DescChecker.lean` imports the test types for its tests.
The `Spec.lean` modules of the Prysm types import them for their lemmas.
`Codec/ReadUint64List.lean` and `Prysm/DataColumnsByRootIdentifier/SpecDefinitions.lean` also import them.
`Spec` imports only EthLib and `Spec`.
It holds no machine code.
The reduced `Checkpoint` and `AttestationData` of `Spec/TestCheckpointAndAttestationData.lean` are its only forms of Prysm types.
The hand `Desc` of each type of the Prysm target is in `Prysm/<GoTypeName>/` (section 5).

**`Machine`.** Helpers on the Kraken machine model.
They are the one-instruction step lemmas and tactics (`Machine/Step.lean`), and the stack frame, byte, label and flag lemmas.
It also has the commands that read code and data files (`Machine/Include.lean`).
It has the witness host builder and tactics (`Machine/WitnessHost.lean`, `Machine/WitnessSplit.lean`, `Machine/SepPerm.lean`).
It holds no runtime contract and no Prysm type.

**`Runtime`.** The contracts of the Go runtime callees (`Runtime/Contracts.lean`, `Runtime/NewobjectContract.lean`) and their models.
A model is a small assembly program (`Runtime/*.S`) with theorems that it satisfies its contract.
Examples are a bump allocator, a memory copy and error formatting.
A runtime model that reads ELF data of the link set is in `Prysm/RuntimeModel/`.
`Runtime` does not import `Prysm`.

**`Codec`.** Lemmas and statement kinds with the size, the count, the registers or the frame as parameters.
Examples are the `uint64` decoder pattern (`Codec/Uint64Decoder.lean`) and the fixed-bytes field patterns (`Codec/FixedBytesDecode*.lean`).
Others are the encoder step lemmas (`Codec/Encode*.lean`) and the stack guard lemma (`Codec/StackGuard.lean`).
`Codec/Kind/` holds the statement kinds of the generated proofs (`../gen/README.md` section 4).
The whole accept kind is in `Codec/Kind/DecodeAcceptAnyFrame.lean` and the encoder fast-path kind in `Codec/Kind/EncodeFastPathAnyFrame.lean`.
Their field list is in `Codec/Kind/ContainerField.lean`.
The lemmas of the kinds are in `Codec/`.
`Codec/Segment/` holds segment and loop lemmas for any frame, size or element count.
Many `Codec` comments name the type whose code gave a template.
Some `Codec` modules have one user type, for example `Codec/Segment/SizeReject.lean` (Deposit).
A work unit keeps a new lemma in its type directory (`../../AGENTS.md`).

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

The types of the accept rows of `../gen/generator/types.tsv` have generated modules `Prysm/<GoTypeName>/Generated*.lean`.
Section 8 tells which of them a generator writes.
A type directory with only `Code.lean` holds a type that the generator refuses.

### Dependencies

The import lines of the tree give these relations:

```text
EthLib -> Spec -> Machine -> Runtime
Codec <-> Prysm (at module level, both directions)
```

- `Spec` imports only EthLib and `Spec`.
  `Machine` imports only Kraken, Std, Lean and `Machine`.
  (`Machine/Include.lean` and `Machine/SepPerm.lean` have `public meta import Lean` for their elaborators.)
  `Runtime` imports only Kraken, `Machine` and `Runtime`.
  So these three libraries import only libraries to their left, and Lean itself.
- `Codec` and `Prysm` import each other at module level.
  Some `Codec` modules import a `Prysm` module, and many `Prysm` modules import a `Codec` module.
  Lean forbids a cycle of modules, so the module graph has no cycle.
  Only the libraries have no order.
- A `Codec` module that imports `Prysm` uses code, data or specification lemmas of a type in a general lemma or kind.
  `grep -rlE '^public import Prysm' lean/Codec` gives these modules, with the `Prysm` directories that they import:
  - `Codec/CalleeDecode.lean` (ValidatorIndex, Epoch, Slot): it uses their decoder specifications;
  - `Codec/Segment/Bytes32VectorSpec.lean` (HistoricalBatch): it uses the element lemmas of `Prysm/HistoricalBatch/Spec.lean`;
  - `Codec/SerializeFieldsCongruence.lean` (AttestationData);
  - `Codec/DecodeRejectSizeAnyFrame.lean`, `Codec/FixedBytesDecode.lean`, `Codec/Kind/DecodeAcceptAnyFrame.lean`, `Codec/Kind/DecodeRejectAnyFrame.lean`,
    `Codec/Segment/Bytes32LoopProof.lean`, `Codec/Segment/SizeReject.lean` and `Codec/Uint64RejectSize.lean` (ElfData): they use data addresses of the link set.
- A module of one type directory imports a module of another type directory for one of these reasons:
  - A callee decoder: the code calls the decoder of another type.
    The module imports the `Code` module of the callee and the module of its `Decode.accept_function_spec_holds`.
    Examples are the generated decoders that call Slot, Epoch or ValidatorIndex, and AttestationData, which calls Checkpoint.
  - A nested type: the type holds another type as a field.
    The module imports the modules of the field type, for example Deposit and `Prysm/Deposit_Data/`.
  - The shared `Spec` of a nested type: the outer `Spec` module uses the `SszValue` lemmas of the field type.
    An example is `Prysm/IndexedAttestation/Spec.lean`, which uses `Prysm.AttestationData.SszValue`.
  - A module imports only the modules whose names it uses.
    It does not import a module of another type for the imports of that module.
    A lemma that two types share and that names no single type is in `Codec/` or `Spec/`.
- A type directory also imports the two directories of `Prysm/` that are not types: `Prysm/ElfData/` and `Prysm/RuntimeModel/`.

### Module system

Each file of the libraries is a Lean module, with this header:

```lean
module

public import Machine.Step

@[expose] public section
```

- `@[expose]` makes the definition bodies visible to importing files.
  The witnesses unfold `Code` definitions.
- A proof body is not public data.
  Thus a change of a proof body does not rebuild the importing modules.
- Kraken does not expose all definition bodies.
  A file that unfolds `sep` or `List.At` adds `import all Kraken.Separation` and `import all Kraken.Mem`.
- `Spec/TestBitVec.lean` and `Spec/TestBitList.lean` are not modules.
  Their `decide +kernel` proofs need core `UInt8` bodies.
- Each generator writes this header.

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
Its conclusion keeps `rsp + 8`, `r14` and the frame `F`.
Some contracts also keep `rbp`, and section 4.1 says which.
The forms are in `Runtime/Contracts.lean` and `Runtime/NewobjectContract.lean` (runtime functions).

A hand-written callee, for example `(*primitives.Epoch).UnmarshalSSZ`, gets a function specification of the same form.
Examples are `Prysm.Epoch.Decode.accept_function_spec` and `Prysm.Slot.Decode.accept_function_spec`.
`Codec.Uint64CalleeAccept` is the common form of the four `uint64` accept specifications.
The Checkpoint callee has `Prysm.Checkpoint.Decode.accept_function_spec` and `Prysm.Checkpoint.Encode.fast_path_function_spec`.
A theorem about the callee code (`*_holds`) proves the specification.
An example is `Prysm.Checkpoint.Encode.fast_path_function_spec_holds`.
Thus a function specification is not a trust item, and section 4.1 does not list it.

A contract is a hypothesis because no proof covers the compiled Go runtime.
The proof uses the contract at each call site and continues from any state that satisfies its conclusion.
If the conclusion decides a branch (for example `rax ≠ 0`), the proof follows that branch.
Otherwise the proof covers both branches.
A contract can be contradictory.
Its form is not evidence.
Only a runtime model that satisfies it and a witness show that it can hold.
The contracts assume that no garbage collection runs during the call, and that allocation succeeds.

### 4.1 Table of the runtime contracts

The table has one row for each runtime contract of the tree.
`grep -n '^def.*Contract' Runtime/*.lean` lists the definitions.
Every contract has these parts, and the table does not repeat them:

- Premise: the 8-byte return address `ret` at `rsp`, and `S` scratch bytes below `rsp`.
- Premise: the frame `F`, separate from all other fragments.
- Conclusion: every run from the label reaches `ret`, with `rsp + 8` and `r14` kept.
- Conclusion: the return address and `F` are unchanged.
  The scratch bytes and the spill area, if any, hold other bytes of the same length.
- The conclusion does not state the other registers or the flags.

The columns give this information:

- Parameters: the arguments of the Lean definition.
- Precondition and postcondition: the premises and the conclusion of the definition, in addition to the common parts.
  `Heap avail` is the runtime heap with `avail` free bytes.
  A primed register, for example `rcx'`, is the register at the return.
- Left open: what the definition does not fix.
- Source: the Go source that the module text names, and the row of `../gen/checks/runtime_diff.py`.
  The Go file names are files of the Go source tree, not of this repository.
  `runtime_diff.py` compares these sources between Go 1.26.3 and Go 1.26.10.
- Model: the `.S` file and the theorem that shows that the model satisfies the contract.
  A model shows that the contract can hold.
  It is not a refinement of the Go code.
  The models use the bump heap `Runtime.bumpHeap` of `Runtime/BumpAllocator.lean`.
  The witnesses are the type directories whose witness modules use the model theorem.
  `grep -lw <theorem> Prysm/*/Witness*.lean` lists these modules.
  The match in `WitnessBumpAllocator.lean` is the definition of a model, not a use.
- Open limits: the titles of the entries of `../FINDINGS.md`.
  The entry "The runtime contracts are not proved on the compiled runtime" applies to each row.
  The table does not repeat it.

| Contract and module | Go label | Parameters | Precondition | Postcondition | Left open | Source | Model and witnesses | Open limits |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| `Runtime.MakesliceContract` in `Runtime/Contracts.lean` | `runtime.makeslice` | `Heap`: the heap predicate. `ty`: the address of the element type descriptor. `esz`: the element size. `S`: the scratch size. | `rax` is `ty`. `rbx ≤ cnt` and `rcx = cnt`, with `cnt < 2^63`. `esz * cnt ≤ avail` and `esz * cnt ≤ maxAlloc`. `Runtime.maxAlloc` is 2^48. A 24-byte spill area at `rsp + 8`. `Heap avail`. | `rbp` kept. A zero block of `esz * cnt` bytes at `rax'`. `Heap (avail - esz * cnt)`. | The value of `rax'`. The connection of `ty` to `esz`. | The docstring names Go 1.26.3 runtime/slice.go. The docstring of `Runtime.maxAlloc` names runtime/malloc.go. The `runtime_diff.py` row "MakesliceContract (esz 1)" names the Go functions makeslice and mallocgc. | `Runtime/BumpMakeslice8.S` with `Runtime.bump_makeslice` (esz 8). No witness module uses it. `Runtime/BumpMakeslice1.S` with `Runtime.bump_makeslice1` (esz 1). Witnesses: AttestationData, BeaconBlockHeader, BlobIdentifier, BuilderDepositRequest, Checkpoint, DepositMessage, DepositRequest, Deposit_Data, Eth1Data. Witnesses: HistoricalSummary, PartialDataColumnGroupID, PendingDeposit, PowBlock, SigningData, SyncAggregate, SyncCommitteeMessage, ValidatorIdentity. The models below select the size by the type word in `rax`. `Prysm/RuntimeModel/BumpMakesliceByteSliceDispatch.S` with `Prysm.RuntimeModel.bump_makeslice_byte_slice_dispatch_size1` and `Prysm.RuntimeModel.bump_makeslice_byte_slice_dispatch_size24`. Witnesses of both: Deposit, HistoricalBatch, SyncCommittee. `Prysm/RuntimeModel/BumpMakesliceUint64Dispatch.S` with `Prysm.RuntimeModel.bump_makeslice_uint64_dispatch_size1` (witnesses: IndexedAttestation, SingleAttestation). The same file with `Prysm.RuntimeModel.bump_makeslice_uint64_dispatch_size8` (witness: IndexedAttestation). `Prysm/RuntimeModel/BumpMakesliceUint64DispatchForDataColumnsByRootIdentifier.S` with `Prysm.RuntimeModel.bump_makeslice_uint64_dispatch_for_data_columns_by_root_identifier_size1`. The same file with `Prysm.RuntimeModel.bump_makeslice_uint64_dispatch_for_data_columns_by_root_identifier_size8`. Witness of both: DataColumnsByRootIdentifier. | "The allocation type argument is not connected to the size". "Two bump allocator models differ only in a label". |
| `Runtime.NewobjectContract` in `Runtime/NewobjectContract.lean` | `runtime.newobject` | `Heap`, `ty` and `S` as in `Runtime.MakesliceContract`. `sz`: the object size. | `rax` is `ty`. `sz ≤ avail`. An 8-byte spill area at `rsp + 8`. `Heap avail`. | `rbp` kept. A zero block of `sz` bytes at `rax'`. `Heap (avail - sz)`. | The value of `rax'`. The connection of `ty` to `sz`. The contract has no upper bound on `sz`, for example `Runtime.maxAlloc`. | The module text names no Go source file and no Go version. The `runtime_diff.py` row "NewobjectContract" names the Go functions newobject and mallocgc of runtime/malloc.go. | `Runtime/BumpNewobject16.S`, `Runtime/BumpNewobject24.S` and `Runtime/BumpNewobject32.S`. Their theorems are `Runtime.bump_newobject16`, `Runtime.bump_newobject24` and `Runtime.bump_newobject32`. No witness module uses them. `Prysm/AttestationData/BumpNewobject72.S` with `Prysm.AttestationData.bump_newobject72`. Witness: AttestationData. `Prysm/Deposit/BumpNewobject120.S` with `Prysm.Deposit.bump_newobject120`. Witness: Deposit. `Prysm/RuntimeModel/BumpNewobjectStructDispatch.S` selects the size by the type word in `rax`. Its theorems are `Prysm.RuntimeModel.bump_newobject_struct_dispatch_size72` and `Prysm.RuntimeModel.bump_newobject_struct_dispatch_size96`. Witnesses of both: IndexedAttestation, SingleAttestation. | "The allocation type argument is not connected to the size". |
| `Runtime.GrowsliceContract` in `Runtime/Contracts.lean` | `runtime.growslice` | `Heap` and `S` as in `Runtime.MakesliceContract`. `ty`: the address of the element type descriptor. `esz`: the element size. | `0 < esz`. `rax` is the old pointer, `rbx` the new length, `rcx` the old capacity. `rdi` is the count of new elements, and `rsi` is `ty`. `rdi ≤ rbx` and `rbx - rdi ≤ rcx < rbx`. `nc` is `nextSliceCap rbx rcx` (`Runtime.nextSliceCap`). `2 * (esz * nc) + 8192 ≤ avail ≤ maxAlloc`. The `esz * (rbx - rdi)` old bytes at `rax`. A 40-byte spill area at `rsp + 8`. `Heap avail`. | `rbp` kept, and `rbx'` is `rbx`. `nc ≤ rcx'` and `esz * rcx' ≤ 2 * (esz * nc) + 8192`. A block of `esz * rcx'` bytes at `rax'` that starts with the old bytes. The old bytes stay at `rax`. `Heap avail'` with `avail' + esz * rcx' ≤ avail`. | The bytes after the old bytes in the new block. The value of `rcx'` inside its bounds. A lower bound on `avail'`. | The docstring names Go 1.26.3 runtime/slice.go and the size rule of roundupsize. The docstring of `Runtime.nextSliceCap` names Go 1.26.3 nextslicecap. The `runtime_diff.py` row "GrowsliceContract (esz 1)" names growslice, nextslicecap, mallocgc and roundupsize. | `Runtime/MemmoveGrowsliceModel.S` with `Runtime.model_growslice`, for `esz = 1` only. Witnesses: Checkpoint, CommitteeIndex, DataColumnsByRootIdentifier, Epoch, Slot, ValidatorIndex. | "Growslice contract gives no lower bound on the remaining heap". "Paths that the proofs do not cover". |
| `Runtime.MemmoveContract` in `Runtime/Contracts.lean` | `runtime.memmove` | `S`: the scratch size. | `rax` is the destination, `rbx` the source, and `rcx` is the length `n`. The `n` source bytes at `rbx` and `n` destination bytes at `rax`. The two blocks and `F` are separate. No spill area and no heap. | `rbp` kept. The destination holds the source bytes. The source bytes are unchanged. | Overlapping source and destination: the contract has no case for them. | The docstring names memmove_amd64.s and its zero-byte frame, with no Go version. The `runtime_diff.py` row "MemmoveContract" compares the full file runtime/memmove_amd64.s. | `Runtime/MemmoveGrowsliceModel.S` with `Runtime.model_memmove`, for each `S`. Witnesses: AttestationData, BeaconBlockHeader, BlobIdentifier, BuilderDepositRequest, Checkpoint, DataColumnsByRootIdentifier, Deposit, DepositMessage, DepositRequest, Deposit_Data, Eth1Data. Witnesses: HistoricalBatch, HistoricalSummary, IndexedAttestation, PartialDataColumnGroupID, PendingDeposit, PowBlock, SigningData, SingleAttestation, SyncAggregate. Witnesses: SyncCommittee, SyncCommitteeMessage, ValidatorIdentity. | Only the common entry. |
| `Runtime.ConvT64Contract` in `Runtime/Contracts.lean` | `runtime.convT64` | `Heap` and `S` as in `Runtime.MakesliceContract`. | `rax` is the value `v`. `8 ≤ avail`. An 8-byte spill area at `rsp + 8`. `StaticBox v` (`Runtime.StaticBox`): the static table entry of `v`, empty if `v ≥ 256`. `Heap avail`. | `rax'` is a box address `bx` with `BoxIn bx v hb` (`Runtime.BoxIn`). In the first case, `v < 256`, `hb` is empty and `bx` is the static entry of `v`. In the second case, `hb` holds the 8 bytes of `v`. The bytes `hb` are at `bx`. `StaticBox v` is unchanged. `Heap avail'` with `avail' + hb.length ≤ avail ≤ avail' + 8`. | Which of the two cases occurs. The conclusion does not keep `rbp`. | The docstring names Go 1.26.3 runtime/iface.go. The `runtime_diff.py` row "ConvT64Contract" names the Go functions convT64 and mallocgc. | `Runtime/ErrorfConvT64Model.S` with `Runtime.model_convT64`, the second case only. Witnesses: CommitteeIndex, Epoch, IndexedAttestation, Slot, ValidatorIndex. | Only the common entry. |
| `Runtime.FmtErrorfNilContract` in `Runtime/Contracts.lean` | `fmt.errorf`, the internal function of the public `fmt.Errorf` | `S`: the scratch size. | `rax` points to the format bytes `fs`, and `rbx` is their length. `rdi = 0`: the call has no arguments. `fs` has no byte 0x25 (`%`). A 40-byte spill area at `rsp + 8`. No heap. | `rax' = 0`. The format bytes are unchanged. | The conclusion does not keep `rbp`. Any heap of the caller is part of `F`, so the call does not change it. | The docstring names Go 1.26.3 fmt/errors.go. The `runtime_diff.py` row of `fmt.errorf` compares fmt/errors.go, fmt/print.go, fmt/format.go and errors/errors.go. The label of that row does not name this contract. | `Runtime/ErrorfConvT64Model.S` with `Runtime.model_errorf_nil`. No witness module uses it. No theorem in `Codec` or `Prysm` has this contract as a premise. | Only the common entry. |
| `Runtime.FmtErrorfWrapContract` in `Runtime/Contracts.lean` | `fmt.errorf` with one argument | `Heap` and `S` as in `Runtime.MakesliceContract`. `fs`: the format bytes. `RO`: a read-only resource of the caller. `MsgIn`: a predicate that the caller fixes. | `rax` points to `fs`, and `rbx` is its length. `rdi = 1` and `rsi = 1`: one argument. At `rcx`: the 8-byte type word `ity`, then the data word `e`. `ity` is also at the label `go_itab._errors.errorString_error` plus 8. `ErrObj e sp msg` (`Runtime.ErrObj`), the bytes `hm` at `sp`, `RO`, and `MsgIn sp msg hm`. `fs.length + msg.length + 8192 ≤ avail`. A 40-byte spill area at `rsp + 8`. `Heap avail`. | `rax' ≠ 0`. Every premise fragment is unchanged, except the heap, the scratch bytes and the spill area. `Heap avail'` with `avail' ≤ avail`. | The error value: only `rax' ≠ 0`. The conclusion gives no memory of the new error. The conclusion does not keep `rbp`. The verbs in `fs`: the contract reads only its length. | The docstring of `Runtime.FmtErrorfNilContract` names Go 1.26.3 fmt/errors.go for `fmt.errorf`. The `runtime_diff.py` row of `fmt.errorf` names this contract. | `Runtime/ErrorfConvT64Model.S` with `Runtime.model_errorf_wrap`. No witness module uses it. No theorem in `Codec` or `Prysm` has this contract as a premise. | "The content of a format string is not checked". |
| `Runtime.FmtErrorfDecimalWrapContract` in `Runtime/Contracts.lean` | `fmt.errorf` with two arguments, a number and an error | `Heap`, `fs` and `S` as in `Runtime.FmtErrorfWrapContract`. `tw`: the type word of the number argument. | `rax` and `rbx` as in `Runtime.FmtErrorfWrapContract`. `rdi = 2` and `rsi = 2`: two arguments. At `rcx`: `tw`, the box `bx`, the type word `ity`, then the data word `e`. `BoxIn bx v hb`, `StaticBox v` and the bytes `hb` at `bx`. `ity` at the label `go_itab._errors.errorString_error` plus 8. `ErrStr e sp msg` (`Runtime.ErrStr`). `fs.length + 20 + msg.length + 8192 ≤ avail`. A 40-byte spill area at `rsp + 8`. `Heap avail`. | As in `Runtime.FmtErrorfWrapContract`. | As in `Runtime.FmtErrorfWrapContract`. The contract does not fix `tw`. | The docstring of `Runtime.FmtErrorfNilContract` names Go 1.26.3 fmt/errors.go for `fmt.errorf`. The label of the `runtime_diff.py` row of `fmt.errorf` does not name this contract. | `Runtime/ErrorfConvT64Model.S` with `Runtime.model_errorf_decimal_wrap`. Witness: IndexedAttestation. | "The content of a format string is not checked". |
| `Runtime.FmtErrorfDecimalDecimalContract` in `Runtime/Contracts.lean` | `fmt.errorf` with two number arguments | `Heap`, `fs` and `S` as in `Runtime.FmtErrorfWrapContract`. `tw`: the type word of each number argument. | `rax` and `rbx` as in `Runtime.FmtErrorfWrapContract`. `rdi = 2` and `rsi = 2`: two arguments. At `rcx`: `tw`, the box `bx1`, `tw`, then the box `bx2`. `BoxIn bx1 v1 hb1` and `BoxIn bx2 v2 hb2`. `StaticBox v1`, `StaticBox v2`, the bytes `hb1` at `bx1` and `hb2` at `bx2`. `fs.length + 40 + 8192 ≤ avail`. A 40-byte spill area at `rsp + 8`. `Heap avail`. | As in `Runtime.FmtErrorfWrapContract`. | As in `Runtime.FmtErrorfWrapContract`. The contract does not fix `tw`. | The docstring of `Runtime.FmtErrorfNilContract` names Go 1.26.3 fmt/errors.go for `fmt.errorf`. The `runtime_diff.py` row of `fmt.errorf` names this contract. | `Runtime/ErrorfConvT64Model.S` with `Runtime.model_errorf_decimal_decimal`. Witnesses: CommitteeIndex, Epoch, Slot, ValidatorIndex. | "The content of a format string is not checked". |

## 5. The specification side

A Prysm type has a hand `Desc`.
It also has a checker `Desc` when the `Desc` checker accepted a producer file for it.

- The hand `Desc` `Prysm.<GoTypeName>.desc` is written by hand from the consensus-specs definition.
  For some types it is written from the Prysm proto definition: `grep -l 'from the Prysm proto' Prysm/*/SpecDescription.lean` lists them.
  Such a `Desc` has the same source as the `Desc` producer, so it is not an independent specification (`../FINDINGS.md`).
  The hand `Desc` does not use the checker `Desc`.
  For every type, the hand `Desc` is in `Prysm/<GoTypeName>/SpecDescription.lean`.
  That module holds only `desc` and the definitions that only the description needs.
  It imports EthLib, and the `SpecDescription` module of a nested type.
  `grep -lE '^def desc' lean/Prysm/*/*.lean` lists the modules.
  Example: `Prysm.Checkpoint.desc` in `Prysm/Checkpoint/SpecDescription.lean`.
- The value side is in `Spec.lean`: `SszValue`, `toValue`, the `enc` function and the bridge lemmas.
  A `Statements` module that uses these definitions imports `Spec.lean`.
  DataColumnsByRootIdentifier is the exception: its `Spec.lean` imports `StatementsEncode.lean`.
  So its value definitions are in `SpecDefinitions.lean`.
  The statements import it, and `Spec.lean` gets it through `StatementsEncode.lean`.
  Deposit is the other exception: its value definitions are in `StatementsSpec.lean`, with its spec statements.
- The checker `Desc` `Prysm.<GoTypeName>.checkerDesc` is in `SpecChecker.lean`.
  `../gen/checks/desc_to_lean.py` writes it from a file of `../prysm/go1.26.10/evidence/`.
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
To close the memory premise from the split block `H`, use `sep_perm H` (`Machine/SepPerm.lean`).
Do not sort the chunks with `simp only [Std.ExtHashMap.sep_comm, Std.ExtHashMap.sep_comm_l]`, because it is very slow.
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
- A changed statement replaces the earlier statement in the same commit (`../../README.md` section 5).
  The commit message and the PR give the reason for the change.
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
- After a failed build, run `lake build --no-build` before you trust any `.olean`.

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
| `Layout` | Go struct layout of Checkpoint from the IR: offsets and sizes (`../gen/checks/layout.py`) |
| `DecodeLayout` | Hand decoder frame layout `decodeLayout` that a kind tie gives to `Codec.decodeAcceptKindAnyFrame`, and the address lemmas of that tie (Checkpoint) |
| `EncodeLayout` | Hand encoder frame layout `encodeLayout` that `Codec.encodeFastPathKindAnyFrame` reads. The `encoder --fast-path` row of the type in `../gen/generator/types.tsv` gives it to the generator with `--hand-layout` |
| `GoValue`, `GoValueWitness` | Validity of the Go value of the receiver, and its witness |
| `Spec` | The `SszValue` structure, its definitions and its bridge lemmas to EthLib (section 5) |
| `SpecDescription` | The hand `Desc` and the definitions that only the description needs (section 5) |
| `SpecDefinitions` | The value definitions of DataColumnsByRootIdentifier that its statements use (section 5) |
| `SpecChecker` | The checker `Desc` (`../gen/checks/desc_to_lean.py`) |
| `SpecEquivalence` | Codec equality of the hand `Desc` and the checker `Desc` |
| `SpecDecodeBridge` | Decoder-side lemmas of the specification bridge |
| `Statements`, `Statements` + qualifier | Statement definitions `<theorem>_statement : Prop` |
| `EncodeFastPathStatements` | Hand statement of the encoder fast path, for a statement tie with the generated theorem |
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
| `Size` | `SizeSSZ`: the machine theorem and its connection to EthLib |
| `Marshal` | `MarshalSSZ`: the machine theorem and its connection to EthLib |
| `Encode` + part | Encoder, a part of a long proof (`EncodeHead`, `EncodeTail`, `EncodeCover`, `EncodeLoop`) |
| `DecodeThenEncode`, `DecodeThenEncode` + qualifier | Decode then encode: round trip and composition |
| `FunctionSpecsAsNestedField` | Function specifications for a caller that holds the type as a nested field |
| `<Role>KindTie` | A tie of a kind to the hand theorem of module `<Role>` (`../gen/README.md` section 4) |
| `<Role>StatementTie` | A tie of a generated theorem to the hand statement of the path `<Role>` (`EncodeFastPathStatementTie`) |
| `GeneratedDecodeAccept` | Generator output: the decoder step chain, accept and size reject theorems |
| `GeneratedEncodeFastPath` | Generator output: the encoder fast-path theorem |
| `GeneratedEncodeFastPathSpec` | The generated fast path against the hand `Desc` (`../gen/flat-types/flat_types_encode_spec.py`) |
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
- `SizeSSZ`: `Size.result`, `Size.result_spec`; `MarshalSSZ`: `Marshal.result`, `Marshal.result_spec`;
- decode then encode: `DecodeThenEncode.round_trip`;
- the statement of a theorem is the `def` or `abbrev` with the name of the theorem + `_statement`;
- program constants: `Code.unmarshalSSZ`, `Code.marshalSSZTo`, `Code.sizeSSZ`, declared as `def Code.<method>` inside `namespace Prysm.<GoTypeName>`;
  label abbreviations: `Code.unmarshalSSZLabel`, `Code.marshalSSZToLabel`;
  descriptions: `desc`, `checkerDesc`;
- a tie: the name of the hand theorem + `_kind_tie` (a kind) or `_statement_tie` (a generated theorem),
  for example `Decode.accept_kind_tie` and `Encode.fast_path_statement_tie`;
- a function specification of a method: `Decode.accept_function_spec` or `Encode.fast_path_function_spec`.
  The lemma that it holds has the suffix `_holds`;
- a witness module has the namespace `Prysm.<GoTypeName>.Witness.<Module>`, for example `Witness.GeneratedDecodeAccept`.
  Its main theorem is `runs`, with a plain qualifier for the case (`runs_empty`, `runs_one_element`, `runs_maximum`).

The generators write the names `Decode.generated_*` and `Encode.generated_*` (`../gen/README.md`).
Examples are `Decode.generated_accept`, `Decode.generated_reject` and `Encode.generated_fast`.
Each generated theorem `t` has a theorem `t_kind`.
`../gen/flat-types/flat_types_encode_spec.py` writes `Encode.generated_fast_spec`.
The generator writes the tie `Encode.generated_fast_statement_tie` of Checkpoint (`../gen/README.md` section 4).
