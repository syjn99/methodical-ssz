# lean: specifications, contracts and machine-code proofs

This is the Lake project of the proofs. The libraries are in `lakefile.toml`.
The toolchain is in `lean-toolchain`. Kraken and EthLib are Lake dependencies at pinned commits.
The design principles are in `../../README.md`. The build commands are in `../README.md` section 5.

## 1. Libraries

The libraries `Spec`, `Machine`, `Runtime`, `TestTarget` and `Codec` are the shared layer.
The other libraries hold the proofs of Prysm types (one library or a group of modules for each type).
`../gen/restructure/maps/shared-layer/files.tsv` gives the earlier path of each shared module and a one-line meaning.

**`Spec`.** EthLib specifications that several types share, and the ones that the `Desc` checker imports (`../gen/desccheck/`).
They are the specifications of the small test types (`Spec/Test*.lean`) and of two reduced Prysm types (`Spec/ReducedPrysm.lean`).
They import only EthLib and each other. `Spec/DeserializeOfSerialize.lean` holds a general lemma: if `serialize` of every Go value gives `enc g`, then every input that EthLib accepts is `enc g` of one value.
So a machine proof only has to say what the code does on `enc g`, and that the code rejects every other input.

**`Machine`.** Helpers on the Kraken machine model: the one-instruction step lemmas and tactics (`Machine/Step.lean`), the stack frame, byte, label and flag lemmas.
It also has the commands that read code and data files (`Machine/Include.lean`) and the witness host builder and tactics (`Machine/WitnessHost.lean`, `Machine/WitnessSplit.lean`).

**`Runtime`.** The contracts of the Go runtime callees (`Runtime/Contracts.lean`) and their models.
A model is a small assembly program (`Runtime/*.S`) with theorems that it satisfies its contract. Examples are a bump allocator, a memory copy and error formatting.

**`TestTarget`.** Code, data and proofs of the small test target (Go 1.26.3, `../link/out/`), for example `TestTarget/ScalarsDecodeAccept.lean` and `TestTarget/ListU64DecodeReject.lean`.
It also has the function specifications of the test target callees (`TestTarget/FunctionSpecs.lean`) and the contract form `NewobjectC`.
Some Prysm proofs use a few of its declarations (for example `TestTarget.Data.staticuint64s_addr`, `store_avx_step`, `TestTarget.luElems`).

**`Codec`.** Lemmas that do not depend on one Prysm type: the `uint64` decoder pattern (`Codec/Uint64Decoder.lean`), the fixed-bytes field decoder and encoder patterns (`Codec/Bytes32*.lean`, `Codec/FixedBytesDecode*.lean`), the encoder step lemmas (`Codec/Encode*.lean`) and the statement kinds of the generated proofs (`Codec/Kind/`).
`Codec/Segment/` holds segment and loop lemmas stated once for any size or element count, with the fixed instances of `E2eList` and `E2eHb` as corollaries.

**`Prysm`.** One directory for each Prysm type, `Prysm/<GoTypeName>/<Role>.lean`, namespace `Prysm.<GoTypeName>`.
The full name of a main theorem is the name of the work, for example `Prysm.Checkpoint.Decode.reject_size`.
`../gen/restructure/maps/checkpoint-and-epoch/files.tsv` gives the earlier path of each module and a one-line meaning.
- `Prysm/Checkpoint/`: the `v1alpha1.Checkpoint` decoder, encoder and `SizeSSZ`, the hand specification (`Spec.lean`),
  the Go value predicate (`GoValue.lean`) and the decoder-then-encoder composition (`DecodeThenEncode.lean`).
  The files `CapacityReserved*.lean` hold proofs about a separate test ELF of a generator option that is not adopted
  (the encoder reserves 40 bytes of capacity first; namespace `Prysm.Checkpoint.CapacityReserved`).
- `Prysm/Epoch/`: the decoder of the hand-written `primitives.Epoch` method and its function specification.
  Its program constant is in `Prysm/Checkpoint/Code.lean` (shared module, declared as `Prysm.Epoch.Code.unmarshalSSZ`).
- `Prysm/ElfData/`: the ELF data of a link set and the command that reads it, namespace `ElfData.<SetName>`.
  The root `ElfData` keeps the order of the constant names that some `simp` proofs depend on (see `../gen/restructure/README.md`).

**`E2eAd`.** The `v1alpha1.AttestationData` decoder and the decoders of the hand-written `primitives.Slot` and `primitives.CommitteeIndex` methods.

**`E2eScal`.** Generated and hand proofs for the flat fixed-size types. A flat type has only fixed-size fields and no nested container.
The generated files are `Gen*.lean`. They use the patterns and kinds of `Codec`.
The statement kinds of the composed accept theorems, of the callee calls and of the encoder fast path are still here (`KindAccept*.lean`, `KindCall.lean`, `KindEncN.lean`): their modules import modules of single types (see `../gen/README.md`).

**`E2eList`.** The decoders of `v1alpha1.SyncAggregate`, `v1alpha1.SyncCommittee` and `v1alpha1.IndexedAttestation`.
These types have byte vectors, a vector of byte vectors and a variable-size list.

**`E2eHb`.** The `v1alpha1.HistoricalBatch` decoder.

**`E2eDep` and `E2eDepW`.** The `v1alpha1.Deposit` decoder, proved with the lemmas of `Codec/Segment/`, and its witnesses.

**`E2eEnc` and `E2eDec`.** The `v1alpha1.DataColumnsByRootIdentifier` encoder and decoder, and their composition at the machine level.

### Dependencies

The import graph has this order:

```text
EthLib -> Spec -> Machine -> Runtime -> TestTarget -> Codec (except Codec/Segment/)
       -> Prysm -> E2eAd -> E2eScal -> E2eList -> E2eHb -> Codec/Segment/ -> E2eDep -> E2eDepW
                                     E2eList -> E2eEnc -> E2eDec
```

The arrows give the order of the libraries in the import graph. A library imports only libraries to its left.
Exceptions: `Machine/Step.lean` imports `TestTarget/Code.lean`, `Runtime/Contracts.lean` imports `TestTarget/Data.lean`,
`Runtime/BumpAllocatorVariants.lean` imports `TestTarget/FunctionSpecs.lean`, and `Codec/Bytes32Decode.lean` imports `Prysm/ElfData/CheckpointAndEpoch.lean`.
`Prysm/Checkpoint/CapacityReserved*.lean` import `E2eScal`, and `E2eHb` does not import `E2eScal`.
A new type gets its own library or modules. Do not change a reviewed module to add a new type.

## 2. How machine code enters Lean

1. `../link/conv.py` converts the disassembly of one function into a labeled `.S` file.
2. `include_x64_rt "<path>.S"` (`Machine/Include.lean`) parses the file with the Kraken parser when Lean elaborates it. The result is a `Program` constant, for example `E2eList.Code.SaUnmarshal`.
3. A data file holds the bytes or the address of one ELF data item, for example a format string or a type descriptor.
   `data_include <id>` (`Machine/Include.lean`) and its copies for other directories define `<id> : List UInt8` and `<id>_addr : BitVec 64`. No byte or offset is written by hand.
4. `../link/check.py` compares the `.S` files and the data files with the ELF.

The `.S` and data files are not Lean imports. So `lakefile.toml` declares their directories as `input_dir` entries in the `needs` of each library.
Lake then puts the file contents into the input hash, and a changed file makes Lake build the proofs again.
Some directories that `E2eScal` and `Prysm/Checkpoint/CapacityReservedCode.lean` include are not declared. A change there does not cause a rebuild (see `../FINDINGS.md`).
When you add a code directory, add it as an `input_dir` of the library. A `lakefile.toml` change needs user approval.

## 3. Shape of a main theorem

The statement is a `def` of type `Prop`, committed before its proof. The theorem then has that type.
This example is the size reject of the SyncAggregate decoder (`E2eList/StmtSa.lean`).
Its proof is `E2eList.sa_e2e_reject_size_main` in `E2eList/SaReject.lean`.

```lean
def sa_reject_size_stmt : Prop :=
  ∀ (k : Nat) (hk : SaUnmarshal.IsInfixAt Host.prog k) (hf : LabelsFresh SaUnmarshal k)
    (s : MachineData) (ra guard e0 e1 : UInt64) (fp s2 : List UInt8) (hfp : fp.length = 8) (h2 : s2.length = 8)
    (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At ElfData.CheckpointAndEpoch.e2eErrSize_addr)
      ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrSize" + 8).toBitVec) ⋆ R)
    (hguard : guard.toNat < s.regs.rsp.toNat) (hlen : s.regs.rcx ≠ 160),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = e0 ∧ st.data.regs.rbx = e1
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14
        ∧ (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At ElfData.CheckpointAndEpoch.e2eErrSize_addr)
          ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrSize" + 8).toBitVec) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩
```

Line by line:

- `hk`: the converted function sits at index `k` of the host program. `hf`: no label of the function occurs before it in the program.
- `s` is the machine state at entry. `ra` is the return address, `guard` is the stack limit of the goroutine, and `e0`, `e1` are the two words of the error value `ssz.ErrSize`.
- `fp` and `s2` are the old bytes of the slot of the saved `rbp` and of one register spill slot. Only their length is given.
- `R` is the frame: all other memory of the caller, the receiver and the input included.
- `h_mem` gives the memory as separate fragments (`⋆`). They are the return address at `rsp`, the two stack slots, the guard word at `r14 + 16`, the error value and `R`.
  The address of the error value comes from the data include. It is not a hand number.
- `hguard`: the guard is below `rsp`, so the stack growth branch is not taken.
- `hlen`: the input length (register `rcx` in the Go register ABI) is not 160.
- The conclusion says that every execution from the entry reaches a state with these properties.
  The program counter is `ra`, and `rax`, `rbx` hold the error words.
  `rsp` is entry `rsp + 8`, and `rbp` and `r14` are unchanged.
- The final memory names every fragment of the premise again. Only the two stack slots changed. `R` is unchanged, and there is no `⋆ True`.

A specification theorem extends a machine theorem. For example, `sa_reject_size_spec_stmt` adds the premise `rcx = bs.size` and the conclusion that EthLib `deserialize` returns an error.
An accept theorem adds the contract hypotheses (for example `MakesliceC`, `MemmoveC`), the heap budget `Heap avail`, the receiver fragments and a stack window `S` for the callees.

## 4. Contracts and function specifications

A contract describes a callee at its label, for every machine state, return address and frame `F`.
It gives the argument registers, the stack window of `S` scratch bytes below the return slot, and the spill slots that the callee can write.
It also gives the heap budget and the conclusion: the result, the kept registers `rsp + 8`, `r14`, `rbp`, and an unchanged `F`.
The forms are in `Runtime/Contracts.lean` (runtime functions) and `TestTarget/FunctionSpecs.lean` (generated callees).

| Contract | Callee |
| --- | --- |
| `MakesliceC` | `runtime.makeslice`: a zero block of `esz · cnt` bytes from the heap |
| `NewobjectC` | `runtime.newobject`: a zero block of `sz` bytes |
| `GrowsliceC` | `runtime.growslice`: a new block that holds the old bytes |
| `MemmoveC` | `runtime.memmove`: copy between disjoint ranges only |
| `ConvT64C` | `runtime.convT64`: an 8-byte box, or an entry of the static table for values below 256 |
| `FmtErrorfNilC`, `FmtErrorfWC`, `FmtErrorfDWC`, `FmtErrorfDDC` | `fmt.Errorf` with no argument, `%w`, `%d %w` and `%d %d` |

A hand-written callee, for example `(*primitives.Epoch).UnmarshalSSZ`, gets a function specification of the same form.
Examples are `Prysm.Epoch.Decode.accept_function_spec` and `E2eAd.SlUAccC`. A theorem about the callee code (`*_holds`) proves the specification.

A contract is a hypothesis because no proof covers the compiled Go runtime.
The proof uses the contract at each call site and continues from any state that satisfies its conclusion.
If the conclusion decides a branch (for example `rax ≠ 0`), the proof follows that branch. Otherwise the proof covers both branches.
A contract can be contradictory. Its form is not evidence. Only a runtime model that satisfies it and a witness show that it can hold.
The contracts assume that no garbage collection runs during the call, and that allocation succeeds.

## 5. The specification side

Each Prysm type has two `Desc` terms.

- The hand `Desc` is written from the consensus-specs definition, before the checker `Desc` is printed. Example: `Prysm.Checkpoint.desc` in `Prysm/Checkpoint/Spec.lean`.
- The checker `Desc` comes from the generator IR through the checker in `../gen/desccheck/`. `../gen/e2e/descterm.py` renders it as Lean. Example: `Prysm/Checkpoint/SpecChecker.lean`.
- Codec equality theorems show that both give the same `serialize` and `deserialize`. Example: `Prysm.Checkpoint.desc_serialize_checker` in `Prysm/Checkpoint/SpecEquivalence.lean`.

The theorems use the hand `Desc`. For a Prysm type, the checker only compares the IR with the inventory. It does not compare with the specification.
A structure such as `Prysm.Checkpoint.SszValue` holds the SSZ content of a Go value. `toValue` maps it to an EthLib value, and an `enc` function such as `Prysm.Checkpoint.SszValue.encode` gives its bytes.
Fields without an SSZ value (the protobuf fields `state`, `unknownFields`, `sizeCache`) stay as unchanged memory in the machine theorems.

The connection to EthLib has three theorem forms:

- accept: if EthLib accepts the input as `v`, there is a Go value `g` with `toValue g = v`, and the machine code writes `g` to the receiver (`*_accept_spec_k`).
- reject: if the input is not accepted, EthLib returns an error, and the machine code returns the Go error (`*_reject_*_spec`).
- reject completeness: every input that EthLib rejects falls in a proved reject path (`*_reject_complete`).

## 6. Witnesses

A witness file (`Wit*.lean`) builds one concrete `Host` with `Machine.Witness.mkHost` (`Machine/WitnessHost.lean`).
The program is the data labels, the real converted function and the runtime models.
A theorem `*_runs` applies the main theorem to a concrete memory block and discharges every premise.
The runtime models discharge the contract hypotheses. Example: `E2eList.WitSaA.sa_accept_runs`.
For a variable length, the witnesses cover the empty value, one element and the maximum.
The receiver in a witness must be a Go value of the type. `Prysm/Checkpoint/GoValue.lean` gives a Lean predicate for this check.
Use one witness host for each file. Two `Host` instances in one file make instance resolution choose the wrong host.

## 7. Proof conventions

- Do not use `sorry`, `admit`, a new `axiom`, `native_decide` or `bv_decide`.
- Do not change a committed statement. Add a new statement with a new name and a reason.
- Keep `maxHeartbeats` and `maxRecDepth` at the default. If a proof needs more, profile the declaration first.
  Then write the measured cause in words in a comment above the `set_option` line. `E2eList/IaAccept.lean` has an example.
- Many files have limit options without such a comment. Do not copy them as a model for new work.
- Use `Machine.cmp_be_false` or `Codec.lea_cmp_be_false` for the stack guard branch. A `simp` and `omega` proof of that branch can use too much kernel memory.
- Split a long straight-line proof into segments over the fragments that each segment touches, then compose them.
- A scratch result is closed only when `#print axioms` of every theorem that it uses has no `sorryAx` and does not list the theorem itself.
- Build one heavy job at a time. After a failed build, run `lake build --no-build` before you trust any `.olean`.

## 8. Names

The current file and theorem names use short abbreviations of the Go types.
A structure `P<abbreviation>` holds the SSZ content of the type, for example `Prysm.Checkpoint.SszValue`.
Some abbreviations have two or three meanings. The namespace decides the meaning.

| Abbreviation | Go type |
| --- | --- |
| `Cp` | `v1alpha1.Checkpoint` |
| `Ad` | `v1alpha1.AttestationData` |
| `Bh` | `v1alpha1.BeaconBlockHeader` |
| `E1` | `v1alpha1.Eth1Data` |
| `Bi` | `v1alpha1.BlobIdentifier` |
| `Dm` | `v1alpha1.DepositMessage` |
| `Dd` | `v1alpha1.Deposit_Data` |
| `Dep` | `v1alpha1.Deposit` |
| `Pw` | `v1alpha1.PendingPartialWithdrawal` |
| `Sm` | `v1alpha1.SyncCommitteeMessage` |
| `Pc` | `v1alpha1.PendingConsolidation` |
| `Pd` | `v1alpha1.PendingDeposit` |
| `Pb` | `v1alpha1.PowBlock` |
| `Hs` | `v1alpha1.HistoricalSummary` |
| `Hb` | `v1alpha1.HistoricalBatch` |
| `Sd` | `v1alpha1.SigningData` |
| `Vb` | `v1alpha1.ValidatorBalance` |
| `Ve` | `v1alpha1.VoluntaryExit` |
| `Ia` | `v1alpha1.IndexedAttestation` |
| `Dc`, `dcd` | `v1alpha1.DataColumnsByRootIdentifier` (encoder `Dc`, decoder `dcd`) |
| `Dpr`, `Bdr` | `engine_v1.DepositRequest`, `engine_v1.BuilderDepositRequest` |
| `Bbr`, `Bsr`, `Epr` | `v1alpha1.BeaconBlocksByRangeRequest`, `BlobSidecarsByRangeRequest`, `ExecutionPayloadEnvelopesByRangeRequest` |
| `Pdc`, `Vid`, `Bpf` | `v1alpha1.PartialDataColumnGroupID`, `ValidatorIdentity`, `BuilderPreferences` |
| `Ep`, `Sl`, `Ci`, `Vi` | `primitives.Epoch`, `Slot`, `CommitteeIndex`, `ValidatorIndex` (hand-written methods) |
| `Lu`, `Lc`, `Bl`, `Bv` | test types `ListU64`, `ListC`, `BitL`, `BitVec` in `../target/` |
| `Sc` | three meanings: `v1alpha1.SyncCommitteeMessage` in `E2eScal` encoder names such as `Gen6ScEnc`, `v1alpha1.SyncCommittee` in `E2eList`, and the test type `Scalars` in `TestTarget` |
| `Sa` | two meanings: `v1alpha1.SyncAggregatorSelectionData` in `E2eScal`, and `v1alpha1.SyncAggregate` in `E2eList` |
| `Fv` | the test type `FixedVec` in `TestTarget` declaration names |
| `epr` | two meanings: `ExecutionPayloadEnvelopesByRangeRequest`, and the Epoch reject witness `Prysm.Epoch.Witness.DecodeRejectSize.runs` |
| `pad` | the encoder `padEnc` of `E2e.PAd` (AttestationData, in `E2eAd/Spec.lean`). The generator scripts use `Pad` for `v1alpha1.PayloadAttestationData` |
