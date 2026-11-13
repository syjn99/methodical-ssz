# lean: specifications, contracts and machine-code proofs

This is the Lake project of the proofs. The libraries are in `lakefile.toml`.
The toolchain is in `lean-toolchain`. Kraken and EthLib are Lake dependencies at pinned commits.
The design principles are in `../../README.md`. The build commands are in `../README.md` section 5.

## 1. Libraries

The libraries `Spec`, `Machine`, `Runtime` and `Codec` are the shared layer.
The library `Prysm` holds the proofs of the Prysm types (one directory for each type).
`../gen/restructure/maps/shared-layer/files.tsv` gives the earlier path and a one-line meaning of each module that this map moved.
A module that a later step added or split is not in a `files.tsv`.

**`Spec`.** EthLib specifications that several types share, and the ones that the `Desc` checker imports (`../gen/desc-checker/`).
They are the specifications of the small test types (`Spec/Test*.lean`) and of two reduced Prysm types (`Spec/TestCheckpointAndAttestationData.lean`).
They import only EthLib and each other. `Spec/DeserializeOfSerialize.lean` holds a general lemma: if `serialize` of every Go value gives `enc g`, then every input that EthLib accepts is `enc g` of one value.
So a machine proof only has to say what the code does on `enc g`, and that the code rejects every other input.

**`Machine`.** Helpers on the Kraken machine model: the one-instruction step lemmas and tactics (`Machine/Step.lean`), the stack frame, byte, label and flag lemmas.
It also has the commands that read code and data files (`Machine/Include.lean`) and the witness host builder and tactics (`Machine/WitnessHost.lean`, `Machine/WitnessSplit.lean`).

**`Runtime`.** The contracts of the Go runtime callees (`Runtime/Contracts.lean`) and their models.
A model is a small assembly program (`Runtime/*.S`) with theorems that it satisfies its contract. Examples are a bump allocator, a memory copy and error formatting.

**`Codec`.** Lemmas that do not depend on one Prysm type: the `uint64` decoder pattern (`Codec/Uint64Decoder.lean`), the fixed-bytes field decoder and encoder patterns (`Codec/Bytes32*.lean`, `Codec/FixedBytesDecode*.lean`), the encoder step lemmas (`Codec/Encode*.lean`) and the statement kinds of the generated proofs (`Codec/Kind/`).
`Codec/Segment/` holds segment and loop lemmas stated once for any size or element count, with the fixed instances of `Prysm/SyncAggregate/`, `Prysm/SyncCommittee/` and `Prysm/HistoricalBatch/` as corollaries.

**`Prysm`.** One directory for each Prysm type, `Prysm/<GoTypeName>/<Role>.lean`, namespace `Prysm.<GoTypeName>`.
The full name of a main theorem is the name of the work, for example `Prysm.Checkpoint.Decode.reject_size`.
The files `files.tsv` of `../gen/restructure/maps/checkpoint-and-epoch/` and `../gen/restructure/maps/attestation-data/` give the earlier path and a one-line meaning of each module that these maps moved.
- `Prysm/Checkpoint/`: the `v1alpha1.Checkpoint` decoder, encoder and `SizeSSZ`, the hand specification (`Spec.lean`),
  the Go value predicate (`GoValue.lean`) and the decoder-then-encoder composition (`DecodeThenEncode.lean`).
  The files `CapacityReserved*.lean` hold proofs about a separate test ELF of a generator option that is not adopted
  (the encoder reserves 40 bytes of capacity first; namespace `Prysm.Checkpoint.CapacityReserved`).
- `Prysm/Epoch/`: the decoder of the hand-written `primitives.Epoch` method and its function specification.
  Its program constant is `Prysm.Epoch.Code.unmarshalSSZ` (`Prysm/Epoch/Code.lean`).
- `Prysm/AttestationData/`: the `v1alpha1.AttestationData` decoder (accept path in four parts, size reject, EthLib
  alignment), its hand specification and witnesses. The Slot and CommitteeIndex
  decoders of its link set are in `Prysm/Slot/Code.lean` and `Prysm/CommitteeIndex/Code.lean`.
- `Prysm/Slot/` and `Prysm/CommitteeIndex/`: the decoders of the hand-written `primitives.Slot` and
  `primitives.CommitteeIndex` methods and their function specifications.
- `Prysm/Checkpoint/*AsNestedField.lean`: the function specifications of the Checkpoint decoder and encoder for a
  caller that holds Checkpoint as a nested field (AttestationData), and their checks on the Checkpoint witness hosts.
- `Prysm/SyncAggregate/`, `Prysm/SyncCommittee/`, `Prysm/IndexedAttestation/`: the decoders of these types.
  They have byte vectors, a vector of byte vectors and a variable-size list.
  `../gen/restructure/maps/sync-and-indexed-attestation/files.tsv` gives the earlier path of each module that this map moved.
- `Prysm/HistoricalBatch/`: the `v1alpha1.HistoricalBatch` decoder.
- `Prysm/Deposit/`: the `v1alpha1.Deposit` decoder, proved with the lemmas of `Codec/Segment/`, and its witnesses.
  `../gen/restructure/maps/historical-batch-and-deposit/files.tsv` gives the earlier path of each module of the two types that this map moved.
- `Prysm/DataColumnsByRootIdentifier/`: the `v1alpha1.DataColumnsByRootIdentifier` encoder (fast path, growth at the
  first site and at any one site, two rejects), the decoder, and their composition at the machine level.
  `../gen/restructure/maps/data-columns-by-root-identifier/files.tsv` gives the earlier path of each module that this map moved.
- `Prysm/RuntimeModel/`: witness-only models of runtime functions that read ELF data of a link set
  (bump allocators that dispatch on a type word). The library `Runtime` does not import `Prysm`.
- `Prysm/ElfData/`: the ELF data of the link set `../prysm/go1.26.10/link-set` (`PrysmTarget.lean`, namespace
  `ElfData.PrysmTarget`) and the command `prysm_data_include` that reads it (`PrysmTargetReader.lean`).
  The root `ElfData` keeps the order of the constant names that some `simp` proofs depend on (see `../gen/restructure/README.md`).
  A data name is the id of its data file, and the id names the ELF item: `sszErrSize` is the address of the global
  `ssz.ErrSize`, `typeUint8` the type descriptor of `uint8`, `formatSlot` the format string `Slot: %w`.
  `../link/data.py` (`item_id`) gives the rule; a type descriptor gets its id in the item table of its link script.
  The lemmas `<id>_addr_eq` restate an address. `../prysm/go1.26.10/link-set/data-ids-old-new.tsv` gives the earlier ids.

The flat fixed-size types (a flat type has only fixed-size fields and no nested container) have their directories in
`Prysm/` too, for example `Prysm/BeaconBlockHeader/` and `Prysm/DepositRequest/`. The generated files are
`Prysm/<GoTypeName>/Generated*.lean`. They use the patterns and kinds of `Codec`.
`../gen/restructure/maps/flat-types/files.tsv` gives the earlier path of each module that this map moved.
The statement kinds of the composed and whole accept theorems, of the callee calls and of the encoder fast path are in
`Codec/Kind/` (`DecodeAccept*.lean`, `CalleeDecode.lean`, `EncodeFastPathAnyFrame.lean`); some of these modules import modules of single types.

### Dependencies

The import lines of the tree give these relations:

```text
EthLib -> Spec -> Machine -> Runtime
Codec <-> Prysm (at module level, both directions)
```

- `Spec` imports only EthLib and `Spec`. `Machine` imports only Kraken, Std and `Machine`. `Runtime` imports only
  Kraken, `Machine` and `Runtime`. So these three libraries import only libraries to their left.
- `Codec` and `Prysm` import each other at module level. 25 of the 60 `Codec` modules import a `Prysm` module:
  13 of 36 in `Codec/`, 2 of 11 in `Codec/Kind/`, 10 of 13 in `Codec/Segment/`. 211 of the 673 `Prysm` modules
  import a `Codec` module. Lean forbids a cycle of modules, so the module graph has no cycle; only the
  libraries have no order.
- The `Codec` modules that import `Prysm` hold lemmas and kinds that the shared layer took from a type
  (for example `Codec/Bytes32Decode.lean` reads the ELF data of `Prysm/ElfData/PrysmTarget.lean`), and instances
  that tie a general lemma to the lemmas of a type (`Codec/Segment/*Instances.lean`).
- `Prysm/Checkpoint/CapacityReserved*.lean` and `Prysm/Deposit/` import modules of the flat types, and `Prysm/HistoricalBatch/` does not import them.
A new type gets its own directory `Prysm/<GoTypeName>/`. Do not change a reviewed module to add a new type.

## 2. How machine code enters Lean

1. `../link/convert_objdump.py` converts the disassembly of one function into a labeled `.S` file.
2. `include_x64_code "<path>.S"` (`Machine/Include.lean`) parses the file with the Kraken parser when Lean elaborates it. The result is a `Program` constant, for example `Prysm.SyncAggregate.Code.unmarshalSSZ`.
3. A data file holds the bytes or the address of one ELF data item, for example a format string or a type descriptor.
   `data_include <id>` (`Machine/Include.lean`) and its copy `prysm_data_include` for the Prysm link set define `<id> : List UInt8` and `<id>_addr : BitVec 64`. No byte or offset is written by hand.
4. `../link/check.py` compares the `.S` files and the data files with the ELF.

The `.S` and data files are not Lean imports. So `lakefile.toml` declares their directories as `input_dir` entries in the `needs` of each library.
Lake then puts the file contents into the input hash, and a changed file makes Lake build the proofs again.
The directory that `Prysm/Checkpoint/CapacityReservedCode.lean` includes is not declared. A change there does not cause a rebuild (see `../FINDINGS.md`).
When you add a code directory, add it as an `input_dir` of the library. A `lakefile.toml` change needs user approval.

## 3. Shape of a main theorem

The statement is a `def` of type `Prop`, committed before its proof. The theorem then has that type.
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

A specification theorem extends a machine theorem. For example, `Prysm.SyncAggregate.Decode.reject_size_spec_statement` adds the premise `rcx = bs.size` and the conclusion that EthLib `deserialize` returns an error.
An accept theorem adds the contract hypotheses (for example `MakesliceContract`, `MemmoveContract`), the heap budget `Heap avail`, the receiver fragments and a stack window `S` for the callees.

## 4. Contracts and function specifications

A contract describes a callee at its label, for every machine state, return address and frame `F`.
It gives the argument registers, the stack window of `S` scratch bytes below the return slot, and the spill slots that the callee can write.
It also gives the heap budget and the conclusion: the result, the kept registers `rsp + 8`, `r14`, `rbp`, and an unchanged `F`.
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
Examples are `Prysm.Epoch.Decode.accept_function_spec` and `Prysm.Slot.Decode.accept_function_spec`. A theorem about the callee code (`*_holds`) proves the specification.

A contract is a hypothesis because no proof covers the compiled Go runtime.
The proof uses the contract at each call site and continues from any state that satisfies its conclusion.
If the conclusion decides a branch (for example `rax ≠ 0`), the proof follows that branch. Otherwise the proof covers both branches.
A contract can be contradictory. Its form is not evidence. Only a runtime model that satisfies it and a witness show that it can hold.
The contracts assume that no garbage collection runs during the call, and that allocation succeeds.

## 5. The specification side

Each Prysm type has two `Desc` terms.

- The hand `Desc` is written from the consensus-specs definition, before the checker `Desc` is printed. Example: `Prysm.Checkpoint.desc` in `Prysm/Checkpoint/Spec.lean`.
- The checker `Desc` comes from the generator IR through the checker in `../gen/desc-checker/`. `../gen/checks/desc_to_lean.py` renders it as Lean. Example: `Prysm/Checkpoint/SpecChecker.lean`.
- Codec equality theorems show that both give the same `serialize` and `deserialize`. Example: `Prysm.Checkpoint.desc_serialize_checker` in `Prysm/Checkpoint/SpecEquivalence.lean`.

The theorems use the hand `Desc`. For a Prysm type, the checker only compares the IR with the inventory. It does not compare with the specification.
A structure such as `Prysm.Checkpoint.SszValue` holds the SSZ content of a Go value. `toValue` maps it to an EthLib value, and an `enc` function such as `Prysm.Checkpoint.SszValue.encode` gives its bytes.
Fields without an SSZ value (the protobuf fields `state`, `unknownFields`, `sizeCache`) stay as unchanged memory in the machine theorems.

The connection to EthLib has three theorem forms:

- accept: if EthLib accepts the input as `v`, there is a Go value `g` with `toValue g = v`, and the machine code writes `g` to the receiver (`Decode.accept_spec`).
- reject: if the input is not accepted, EthLib returns an error, and the machine code returns the Go error (`Decode.reject_<cause>_spec`).
- reject completeness: every input that EthLib rejects falls in a proved reject path (`Decode.reject_complete`).

## 6. Witnesses

A witness file (`Prysm/<GoTypeName>/Witness*.lean`, namespace `Prysm.<GoTypeName>.Witness.<Role>`) builds one concrete `Host` with `Machine.Witness.mkHost` (`Machine/WitnessHost.lean`).
The program is the data labels, the real converted function and the runtime models.
A theorem `runs` (or `runs_<case>`) applies the main theorem to a concrete memory block and discharges every premise.
The runtime models discharge the contract hypotheses. Example: `Prysm.SyncAggregate.Witness.DecodeAccept.runs`.
For a variable length, the witnesses cover the empty value, one element and the maximum.
The receiver in a witness must be a Go value of the type. `Prysm/Checkpoint/GoValue.lean` gives a Lean predicate for this check.
Use one witness host for each file. Two `Host` instances in one file make instance resolution choose the wrong host.

## 7. Proof conventions

- Do not use `sorry`, `admit`, a new `axiom`, `native_decide` or `bv_decide`.
- Do not change a committed statement. Add a new statement with a new name and a reason.
- Keep `maxHeartbeats` and `maxRecDepth` at the default. If a proof needs more, profile the declaration first.
  Then write the measured cause in words in a comment above the `set_option` line. `Prysm/IndexedAttestation/DecodeAccept.lean` has an example.
- Many files have limit options without such a comment. Do not copy them as a model for new work.
- Use `Machine.cmp_be_false` or `Codec.lea_cmp_be_false` for the stack guard branch. A `simp` and `omega` proof of that branch can use too much kernel memory.
- Split a long straight-line proof into segments over the fragments that each segment touches, then compose them.
- A scratch result is closed only when `#print axioms` of every theorem that it uses has no `sorryAx` and does not list the theorem itself.
- Build one heavy job at a time. After a failed build, run `lake build --no-build` before you trust any `.olean`.

## 8. Names

Module, namespace and main theorem names use the full Go type name (`../gen/restructure/SPEC.md`).
The structure `Prysm.<GoTypeName>.SszValue` holds the SSZ content of a type.
Earlier short names and labels remain only in the places below, each for the reason given.

- External identities, written as their source writes them:
  - ELF symbols, the labels of the `.S` files that come from the ELF (`../prysm/go1.26.10/link-set/norm/`), and the
    code constants and labels that `include_x64_code` takes from them;
  - Go names: the type, field, function and package names of Prysm and of the test target `../target/` (for example
    `ListC`, a list of containers, and `BitL`, a bit list; `Spec/Test*.lean` writes the type names in full words and
    keeps the Go field names in lower case as structure fields);
  - the build path `fvphase1c/p1cbin` of the `main` package of the pinned Prysm ELF (`../README.md`): the ELF records it;
  - the names of Kraken, Lean, Mathlib and EthLib.
- Records of earlier runs keep the names and paths of their run. These tables give the present name of each earlier one:
  - `../gen/path-names.tsv`: earlier paths of tools, tests, directories and case files;
  - `<case file>.ids.tsv`, next to each negative case file `negative-cases-*.json`: earlier ids of the negative cases;
  - `../gen/generator/decoder-test-case-ids.tsv` and `../gen/generator/encoder-test-case-ids.tsv`: earlier ids of the
    cases of the generator tests;
  - `../gen/generator/option-names.tsv`: earlier generator modes, options and header labels;
  - `../prysm/go1.26.10/evidence/flat-types/runs/record-names.tsv`: earlier record file names of the generator runs on
    the 24 flat types, and the names that a new run writes;
  - `../prysm/go1.26.10/link-set/data-ids-old-new.tsv`: earlier data ids of the Prysm link set;
  - `../gen/desc/spec-names-old-new.tsv`: earlier names of the `Spec` test-type declarations, which the records of the
    `Desc` checker name;
  - the maps of `../gen/restructure/maps/` (`names.tsv`, `files.tsv`): the module and declaration names before and
    after each rename step (`../gen/restructure/README.md` section 4).
- Schema ids: `fvphase1c.*` (for example `fvphase1c.inventory/1`, `fvphase1c.desc/1`) and `fvpar.include-api/1`. They are
  format identifiers that the tools write and that records and checks compare, so they are kept.
- The forwarder `../gen/e2e/axioms_gate.py`: the CI workflow names this earlier path (`../gen/README.md` section 6).
- Standard short words: `dec` and `enc` (decode, encode), `u64` (uint64), and lemma names of the form instruction +
  constant + fact (`Machine.and7_zero`, `Machine.zx8`, `Machine.jg16_false`).
