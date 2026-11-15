# lean: specifications, contracts and machine-code proofs

This is the Lake project of the proofs. The libraries are in `lakefile.toml`.
The toolchain is in `lean-toolchain`. Kraken and EthLib are Lake dependencies at pinned commits.
The design principles are in `../../README.md`. The build commands are in `../README.md` section 5.

## 1. Libraries

The libraries `Spec`, `Machine`, `Runtime` and `Codec` are the shared layer.
The library `Prysm` holds the proofs of the Prysm types (one directory for each type).

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
- `Prysm/Checkpoint/`: the `v1alpha1.Checkpoint` decoder, encoder and `SizeSSZ`, the hand specification (`Spec.lean`),
  the Go value predicate (`GoValue.lean`) and the decoder-then-encoder composition (`DecodeThenEncode.lean`).
- `Prysm/Epoch/`: the decoder of the hand-written `primitives.Epoch` method, its function specification and its EthLib alignment (`DecodeSpec.lean`).
  Its program constant is `Prysm.Epoch.Code.unmarshalSSZ` (`Prysm/Epoch/Code.lean`).
  The directory also has the encoder fast path (`EncodeFastPath.lean`, `EncodeSpec.lean`) and `SizeSSZ` (`Size.lean`).
  Their program constants are in `EncodeCode.lean` and `SizeCode.lean`, so that the importers of `Code.lean` do not build again.
  `EncodeGrowFirstSite.lean` has the encoder growslice path.
  `EncodeCoverFramed.lean` joins the two encoder paths for every capacity, with the exact frame.
  `Marshal.lean` has `MarshalSSZ` with the growslice contract and its EthLib link; its witness is `WitnessMarshal.lean`.
  Its program constant is in `MarshalCode.lean`.
- `Prysm/AttestationData/`: the `v1alpha1.AttestationData` decoder (accept path in four parts, size reject, EthLib
  alignment), `SizeSSZ` (`Size.lean`), its hand specification and witnesses. The Slot and CommitteeIndex
  decoders of its link set are in `Prysm/Slot/Code.lean` and `Prysm/CommitteeIndex/Code.lean`.
- `Prysm/Slot/` and `Prysm/CommitteeIndex/`: the decoders of the hand-written `primitives.Slot` and
  `primitives.CommitteeIndex` methods and their function specifications.
  Both directories have the encoder fast path and `SizeSSZ` in files with the names of `Prysm/Epoch/`.
  They also have the encoder growslice path and the framed cover in files with these names.
  They also have `MarshalSSZ` in `Marshal.lean`, `MarshalCode.lean` and `WitnessMarshal.lean`.
  `Prysm/ValidatorIndex/` has the encoder fast path, the growslice path and the framed cover in such files.
  `Prysm/CommitteeIndex/Spec.lean` holds its description `.uint 8`.
  `Prysm/Slot/DecodeSpec.lean` and `Prysm/ValidatorIndex/DecodeSpec.lean` align the Slot and ValidatorIndex decoders with EthLib.
- `Prysm/Checkpoint/*AsNestedField.lean`: the function specifications of the Checkpoint decoder and encoder for a
  caller that holds Checkpoint as a nested field (AttestationData), and their checks on the Checkpoint witness hosts.
- `Prysm/SyncAggregate/`, `Prysm/SyncCommittee/`, `Prysm/IndexedAttestation/`: the decoders of these types.
  They have byte vectors, a vector of byte vectors and a variable-size list.
- `Prysm/HistoricalBatch/`: the `v1alpha1.HistoricalBatch` decoder.
- `Prysm/Deposit/`: the `v1alpha1.Deposit` decoder, proved with the lemmas of `Codec/Segment/`, and its witnesses.
- `Prysm/DataColumnsByRootIdentifier/`: the `v1alpha1.DataColumnsByRootIdentifier` encoder (fast path, growth at the
  first site and at any one site, two rejects), the decoder, and their composition at the machine level.
- `Prysm/RuntimeModel/`: witness-only models of runtime functions that read ELF data of a link set
  (bump allocators that dispatch on a type word). The library `Runtime` does not import `Prysm`.
- `Prysm/ElfData/`: the ELF data of the link set `../prysm/go1.26.10/link-set` (`PrysmTarget.lean`, namespace
  `ElfData.PrysmTarget`) and the command `prysm_data_include` that reads it (`PrysmTargetReader.lean`).
  The data namespace has the root `ElfData`, not `Prysm`, because of the order of names in `simp`.
  `simp` with the commutativity lemmas `Std.ExtHashMap.sep_comm` and `sep_comm_l` orders the parts of a separating
  conjunction by the names of their constants (Lean `Name.cmp`, root component first).
  The root `ElfData` sorts before `HAdd`, `HSub`, `Host`, `Int`, `List` and `Eq`; the root `Prysm` sorts after them.
  Some `simp` proofs depend on that order, so a data name with another root can make them fail. Only a build shows such a failure.
  A data name is the id of its data file, and the id names the ELF item: `sszErrSize` is the address of the global
  `ssz.ErrSize`, `typeUint8` the type descriptor of `uint8`, `formatSlot` the format string `Slot: %w`.
  `../link/data.py` (`item_id`) gives the rule; a type descriptor gets its id in the item table of its link script.
  The lemmas `<id>_addr_eq` restate an address.

The flat fixed-size types (a flat type has only fixed-size fields and no nested container) have their directories in
`Prysm/` too, for example `Prysm/BeaconBlockHeader/` and `Prysm/DepositRequest/`. The generated files are
`Prysm/<GoTypeName>/Generated*.lean`. They use the patterns and kinds of `Codec`.
The statement kinds of the composed and whole accept theorems, of the callee calls and of the encoder fast path are in
`Codec/Kind/` (`DecodeAccept*.lean`, `CalleeDecode.lean`, `EncodeFastPathAnyFrame.lean`); some of these modules import modules of single types.

### Dependencies

The import lines of the tree give these relations:

```text
EthLib -> Spec -> Machine -> Runtime
Codec <-> Prysm (at module level, both directions)
```

- `Spec` imports only EthLib and `Spec`. `Machine` imports only Kraken, Std, Lean and `Machine` (`Machine/Include.lean`
  has `public meta import Lean` for its elaborators). `Runtime` imports only Kraken, `Machine` and `Runtime`. So these
  three libraries import only libraries to their left (and Lean itself).
- `Codec` and `Prysm` import each other at module level. 25 of the 60 `Codec` modules import a `Prysm` module:
  13 of 36 in `Codec/`, 2 of 11 in `Codec/Kind/`, 10 of 13 in `Codec/Segment/`. 214 of the 727 `Prysm` modules
  import a `Codec` module. Lean forbids a cycle of modules, so the module graph has no cycle; only the
  libraries have no order.
- The `Codec` modules that import `Prysm` hold lemmas and kinds that the shared layer took from a type
  (for example `Codec/Bytes32Decode.lean` reads the ELF data of `Prysm/ElfData/PrysmTarget.lean`), and instances
  that tie a general lemma to the lemmas of a type (`Codec/Segment/*Instances.lean`).
- `Prysm/Deposit/` imports modules of a flat type (`Prysm/Deposit_Data/`). `Prysm/HistoricalBatch/` does not import the flat types.
A new type gets its own directory `Prysm/<GoTypeName>/`. Do not change a reviewed module to add a new type.

## 2. How machine code enters Lean

1. `../link/convert_objdump.py` converts the disassembly of one function into a labeled `.S` file.
2. `include_x64_code "<path>.S"` (`Machine/Include.lean`) parses the file with the Kraken parser when Lean elaborates it. The result is a `Program` constant, for example `Prysm.SyncAggregate.Code.unmarshalSSZ`.
3. A data file holds the bytes or the address of one ELF data item, for example a format string or a type descriptor.
   `data_include <id>` (`Machine/Include.lean`) and its copy `prysm_data_include` for the Prysm link set define `<id> : List UInt8` and `<id>_addr : BitVec 64`. No byte or offset is written by hand.
4. `../link/check.py` compares the `.S` files and the data files with the ELF.

The `.S` and data files are not Lean imports. So `lakefile.toml` declares their directories as `input_dir` entries in the `needs` of each library.
Lake then puts the file contents into the input hash, and a changed file makes Lake build the proofs again.
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

Module, namespace and main theorem names use the full Go type name.
The rules are in "Name forms" at the end of this section.
The structure `Prysm.<GoTypeName>.SszValue` holds the SSZ content of a type.
Some short names, labels and earlier names remain in the tree.
The lists below give each one with its reason.
A name with no reason except "record of an earlier run" is marked as a candidate.
The user decides on it.

### Names that an external source gives

These names are written as their source writes them.

- ELF symbols and the labels of the converted `.S` files.
  `../link/convert_objdump.py` takes the file name and the first label from the ELF symbol.
  It drops the module path.
  It writes `_` for a character outside `[A-Za-z0-9_.]`, for example `target_prysm.Checkpoint`.
  A jump target inside a function gets the label `L_<function>_<hex offset>`.
  The `Code` constants of `include_x64_code` and the runtime labels (`runtime.makeslice`, `fmt.errorf`) use these names.
- Go names of Prysm and of the test target `../target/`: type, field, method and package names.
  Examples are `Deposit_Data` (a protobuf name), `ENRForkID`, `ListC` (a list of containers) and `BitL` (a bit list).
  `Spec/Test*.lean` writes the type names in full words, for example `Spec.ListOfContainersValue` for `ListC`.
  It keeps the Go field names in lower case as structure fields.
  The test type `ListU64` (`../target/types.go`) keeps its Go name in `Spec`.
  The names made from it keep it too.
  These are the module `Spec/TestListU64.lean`, the structure `Spec.ListU64` and the lemmas `Spec.listU64Desc*`.
  The lemmas `Spec.listU64Encode`, `Spec.listU64_*`, `Spec.allFit_listU64_inv` and `Spec.serializeEach_listU64` also keep it.
  The checker input `../gen/desc/hand-types-ir.json` and the checker table use the Go names `ListU64`, `ListC` and `BitL`.
  So do `../gen/desc/hand-types-references.json` and the checker result `../gen/desc/results/main.result.json`.
- Data ids that `../link/data.py` (`item_id`) makes from a Go name, for example `formatJ` for the format string `J: %w`.
  `J`, `B` and `L` are Go field names of the test target (`../link/out/data/`).
- The Go compiler flag in the file name `../prysm/go1.26.10/evidence/gcflags-m2.txt` (output of `-gcflags=-m=2`).
- The names of Kraken, Lean, Mathlib and EthLib, and of their declarations.

### Names that a pinned file or a tool needs

- The word `"p1cbin"`.
  `../gen/keepalive.py` writes it into the `main` function of the Prysm target.
  The copy of that file is `../prysm/go1.26.10/prysm-target-main.go.txt`.
  The program prints the word, so the word is a string of the pinned ELF.
  `../prysm/go1.26.10/build-ids.txt` records the sha256 of this `main.go`.
  Each byte of `main.go` goes into the ELF.
  Another word moves the string data, and with it the string addresses that the proofs name.
  The message of commit `6c759123` records a scratch build with another word of the same length.
  In that build, 232 lines in 36 `.S` files of the link set changed.
  A new ELF hash needs user approval (`../../../AGENTS.md`).
- The keys `elf b2 sha256` and `go build id b2` of `../prysm/go1.26.10/build-ids.txt`.
  `b2` is the second build.
  `../gen/prysm-elf.sh` writes these lines after it builds the ELF two times.
  A new line needs a new build.
- The set labels of the inventory `../prysm/inventory.json`.
  The sets are `A`, `B`, `I` and their parts (`A_minus_B`, `B_generated_minus_A`, `I_minus_A`, `I_hand_written`).
  The counts are `set_A`, `set_B`, `set_I` and similar keys.
  Each type has the flags `in_A` and `in_B`.
  These are keys of the inventory format.
  `../gen/type_inventory.py` writes them.
  `../gen/type_list_document.py`, `../gen/type_scope.py` (only `in_B`) and `../prysm/TYPES.md` read or show them.
- Case ids that a test tool makes from the case parameters.
  `../gen/checks/differential.py` writes ids such as `dec-…` and `enc-empty-cap40-…`.
  `../prysm/go1.26.10/evidence/differential.json` records them.
  `../gen/desc/test_desc.py` names its mutants `m-…`, `e1-…` to `e8-…`, `y1-…` to `y10-…` and `z1-…` to `z4-…`.
  It names its scenarios `s-…`.
  The checker result `../gen/desc/results/main.result.json` records these ids in its paths.
  A new id needs a new differential run with Go, or a new checker run with Lean.
- The negative case ids, for example `epoch-decode-accept-code-cmp-0x8-to-0x9`.
  An id is the theorem name, the kind, and the old and the new text of the mutation.
  So it holds register names such as `rax` and hypothesis names such as `hlen` and `hgrow`.
- The review sources `../gen/desc/review/r1_mutants.py`, `r2_mutants.py` and `r3_mutants.py`.
  `r1`, `r2` and `r3` are review labels.
  The docstrings have more review labels and commit ids.
  `../gen/desc/test_desc.py prepare` runs the three files on a copy of the original descriptions.
  It replays their mutants (`r1-…`, `n01-…`, `q01-…`) and the list scenarios `t01` to `t13` of `r3_mutants.py`.
  `r3_mutants.py` writes its forged checker line with the work directory path as given.
  The replay writes the work directories `replay/rmut`, `replay/n` and `replay/r3`.
  The checker result records these paths.
  Some mutants set `reference` to earlier names `Fv1.<xy>Desc`, for example `Fv1.scDesc` for Scalars.
  These names occur in the checker result only inside the texts of these mutants.
  `../FINDINGS.md` ("Replayed review mutants carry earlier reference names") gives the effect on three mutants.
  The docstring labels have no reason of their own.
  They are candidates for plain words.
- The record link table `../prysm/go1.26.10/link/` keeps the data ids of its run, `x5CpElemType` and `x5ErrSize`.
  Its `RESULT` names these data files.
  No theorem includes the table.
  `../FINDINGS.md` ("Link set `prysm/go1.26.10/link` has no tracked disassembly") gives the way to check it again.
  The table is a candidate for deletion.
- The schema ids `fvkraken.ssz-methods/1` and `fvkraken.inventory/2` of `../gen/tools/proof_inventory.py`.
  The schema id `type-scope/1` of `../gen/type_scope.py`.
  The other schema ids have the form `fv.kraken.<name>/<n>`.
  No tool reads these three ids.
  They are candidates for that form.
  A change needs a change of the tool and a new run of it.
- The Lake package name `fvkraken` in `lakefile.toml`.
  `lake-manifest.json` gives the root package the name `k0b`.
  Lake writes the manifest.
  The name `k0b` is a candidate for a fix.
  A Lake change needs user approval (section 2).

### Records that hold earlier names

Each of these files is a record of a run, and it keeps the names of that run.
No tool of the tree reads them, except where the item says so.
`../../AGENTS.md` does not accept "historical material" as a reason.
So each one is a candidate for deletion.

- `../prysm/go1.26.10/evidence/e2e.json` (schema `prysm-e2e.status/1`).
  It names the ELF files `p1bin-amd64` and `p1bin-amd64.nm` and the libraries `E2e` and `E2eAd`.
  It also names paths under `prysm/go1.26.10/e2e/`.
  No tool writes it or reads it.
- `../prysm/go1.26.10/evidence/axioms-gate.json`.
  Its header names the libraries `E2e`, `E2eAd` and `E2eScal`.
  `../gen/tools/proof_inventory.py` states that it does not read this record.
- `../prysm/go1.26.10/evidence/negative/result.json`.
  `../gen/checks/negative.py` writes such a file.
  It has 154 case ids, for example `ep-control` and `cpa-cmp41`.
  None of them is one of the 239 ids of `../gen/checks/negative-cases-checkpoint-and-attestation-data.json`.
  Its mutant diffs name `ElfData.CheckpointAndEpoch.e2e*` and `MakesliceC`.
  It has absolute container paths.
  `../../../AGENTS.md` does not allow absolute container paths in committed files.
  A new run on the present case list drops every old id.
- `../prysm/go1.26.10/evidence/generator-cases/AXIOMS.txt`.
  Nine of its 22 names are not declarations of the tree, for example `Codec.u64dec_accept` and `Codec.rootdec_seg`.
- The frozen lists `../gen/frozen/THEOREMS.json` and `ASSUMPTIONS.json`, and the text in `../gen/frozen/build_lists.py`.
  `build_lists.py` writes the lists.
  `../gen/frozen/test_frozen.py` compares them with the tracked files.
  No other tool reads them.
  They name test-target theorems that are not in the tree.
  Examples are `sc_accept_main`, `lu_accept_main` and `vbv_accept_main`.
  They also hold work labels such as `P2`, `fix3`, `OUTBOX` and `phase1c-r1 S1`.
  They also hold the obligation id `compose_hupd`.
  `ASSUMPTIONS.json` has a hand edit (`../gen/README.md` section 8).
  The edit adds a run-directory name, `Fk/Contracts.lean`, `MakesliceC`, `E2e.EpUAccC` and `gen/gen1c/include_adapter.py`.
  `../../../AGENTS.md` does not allow run-directory names in committed files.
- The input paths in `../gen/desc/hand-types-ir.json` (key `file`).
  They are absolute container paths of an earlier run, and the files are not tracked.
  `../gen/desc/producer.py` does not read the key `file`.
  The paths are candidates for deletion.

### Other earlier names

- `../FINDINGS.md` cites earlier records by commit and path.
  An example is `prysm/go1.26.10/e2e/scal/negative-gen4.json` at `4499e775`.
  It also gives the earlier case ids in these records, for example `g4-ex-s82-*`.
  Git keeps each cited file at the cited commit.
  So these names stay as references, not as records.
- `../THIRD-PARTY-NOTICES.md` gives its sections the letters `A` to `I`.
  It refers to "family A" and "family B".
  Only that file uses the letters.
  They are candidates for plain words.
- `Spec/TestFixed.lean` (the structure `Spec.Fixed` and the lemmas `Spec.fixed*`) names the Go type `Fixed`.
  `../target/` has no type `Fixed`.
  `Spec/TestScalars.lean` imports the module for its byte lemmas, for example `Spec.uintBytes_size`.
  The type part of the module is a candidate for deletion.

### Standard short words

- Lemma names of the form instruction + constant + fact.
  Examples are `Machine.and7_zero`, `Machine.jg16_false`, `Machine.add8_neg8` and `Machine.shr3_toNat`.
  `Machine.zx8`, `zx16` and `zx32` are zero extensions of 8, 16 and 32 bits.
  `Machine.stackFrame144` is a frame of 144 bytes.
- The instruction, register, flag and memory words of Kraken and x86 inside `Codec` names.
  Examples are `lea`, `mov`, `nop`, `xor32`, `xmm15`, `r8`, `cmp_nc_true` and `Codec.lea_cmp_be_false`.
- Hypothesis and variable names in statements, for example `hk`, `hf`, `hlen`, `e0`, `e1`, `ra` and `fp` (section 3).

### Name forms

A module of a Prysm type is `Prysm/<GoTypeName>/<Role>.lean` in the library `Prysm`.
Its namespace is `Prysm.<GoTypeName>`.
`<GoTypeName>` is the Go type name as the Go source writes it.
It is never an abbreviation.
A declaration of the type uses a dotted name for the function part.
An example is `theorem Decode.reject_size` inside `namespace Prysm.Checkpoint`.

| Content of the module | Role name |
| --- | --- |
| Program constants read from the converted `.S` files | `Code` |
| Go struct layout (offsets, sizes) | `Layout` |
| Validity of the Go value of the receiver | `GoValue` (and `GoValueWitness` for its witness) |
| The EthLib description of the type and the bridge lemmas | `Spec` |
| The description generated for the description checker | `SpecChecker` |
| Equality of the hand description and the checker description | `SpecEquivalence` |
| Decoder, accept path | `DecodeAccept` |
| Decoder, one reject path | `DecodeRejectSize`, `DecodeRejectOffset`, `DecodeRejectAlignment`, `DecodeRejectOverflow`, `DecodeRejectDelegate` |
| Decoder, a loop or a call that the accept path uses | `DecodeLoop`, `DecodeCall`, with a plain qualifier when there are several |
| Decoder, connection to EthLib | `DecodeSpec` |
| Encoder, path with no slice growth | `EncodeFastPath` |
| Encoder, growth at the first append site only | `EncodeGrowFirstSite` |
| Encoder, growth at any one site / at any site | `EncodeGrowOneSite` / `EncodeGrowAnySite` |
| Encoder, a reject | `EncodeRejectLength`, `EncodeRejectTooBig`, and so on (name the cause) |
| Encoder, connection to EthLib | `EncodeSpec` |
| Encoder, a part of a long proof (head, tail, cover, a field) | `Encode` + plain word for the part (`EncodeHead`, `EncodeTail`, `EncodeCover`) |
| `SizeSSZ` | `Size` |
| `MarshalSSZ` | `Marshal` |
| Decode then encode, round trip, composition | `DecodeThenEncode` |
| A witness of theorem X (a concrete state that satisfies the premises) | `Witness` + the role of X (`WitnessDecodeAccept`, `WitnessEncodeFastPath`) |
| Statements only (definitions `..._statement : Prop`) | `Statements`, or `Statements` + plain qualifier |
| ELF data definitions of a link set, and the command that reads them | under `Prysm/ElfData/`: `<PlainSetName>` and `<PlainSetName>Reader` |

If no role fits, the module name uses plain words that say what the module holds.
Examples are `DecodeFieldSegments` and `SpecDescription`.
A module that holds several roles has the name of its main role.

The main theorems inside `Prysm.<GoTypeName>` have these names:

- decoder: `Decode.accept`, `Decode.reject_size`, `Decode.reject_offset`, `Decode.reject_alignment`, `Decode.reject_overflow`,
  `Decode.accept_spec`, `Decode.reject_<cause>_spec`, `Decode.reject_complete`;
- encoder: `Encode.fast_path`, `Encode.grow_first_site`, `Encode.grow_one_site`, `Encode.grow_any_site`, `Encode.reject_length`,
  `Encode.reject_too_big`, `Encode.fast_path_spec` (and `Encode.<path>_spec` for the other paths);
- `SizeSSZ`: `Size.result`, `Size.result_spec`; `MarshalSSZ`: `Marshal.result`, `Marshal.result_spec`;
- decode then encode: `DecodeThenEncode.round_trip`;
- a suffix in words states an added premise, for example `Decode.reject_alignment_error_word_nonzero`;
- the statement of a theorem is the `def` or `abbrev` with the name of the theorem + `_statement`;
- program constants: `Code.unmarshalSSZ`, `Code.marshalSSZTo`, `Code.sizeSSZ`, `Code.marshalSSZ`; descriptions: `desc`,
  `checkerDesc`; Go layout: `goFields`, `goSize`;
- a function specification of a method: `Decode.accept_function_spec` or `Encode.fast_path_function_spec`; the lemma
  that it holds has the suffix `_holds`;
- a witness file has the namespace `Prysm.<GoTypeName>.Witness.<Role>` (for example `Witness.DecodeAccept`), and its
  main theorem is `runs`, with a plain qualifier for the case (`runs_empty`, `runs_one_element`, `runs_maximum`).

The generators write the names `Decode.generated_*` and `Encode.generated_*` (`../gen/README.md`).
