# Findings

This file lists what the proof work found in the generator, the generated code, the tools and the process.
Each entry gives what is wrong or what the limit is, where it is, how it shows, and its state.
The state is the state that the records give. "Open" means that no fix exists in the tree.
How to handle a new finding is in `../README.md` section 7.

## 1. Generator and runtime library

### Bitvector decoder accepts a byte with padding bits set

- What: the decoder of a bitvector field accepted an input byte with bits set above the bitvector length. The specification rejects such a byte.
- Where: the generated decoder and `ssz.ValidateBitvector`.
- How it shows: a proof attempt on a bitvector test type found the counterexample.
- State: fixed in commit `f0b85c7`.

### Bitvector padding check can overflow

- What: the check that the padding fix added could panic on a `uint64` overflow.
- Where: `ssz.ValidateBitvector`.
- How it shows: code review found it. A proof did not find it.
- State: fixed in commit `60d4d3b`.

### Bitlist encoder checks the length in bytes, not in bits

- What: the encoder accepted a bitlist with more bits than the limit, if its byte count fit the limit.
- Where: the generated encoder of a bitlist field. It now calls `ssz.ValidateBitlist(x, limit)` with the limit in bits.
- How it shows: a proof attempt on a bitlist test type found the counterexample.
- State: fixed in commit `280b752`.

### Array field decoder emits a `make` that does not compile

- What: the decoder of a `[N]T` array field had a `make` call that Go does not compile.
- Where: the generator template for array fields.
- How it shows: the generated code does not build.
- State: fixed. The records connect this fix to commit `ab0fb00` only by elimination. The connection is not confirmed.

### Nested container fields have the wrong keys in the IR

- What: in the generator IR, the field keys of a nested container are the container name, not the field names.
- Where: the `case *types.Struct:` branch of `FieldParser.expand` in `sszgen/representer.go`. It appends `f.name`, where it needs `field.Name()`.
- How it shows: `ssz ir --type-names=AttestationData` on `fv/kraken/target/prysm` gives the key `Checkpoint` for the fields `Epoch` and `Root` of `Source`.
- Effect: no effect on the generated Go code. Tools that read the IR get wrong keys.
- State: open. The generator is not changed.

### Generator log has an empty package name

- What: a log line reads `Generating methods for /StatusV2`.
- Where: `packages.Config.Mode` in `sszgen/importer.go` has no `NeedName`, so `PkgPath` is empty.
- Effect: none on the output files.
- State: open.

### Hand-written primitive methods are not generated

- What: Prysm `consensus-types/primitives` has hand-written SSZ methods for `Slot`, `Epoch`, `ValidatorIndex`, `Gwei` and `CommitteeIndex`. The generated code calls them for these fields.
- Where: 24 functions, called by 52 generated types.
- Effect: each needs its own specification and proof. A generated decoder that calls one depends on it.
- State: the records give proofs of the `Epoch` decoder accept path (function specification `Prysm.Epoch.Decode.accept_function_spec`) and its length reject. They give the other methods as not proved.
  The generated table `prysm/proof-inventory.md` lists the theorems that exist now for each primitive method.

### Encoders write into the caller array before a later length reject

- What: an encoder appends the earlier fields to `dst` before it tests the length of a later field.
  On the reject, it returns `nil` and an error, but the bytes stay in the backing array of the caller beyond `len(dst)`.
- Where: `(*v1alpha1.Checkpoint).MarshalSSZTo` writes the 8 epoch bytes before the `Root` length test.
  `(*v1alpha1.BeaconBlockHeader).MarshalSSZTo` writes `Slot`, `ProposerIndex` and earlier roots before a later root length test.
- How it shows: `Prysm.Checkpoint.Encode.reject_length` states the written bytes. Its negative test with "dst unchanged" fails.
- Effect: SSZ has no rule for a Go value with a wrong field length. The generator documents only that `dst[:len]` is unchanged (commit `e9cbf5c`).
- State: classified as known behavior, not a specification violation. The Checkpoint entry has no independent review. The BeaconBlockHeader entry is reviewed.

### AttestationData encoder writes the receiver

- What: if `Source` or `Target` is nil, the encoder stores a new zero `Checkpoint` in the receiver before it encodes it. The zero `Checkpoint` then fails with `ErrBytesLength`.
- Where: `(*v1alpha1.AttestationData).MarshalSSZTo`.
- Effect: an encoder theorem must state this change of the receiver.
- State: known behavior, not a specification violation. No encoder theorem exists for this type yet.

### AttestationData decoder always allocates Source and Target

- What: the decoder allocates a new `Source` and `Target`, also when the receiver already has them. This is the same as the Go source.
- Where: `(*v1alpha1.AttestationData).UnmarshalSSZ`.
- How it shows: `E2eAd.ad_e2e_accept_main` states the new pointers for every old receiver.
- State: known behavior, proved.

### Error paths with `%d` allocate

- What: an error built with `fmt.Errorf` and `%d` arguments boxes each argument with `runtime.convT64`, so the error path allocates.
- Where: for example the element offset order error of a list-of-lists decoder in the test types.
- State: observation. It is an input for optimization work.

### Bitlist error messages differ from three Prysm tests

- What: after the bitlist fix, the encoder rejects the same inputs as before with a different error text.
- Where: Prysm `consensus-types/blocks` tests `TestMarshalPartsMetadata/available_too_large`, `/requests_too_large` and `TestPartialDataColumn_PartsMetadata/marshal_error_due_max_bitlist_size`.
- State: compatibility issue, not a generator defect. The tests are not changed.

### Option that reserves the encoder output once is not adopted

- What: a generator option `--reserve-marshal` makes `Checkpoint.MarshalSSZTo` reserve `len + 40` bytes once.
  With an invalid `Root` and 8 to 39 spare bytes, the new code allocates one block and does not write the spare bytes of the caller.
- Where: generator commit `ca191bb` on a branch that is not merged. The evidence is in `prysm/go1.26.10/opt-r1/` and `lean/Prysm/Checkpoint/CapacityReserved*.lean`.
- How it shows: the benchmark results are mixed. The fast path is slower and the error path allocates one more block.
- State: not adopted. The option is off by default. The old proofs apply only to the old ELF.

### In-place hash call depends on an aliasing premise

- What: the in-place `gohashtree.Hash` call depends on an aliasing premise.
- State: a test pins the premise (commit `b03a45d`). Not a defect. A hash tree root proof must state it.

## 2. Verification tools and machine model

### Kraken cannot parse `bsr`

- What: the Kraken parser has no `bsr` instruction.
- Where: `ssz.ValidateBitlist` uses `bsr` for `bits.Len8` in the `GOAMD64=v1` build.
- Effect: the bitlist validation can only be a contract. The core bitlist checks are behind that contract.
- State: open. It is a request to Kraken.

### Kraken cannot parse some operand and instruction forms

- What: the Kraken parser rejects the SIB index `%riz` and multi-byte padding `nop` forms. The `include_x64` elaborator rejects some condition codes.
- Where: 13 generated functions had `%riz`.
- State: worked around. `link/conv.py --norm` drops `%riz` and writes padding as `nop`. `include_x64_rt` (`lean/Machine/Include.lean`) uses the runtime parser.

### Converter wrote a negative 32-bit displacement as a large positive number

- What: `go tool objdump -gnu` writes a displacement of −228 as `0xffffff1c`. Kraken reads that form as a positive number, so the address in the proof is not the machine address.
- Where: `link/conv.py` output, for example `IndexedAttestation.UnmarshalSSZ`. The full Prysm disassembly had 161 such operands in 104 functions.
- How it shows: `clang` rejected the line in the reassembly step of the link check.
- State: fixed in commit `93b3f2a`. `link/conv.py --norm` writes the signed form. The SIB form without a base and the segment form are not handled. The Prysm ELF has none of them.
  A displacement range check in `link/check.py` is not added.

### Stack guard branch exhausts kernel memory

- What: a `simp` and `omega` proof that the stack growth branch is not taken fails in the Lean kernel on memory, for the form `lea -N(%rsp),%r12; cmp 0x10(%r14),%r12; jbe`.
- Where: `BeaconBlockHeader.MarshalSSZTo` and other encoders with a large frame.
- How it shows: a pure `BitVec` reproduction fails under a 5 GiB limit. The costly subterm is not profiled.
- State: fixed by the lemma `Codec.lea_cmp_be_false` (`lean/Codec/StackGuard.lean`), with no heartbeat increase. The docstring of that file gives a different memory value than the measurement.

### Growslice contract gives no lower bound on the remaining heap

- What: `GrowsliceC` gives the remaining heap only as an upper bound. A second growth call needs a lower bound as its budget premise.
- Where: `lean/Runtime/Contracts.lean`. It affects every encoder growth path.
- How it shows: in `Prysm.Checkpoint.Encode.grow_any_site_three_cases`, one case ends at the entry of the second growth call. The run after that state is not proved.
- State: blocked until a user decision on a new contract form. That case has only Go differential checks. The growth branches of the other encoders are not proved.

### The `ecancel` tactic fails on some atom forms

- What: `ecancel` fails when two atoms print the same but elaborate differently. It times out on `uintBytes` of a symbolic value. It fails with a trailing `⋆ emp` and with some atom orders. An atom such as `StaticBox (-4 + rcx)` hits the recursion limit.
- State: worked around. The workarounds are `generalize` of the byte lists, a re-elaboration with `rw [show a = a from rfl]`, and `simp only [sep_assoc, sep_emp]` before an AC sort. The causes are not verified.

### Other tactic gaps

- `kaddr` (`lean/Machine/Step.lean`) does not reduce `Width.W64.bits`. The local macro `eaddr` is used instead.
- A `grind` timeout inside `kstep` cannot be caught. `load_step` and `store_step` are used instead.
- Closing register goals with symbolic `BitVec` by `trivial` or `rfl` inside `first` used more than 6 GiB. The decoder proof is split, and the goals close with `exact trivial`, `with_reducible rfl` or `toBitVec_inj`.
- Two witness `Host` instances in one file make instance resolution choose the wrong host. Each file has one witness host.
- `lean/Machine/Include.lean` keeps the data reader private. Other libraries copy it, and `gen/e2e/check_include.py` compares the copies.
- State: worked around in each case.

### Format string content is not checked

- What: Lean binds a format string only by its length and the absence of `%`. The agreement of its verbs with the contracts `FmtErrorfWC`, `FmtErrorfDWC` and `FmtErrorfDDC` is a contract hypothesis.
- State: open.

### Allocation type argument is not connected to the element size

- What: the type descriptor argument of `MakesliceC` and `NewobjectC` is not connected to the element size or object size in the contract.
  For example, the object size 120 of the `Deposit_Data` allocation is a premise of the statement. No theorem ties it to the data file.
- State: accepted contract hypothesis.

### Link check result changes on a new run

- What: the tracked `RESULT` files hash an axioms listing file that is no longer in the tree. `link/check.py` hashes that file only if it exists.
- Effect: a new run writes a `RESULT` without that line, with a different bundle hash.
- State: open.

### The proof generator covers only some code forms

- What: `gen/scal/scalgen.py` matches fixed instruction templates. It refuses a field whose code has another form.
- Where: the records give these forms as refused or not covered:
  - 20-byte, 4-byte and 1-byte byte vectors, `bool` fields and the `Gwei` callee.
  - The inline `DepositCount` read.
  - A receiver reloaded into `rax`, and a call set-up with the receiver already in `rax`.
  - A padding `nop` after a call, and compositions with call fields.
- Encoder side: the six compiled sites that append a 32-byte field have six different instruction texts. Only the call step is shared. The steps before the call stay per site.
- State: open proposals. A generator change needs user approval.
- Open generator items: an internal refusal inside one phase can report full coverage in the summary (not reachable today). A stale `--partial-out` file can remain on exit 0 or 2. No summary is written on an interrupt.

### Kind checks do not bind every parameter

- What: the accept kind `decAcceptKindN` does not read the frame of its layout. An accept kind line with a wrong frame still elaborates.
  `gen/scal/kindcheck.py` does not bind the code constant to the `.S` file of the header. It does not check the `.S` label against the IR type.
- How it shows: a negative test with a wrong frame in the kind line gives no error. The head, field and epilogue kinds fix the frame.
- State: open. A kind change needs a new lemma unit.

## 3. Proof process and checks

### Negative test classifier can count a wrong failure as a pass

- What: a mutant passes when Lean reports an error inside the theorem. An unknown identifier or a parse error is such an error, but it does not test the code.
- Where: `gen/e2e/negative.py`.
- State: fixed in part (commit `23eceac` and later). Such first errors get the class `wrong_target`. The list of patterns is not complete. Read the first error of every row.

### A theorem can look closed when it is not

- What: Lean registers a theorem that the kernel rejects as an axiom. `case tag => tac` logs an error, admits the goal and continues.
- How it shows: in a scratch file, segment theorems depended on `sorryAx` although the run looked clean.
- State: rule. A scratch result is closed only when `#print axioms` of every theorem that it uses has no `sorryAx` and does not list the theorem itself.
- A job command must end with the Lean exit code. A command that ends with `echo` hides a failure.

### A generated theorem can carry an extra hypothesis

- What: a proof by `exact` checks only the text after the colon. A hypothesis added before the colon still compiles.
- State: fixed by the `_kind` identity on the full type (commit `094e51e`) and the text check `gen/scal/kindcheck.py`. Neither check alone is enough.

### `lake env lean` does not check that the build is current

- What: `lake env lean` uses `.olean` files without a trace check. A stale file can make a check pass.
- State: fixed in commit `875368f`. The drivers run `lake build --no-build` first and stop on a nonzero exit.

### Negative test time limit killed only the wrapper

- What: the per-case time limit killed only the memory-limit wrapper, not the Lean process tree.
- Where: `gen/tools/memcap.py`.
- State: fixed in commit `cc61ebc`.

### Slow proof steps

- What: two proofs spent most of their time in one `omega` side goal each.
- Where: the `bv_omega` of the argument `hLo` of `Codec.rootenc_seg` in `lean/E2eScal/P2EncCp.lean`. The `wit_split` side goals of the Checkpoint cover witnesses.
- State: fixed. `lean/Machine/WitnessSplit.lean` has `wit_split_n` (commit `301300f`). The `P2EncCp` step is a constant-only rewrite (commit `ab43cbb`).

### Limit options without a profiled cause

- What: many files set `maxHeartbeats` or `maxRecDepth` above the default with no written, profiled cause.
  The flat encoder and the 24 other flat types add `maxHeartbeats 16000000` and `4000000` and `maxRecDepth 100000` in many files.
- State: open. They stay until a profile exists or the user accepts them as model-file values. Do not copy them for new work.

### Theorems that end with `⋆ True`

- What: five Checkpoint theorems do not state the rest of memory: `Prysm.Checkpoint.DecodeThenEncode.encode_decoded_receiver`, `Prysm.Checkpoint.Encode.fast_path_spec`, `Prysm.Checkpoint.DecodeThenEncode.round_trip`, `Prysm.Checkpoint.Encode.cover` and `Prysm.Checkpoint.Encode.reject_length_cover`.
- State: disclosed. The component theorems and the `*_framed` cover theorems state the exact frame. The composition has no framed version.
- Related: `bh_e2e_accept_main` hides three argument-area slots in one 24-byte existential. They are dead stack only. The statement is not changed.

### Docstrings that say more than their theorem

- What: the docstrings of the `*_reject_complete` theorems of `PendingDeposit`, `PowBlock`, `SyncCommitteeMessage` and `PendingConsolidation` say that the code reaches the `ssz.ErrSize` site. The theorem proves only `size ≠ N`.
  A comment in `lean/E2eScal/VbDesc.lean` names the wrong Prysm tree.
- State: open. The fix is a `.lean` edit.

### Unreachable error wraps hold only with the callee specifications

- What: the theorems of an unreachable error wrap state a conditional skip: if the callee returns `rax = 0`, the code skips the wrap.
  Unreachability for every input holds only together with the callee specifications, such as `E2eAd.SlUAccC` and `E2eScal.ViUAccC`.
- State: recorded. The theorems are not changed.

### Hand `Desc` is independent in content, not always in time

- What: for some types, the hand `Desc` is younger than the printed checker `Desc` of the same type.
- Effect: the hand `Desc` copies consensus-specs, but its independence from the checker is by content only.
- State: recorded. A new type must have its hand `Desc` written before the checker `Desc` is printed.

### Several code directories are not Lake inputs

- What: `E2eScal` and `lean/Prysm/Checkpoint/CapacityReservedCode.lean` include `.S` files from directories that `lean/lakefile.toml` does not declare as inputs.
  A change in such a file does not make Lake build the proofs again.
- Where: the `norm` directories of the link sets `bh`, `e1`, `enc2`, `f24`, `h3`, `h4`, `h5` and `h6` under `prysm/go1.26.10/e2e/`, and `prysm/go1.26.10/opt-r1/link/norm`.
  The declared input `lv_dep_data` is not read by any Lean file. `E2eDep.Code.depDataType_addr` is a hand definition. `gen/e2e/depcheck_data.py` compares it with its data file.
- State: open. A `lakefile.toml` change needs user approval.

### Inventory script trusts its method list

- What: `gen/tools/proof_inventory.py run` trusts `prysm/go1.26.10/ssz-methods.json` for methods without a converted `.S` file. Only the `methods` mode and a `cmp` bind that file to the ELF.
  A development type without a mapping row ends in a `KeyError`, not in a FAIL line.
  19 mapped names are not in the `#print axioms` hand list `gen/axioms-lists/flat-fixed-size-types.lean`. `gen/tools/inventory_decls.lean` checks their axioms on every run.
- State: open.

### Open checker items of the flat encoder generator

- The macro `eb` is declared at the root level (`lean/Codec/EncodeFieldHelpers.lean`).
- A broken checker copy fails with a `KeyError`, not with a check result.
- The IR reader of the encoder generator accepts any untagged 8-byte field as `uint64`.
- The negative tests that compare the IR with the code change one theorem only. There are no whole-file mutants.
- `prysm/go1.26.10/e2e/scal/e2c/own_layout_e2g_r1.py` is not a step of a gate script.
- State: open. Each needs a checker or test change.

### Paths that the proofs do not cover

- The stack growth path and the write barrier path of every function. The premises exclude them.
- The encoder growth branches (see the growslice entry), the length rejects with a small capacity, and the `moveSliceNoCapNoScan` branch of `PowBlock`, `HistoricalSummary` and `SigningData`.
- The frame separation premise of the encoders is not justified for every Go caller.
- The `IndexedAttestation` alignment and overflow rejects are proved only with the added premise that the error word is not zero.
- State: open. `prysm/proof-inventory.md` lists the paths not proved for each method.

### Recursion depth limits without a located cause

- What: four witness examples raise `maxRecDepth` and the cause is not known. The rule asks for a profiled cause for each raised limit.
- Where: `lean/E2eEnc/WitF.lean` (one place, limit 4000) and `lean/E2eEnc/WitG.lean` (three places, limit 8000).
- How it shows: the examples fail at 512 and at 2000. `WitG.lean` also fails at 4000. The comment at each place says that the cause is not located.
- State: open.

## 4. Target and environment

### No run on x86-64 hardware

- What: no test compares Kraken with a real x86-64 CPU. The hosts are arm64.
- Effect: the Go differential checks run on arm64. They check Go semantics, not the amd64 machine code.
- State: open.

### Go layout comes from `go/types`

- What: the receiver layout of the theorems comes from the gc amd64 size rules of `go/types` (`prysm/ir/ir-mainnet.json`, `go_fields`). The ELF `abi.Type` has no named symbol, so the proofs do not read it.
- State: open. No amd64 run confirms it.

### Runtime contracts are not proved on the compiled runtime

- What: the contracts come from a reading of the Go 1.26.3 runtime source. A source comparison (`gen/e2e/runtime_diff.py`) found the functions behind each contract unchanged in Go 1.26.10.
  `growslice` and `nextslicecap` are byte-identical. The changed functions (`moveSliceNoCap`, `itabInit`, `adjustframe`, GC stack scanning) carry no contract.
  The compiled runtime code is not compared. The contracts also assume no garbage collection during a call and a successful allocation.
- State: accepted trust item.

### Minimal preset failures in Prysm

- What: with `-tags minimal`, the `consensus-types/blocks` tests do not compile, and `encoding/ssz/detect` `TestByState` panics.
- State: the records give the same failures with the committed Prysm files. Not related to the generated code.

### Reduced Prysm types of the test target differ from Prysm

- What: `target/prysm/types.go` copies the SSZ schema of `Checkpoint` and `AttestationData`, without the protobuf fields. Their Go layout is not the Prysm layout.
- State: by design. The Prysm proofs use the real protobuf types of the Prysm ELF.

### Absolute paths in committed records

- What: some generated records contain absolute paths of the original machine, for example `prysm/go1.26.10/e2e/negative/result.json`.
  Two Python bytecode files in git history contain container paths. They are not in the current tree.
- How it shows: `git grep -nE "/workspace|fve2e-" -- fv/kraken ':!fv/kraken/lean/.lake'`.
- State: open. The user decides how to treat the history before publication.

### Two tracked files differ only in case

- What: `prysm/INVENTORY.json` and `prysm/inventory.json` were both tracked.
- Effect: on a file system that ignores case, only one exists, and `git status` shows a change that is not real.
- State: fixed. The per-method table is now `prysm/proof-inventory.json` and `prysm/proof-inventory.md`.
