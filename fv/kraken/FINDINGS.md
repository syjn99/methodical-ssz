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
- How it shows: `Prysm.AttestationData.Decode.accept` states the new pointers for every old receiver.
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
- Where: a generator branch that is not merged.
- How it shows: the benchmark results are mixed. The fast path is slower and the error path allocates one more block.
- State: closed. The option is not adopted and is off by default.
  Its test ELF records, its negative cases and its Lean proofs are deleted from the tree. Git history keeps them.

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
- Where: 13 generated functions had `%riz` in the Kraken parser run of the record `prysm/go1.26.10/kparse.json` (commit `f55333d1`), made before the converter dropped `%riz`.
- State: worked around. `link/convert_objdump.py --norm` drops `%riz` and writes padding as `nop`. `include_x64_code` (`lean/Machine/Include.lean`) uses the runtime parser.

### Converter wrote a negative 32-bit displacement as a large positive number

- What: `go tool objdump -gnu` writes a displacement of −228 as `0xffffff1c`. Kraken reads that form as a positive number, so the address in the proof is not the machine address.
- Where: `link/convert_objdump.py` output, for example `IndexedAttestation.UnmarshalSSZ`. The full Prysm disassembly had 161 such operands in 104 functions.
- How it shows: `clang` rejected the line in the reassembly step of the link check.
- State: fixed in commit `93b3f2a`. `link/convert_objdump.py --norm` writes the signed form. The SIB form without a base and the segment form are not handled. The Prysm ELF has none of them.
  A displacement range check in `link/check.py` is not added.
  Every converted file of `prysm/go1.26.10/link-set/norm/` is the output of a fresh `--norm` run and has the signed form.

### Stack guard branch exhausts kernel memory

- What: a `simp` and `omega` proof that the stack growth branch is not taken fails in the Lean kernel on memory, for the form `lea -N(%rsp),%r12; cmp 0x10(%r14),%r12; jbe`.
- Where: `BeaconBlockHeader.MarshalSSZTo` and other encoders with a large frame.
- How it shows: a pure `BitVec` reproduction fails under a 5 GiB limit. The costly subterm is not profiled.
- State: fixed by the lemma `Codec.lea_cmp_be_false` (`lean/Codec/StackGuard.lean`), with no heartbeat increase. The docstring of that file gives a different memory value than the measurement.

### Growslice contract gives no lower bound on the remaining heap

- What: `GrowsliceContract` gives the remaining heap only as an upper bound. A second growth call needs a lower bound as its budget premise.
- Where: `lean/Runtime/Contracts.lean`. It affects every encoder growth path.
- How it shows: in `Prysm.Checkpoint.Encode.grow_any_site_three_cases`, one case ends at the entry of the second growth call. The run after that state is not proved.
- State: blocked until a user decision on a new contract form. That case has only Go differential checks. The growth branches of the other encoders are not proved.

### The `ecancel` tactic fails on some atom forms

- What: `ecancel` fails when two atoms print the same but elaborate differently. It times out on `uintBytes` of a symbolic value. It fails with a trailing `⋆ emp` and with some atom orders. An atom such as `StaticBox (-4 + rcx)` hits the recursion limit.
- State: worked around. The workarounds are `generalize` of the byte lists, a re-elaboration with `rw [show a = a from rfl]`, and `simp only [sep_assoc, sep_emp]` before an AC sort. The causes are not verified.

### Other tactic gaps

- `address_equation` (`lean/Machine/Step.lean`) does not reduce `Width.W64.bits`. The macro `checkpoint_addr` (`lean/Prysm/Checkpoint/DecodeAccept.lean`) is used instead.
- A `grind` timeout inside `kstep` cannot be caught. `load_step` and `store_step` are used instead.
- Closing register goals with symbolic `BitVec` by `trivial` or `rfl` inside `first` used more than 6 GiB. The decoder proof is split, and the goals close with `exact trivial`, `with_reducible rfl` or `toBitVec_inj`.
- Two witness `Host` instances in one file make instance resolution choose the wrong host. Each file has one witness host.
- `lean/Machine/Include.lean` keeps the data reader private. `lean/Prysm/ElfData/PrysmTargetReader.lean` has one copy, and `gen/checks/check_include.py` compares it with the original.
- State: worked around in each case.

### Format string content is not checked

- What: Lean binds a format string only by its length and the absence of `%`. The agreement of its verbs with the contracts `FmtErrorfWrapContract`, `FmtErrorfDecimalWrapContract` and `FmtErrorfDecimalDecimalContract` is a contract hypothesis.
- State: open.

### Allocation type argument is not connected to the element size

- What: the type descriptor argument of `MakesliceContract` and `NewobjectContract` is not connected to the element size or object size in the contract.
  For example, the object size 120 of the `Deposit_Data` allocation is a premise of the statement. No theorem ties it to the data file.
- State: accepted contract hypothesis.

### Link check result changes on a new run

- What: `link/check.py` hashes the ELF, the `norm/*.S` files, the `data/*.data` files and `AXIOMS.txt` if it exists. It hashes no Lean file.
  A `RESULT` file that has a sha256 line for a file that is not in the tree gets a different bundle hash on a new run.
- Where: the three `RESULT` files `link/out/RESULT`, `prysm/go1.26.10/link-set/RESULT` and `prysm/go1.26.10/link/RESULT`.
- State: fixed. Each of the three files is the output of a new run on its pinned ELF. None has a sha256 line for a Lean file or `AXIOMS.txt`.

### Link set `prysm/go1.26.10/link` has no tracked disassembly

- What: the directory of this link table (136 functions, read by no theorem) has no `target.objdump`. `link/check.py` needs it.
  Its `norm/` directory is complete: 136 `.S` files and `all.S`, the functions of the 136 `PASS (a)` lines of its `RESULT`.
- How to check it: filter the full disassembly of the pinned ELF (`gen/prysm-elf.sh` writes it) on the functions of `norm/`.
  A function is kept when the clean name of `link/convert_objdump.py` of its `TEXT` line names a `.S` file of `norm/`.
  Then run `link/check.py` on a copy of the directory with that `target.objdump`, the ELF as `target-amd64` and its symbol listing as `target-amd64.nm`.
  The result is exit 0 and 224 PASS lines. Every PASS and DIFF line equals the committed `RESULT`.
- Earlier attempt: a check with the whole disassembly (641 functions) needed `.S` files that `norm/` does not hold.
  A fresh conversion of all 641 functions gives 1269 PASS lines and one FAIL: the reassembly of
  `v1alpha1.BeaconStateBellatrix.MarshalSSZTo` at `0x93fd87`. The ELF bytes of that `jge` are `0f8d7a000000`, and clang gives a 2-byte form.
  That function is not in the table and has no proof.
- State: the table checks with a rebuilt disassembly. The committed `RESULT` is the output of this check on the pinned ELF.
  The link set `prysm/go1.26.10/link-set` passes on the same ELF.

### The proof generator covers only some code forms

- What: `gen/generator/generator.py` matches fixed instruction templates. It refuses a field whose code has another form.
- Where: the records give these forms as refused or not covered:
  - 20-byte, 4-byte and 1-byte byte vectors, `bool` fields and the `Gwei` callee.
  - The inline `DepositCount` read.
  - A receiver reloaded into `rax`, and a call set-up with the receiver already in `rax`.
  - A padding `nop` after a call, and compositions with call fields.
- Encoder side: the six compiled sites that append a 32-byte field have six different instruction texts. Only the call step is shared. The steps before the call stay per site.
- State: open proposals. A generator change needs user approval.
- Open generator items: an internal refusal inside one phase can report full coverage in the summary (not reachable today). A stale `--partial-out` file can remain on exit 0 or 2. No summary is written on an interrupt.

### Kind checks do not bind every parameter

- What: the accept kind `decodeAcceptKindAnyFrame` does not read the frame of its layout. An accept kind line with a wrong frame still elaborates.
  `gen/generator/kindcheck.py` does not bind the code constant to the `.S` file of the header. It does not check the `.S` label against the IR type.
- How it shows: a negative test with a wrong frame in the kind line gives no error. The head, field and epilogue kinds fix the frame.
- State: open. A change of the kind needs new lemmas and a new check of every kind instance.

## 3. Proof process and checks

### Negative test classifier can count a wrong failure as a pass

- What: a mutant passes when Lean reports an error inside the theorem. An unknown identifier or a parse error is such an error, but it does not test the code.
- Where: `gen/checks/negative.py`.
- State: fixed in part (commit `23eceac` and later). Such first errors get the class `wrong_target`. The list of patterns is not complete. Read the first error of every row.

### Negative cases that do not pass

- What: the first full run of the Lean mutant suite on the renamed tree (commit `7adfc767`, all 1062 cases) passed 1036 cases.
  Six of the 26 others were broken by the restructuring; their case texts are corrected (below), and a Lean run of
  these six after the correction passes all six. The count is then 1042 passing and 20 not passing (the 1036 other
  results are from the full run; the six from the later run).
  Each of the 20 has the same outcome in a committed result record from before the restructuring. The list below gives
  the commit, the record path and the earlier case id of each; the records are on the archive branches of the earlier
  history, see the commit message of `eca2b556`. Their mutation texts are the same as in the base case files, and their ranges differ only by the moved
  lines of their modules and by the range rule below.
- Range rule of the tool: the case range starts at the first line of the theorem's command (`set_option … in` lines and an
  attached doc comment `/-- … -/`; `negative.py` `command_start`, used by `list_negative.py`). Lean reports an error of the
  whole declaration, for example its heartbeat timeout, at that line. With this rule
  `checkpoint-encode-fast-path-of-kind-statement-encode-layout-32-to-48` (designed error inside the theorem, then a
  heartbeat timeout of the declaration at its first line) passes. A plain comment, a module comment or a line comment above
  the theorem does not widen the range (self-test fixtures).
- Fixed by the six case-text corrections (a Lean run after the correction: the control passes and the five mutants fail inside their theorems):
  - `sync-committee-message-decode-example-step-directive-82-control` and the four code mutants
    `…-directive-82-code-mov-0x78-rsp-to-0x70-rsp`, `…-directive-86-code-add-rax-to-rdx`, `…-directive-87-code-mov-ecx-to-eax`,
    `…-block-root-segment-code-mov-rax-to-rdx` (`prysm/go1.26.10/evidence/generator-cases/negative-cases-steps.json`): the
    module names its code constant relatively (`Code.unmarshalSSZ` inside `namespace Prysm.SyncCommitteeMessage`), and
    the case namespace `Prysm.SyncCommitteeMessage.Code` made the tool declare `Prysm.SyncCommitteeMessage.Code.Code.unmarshalSSZMut`,
    so the renamed uses did not resolve (`Unknown identifier`). The case namespace is now `Prysm.SyncCommitteeMessage`.
    Before the restructuring they passed (`4499e775`, `prysm/go1.26.10/e2e/scal/negative-gen4.json`, `g4-ex-s82-*`, `g4-ex-s86-code-reg`, `g4-ex-s87-code-clobber`, `g4-ex-br-code-reg`).
  - `checkpoint-encode-generated-fast-kind-statement-prysm-checkpoint-to-eth1-data` (`…/negative-cases-fast-path.json`):
    the mutant names `Prysm.Eth1Data.encodeLayout`, which the case module reached through
    `Prysm.BeaconBlockHeader.EncodeFastPathKindInstances` until commit `7adfc767` removed that import. The case now has
    `mutant_imports: ["Prysm.Eth1Data.EncodeFastPathKindInstances"]`. Before the restructuring it passed (`f6ee2b6c`,
    `prysm/go1.26.10/e2e/scal/gen6/neg-result.json`, `g6-cp-kind-layout`, class `inside`). No other case names a declaration of the two Eth1Data modules.
- The 18 remaining cases that do not pass (present id, class, earlier record with the same outcome, cause):
  - An earlier theorem of the module owns the mutated directive (Lean keeps a failed theorem with `sorry` and continues,
    so the designated theorem has no error; class `outside`):
    - `sync-aggregate-decode-accept-code-movq-0x40-to-0x3f`: `3a7e90b3`, `prysm/go1.26.10/e2e/lv/negative-lv.json`,
      `lv-sa-bitslen63`. The segment lemma `Prysm.SyncAggregate.Decode.bits_segment` owns the directive; the case
      `sync-aggregate-decode-bits-segment-code-movq-0x40-to-0x3f` (same mutation) passes.
    - `eth1-data-encode-encode-deposit-root-code-callq-runtime-memmove-to-runtime-growslice`: `792c8125`,
      `prysm/go1.26.10/e2e/scal/negative-enc.json`, `enc-e1-a-call` (recorded there as "mis-targeted"). The lemma
      `Prysm.Eth1Data.Encode.call_at` owns the `callq`; the case `eth1-data-encode-call-at-code-callq-runtime-memmove-to-runtime-growslice` passes.
    - `pending-deposit-decode-generated-reject-code-add-0x40-to-0x48`: `d3dddd1a`, `prysm/go1.26.10/e2e/scal/negative-gen5g.json`,
      `g5g-pd-rej-code-frame`. One error is inside `Decode.generated_reject`; the other is in the identity theorem
      `Decode.generated_accept_statement` before it, which compares the generated accept theorem (renamed to the mutated
      code constant) with the hand statement of `Prysm/PendingDeposit/Statements.lean` (the original constant), so it fails
      for every code mutation of this module.
  - The kind does not read the frame (entry "Kind checks do not bind every parameter"; class `no_error`):
    `voluntary-exit-decode-generated-accept-statement-uint64-80-to-88`: `d3dddd1a`, `g5g-ve-acc-kind-frame`.
  - Stuck `rfl` comparison (class `timeout_heartbeat` at 200000 heartbeats): the mutated literal is a return directive
    (`Host.addrOf (k + jret)`) or a pointer index (`ps.getD ip 0`) over the abstract `Host` and list `ps`; `rfl` finds
    no constructor clash and unfolds until the limit. The structural mutants of the same groups fail at once.
    - `blob-identifier-decode-accept-is-kind-statement-bytes-32-to-33`: `f5c5f528`, `prysm/go1.26.10/e2e/scal/negative-gen3.json`, `g3-kindacc-stmt-jret`.
    - `pending-deposit-decode-accept-is-kind-any-frame-statement-layout-mixed-frame40-131-to-130` and
      `beacon-block-header-decode-accept-is-kind-any-frame-statement-prysm-2-to-1`: `4d330a0a`, `prysm/go1.26.10/e2e/scal/negative-gen5.json`,
      `g5-tie-pd-kind-jret`, `g5-tie-bh-kind-ptr`.
  - Other heartbeat timeouts (class `timeout_heartbeat`; the cause is not analysed):
    - `codec-window-steps-step-store-statement-get64-r-s-to-r-b`: `4499e775`, `prysm/go1.26.10/e2e/scal/negative-gen4.json`, `g4-sk-st-stmt-src`.
    - `deposit-data-decode-accept-spec-statement-rax-96-to-48` (4000000 heartbeats): `f704f6f0`, `prysm/go1.26.10/e2e/scal/negative-h4.json`, `dd-ask-stmt-siglen`.
    - `sync-aggregator-selection-data-decode-accept-spec-statement-uint-bytes-slot-to-subcommittee-index`,
      `validator-balance-decode-accept-spec-statement-uint-bytes-index-to-balance`,
      `voluntary-exit-decode-accept-spec-statement-uint-bytes-epoch-to-validator-index`: `499db402`,
      `prysm/go1.26.10/e2e/g5c/negative-g5c.json`, `g5c-sa-speck-stmt-field-swap`, `g5c-vb-speck-stmt-field-swap`, `g5c-ve-speck-stmt-field-swap`.
    - `sync-committee-message-decode-accept-spec-statement-uint-bytes-validator-index-to-slot`,
      `sync-committee-message-decode-accept-spec-statement-host-141-to-140`,
      `pending-consolidation-decode-accept-spec-statement-uint-bytes-target-index-to-source-index`,
      `pending-consolidation-decode-accept-spec-statement-host-56-to-55`: `18432398`,
      `prysm/go1.26.10/e2e/h5/negative-h5.json`, `sm-ask-stmt-swap`, `sm-ask-stmt-ret`, `pc-ask-stmt-swap`, `pc-ask-stmt-ret`.
  - Wall time limit of the tool, 300 s (class `timeout_wall`):
    - `pow-block-decode-generated-accept-statement-rax-32-to-48`: `d3dddd1a`, `prysm/go1.26.10/e2e/scal/negative-gen5g.json`, `g5g-pb-acc-stmt-size`.
  - Memory cap kill, 6 GiB (class `killed`): `deposit-data-decode-accept-spec-statement-heap-176-to-175`: `f704f6f0`,
    `prysm/go1.26.10/e2e/scal/negative-h4.json`, `dd-ask-stmt-heap`.
- Two more of the 20 cases had the class `timeout_wall`. They were cases of a separate test ELF.
  That ELF, its Lean proofs and its case file are deleted from the tree, so 18 cases remain.
- Effect: a timeout, a kill, no error or an error outside the designated theorem is not a pass (`../README.md` section 6).
  So these 18 mutants do not show that their theorem depends on the mutated text. The controls of the same groups pass.
- State: open; a decision on the 18 is needed and not taken. Options:
  - cases whose directive an earlier theorem owns: designate the case to that theorem (it then repeats the passing
    sibling case), let a case name the supporting theorems whose errors also count, or mutate a directive that the
    designated theorem proves itself; for the PendingDeposit reject case, keep the identity theorem out of the mutant or
    give the mutant the hand statement with the mutated constant;
  - the stuck `rfl` cases: a stated heartbeat limit for these mutants (if a run without limit ends in a definite `rfl`
    failure), mutations that Lean refutes definitely (for example the same literal in the hand statement, which the accept
    proof checks), or keeping them as recorded limits;
  - the other timeouts, the wall-time case and the memory kill: a per-case limit, a different mutation of the same fault,
    or keeping them as recorded limits;
  - the frame case: it depends on the open item "Kind checks do not bind every parameter".

### A theorem can look closed when it is not

- What: Lean registers a theorem that the kernel rejects as an axiom. `case tag => tac` logs an error, admits the goal and continues.
- How it shows: in a scratch file, segment theorems depended on `sorryAx` although the run looked clean.
- State: rule. A scratch result is closed only when `#print axioms` of every theorem that it uses has no `sorryAx` and does not list the theorem itself.
- A job command must end with the Lean exit code. A command that ends with `echo` hides a failure.

### A generated theorem can carry an extra hypothesis

- What: a proof by `exact` checks only the text after the colon. A hypothesis added before the colon still compiles.
- State: fixed by the `_kind` identity on the full type (commit `094e51e`) and the text check `gen/generator/kindcheck.py`. Neither check alone is enough.

### `lake env lean` does not check that the build is current

- What: `lake env lean` uses `.olean` files without a trace check. A stale file can make a check pass.
- State: fixed in commit `875368f`. The drivers run `lake build --no-build` first and stop on a nonzero exit.

### Negative test time limit killed only the wrapper

- What: the per-case time limit killed only the memory-limit wrapper, not the Lean process tree.
- Where: `gen/tools/memory_limit.py`.
- State: fixed in commit `cc61ebc`.

### Slow proof steps

- What: two proofs spent most of their time in one `omega` side goal each.
- Where: the `bv_omega` of the argument `hLo` of `Codec.root_encode_segment` in `lean/Prysm/Checkpoint/EncodeFastPathFromBytes32Pattern.lean`. The `witness_split` side goals of the Checkpoint cover witnesses.
- State: fixed. `lean/Machine/WitnessSplit.lean` has `witness_split_n` (commit `301300f`). The `Prysm/Checkpoint/EncodeFastPathFromBytes32Pattern.lean` step is a constant-only rewrite (commit `ab43cbb`).

### Limit options without a profiled cause

- What: many files set `maxHeartbeats` or `maxRecDepth` above the default with no written, profiled cause.
  The flat encoder and the 24 other flat types add `maxHeartbeats 16000000` and `4000000` and `maxRecDepth 100000` in many files.
- State: open. They stay until a profile exists or the user accepts them as model-file values. Do not copy them for new work.

### Theorems that end with `⋆ True`

- What: five Checkpoint theorems do not state the rest of memory: `Prysm.Checkpoint.DecodeThenEncode.encode_decoded_receiver`, `Prysm.Checkpoint.Encode.fast_path_spec`, `Prysm.Checkpoint.DecodeThenEncode.round_trip`, `Prysm.Checkpoint.Encode.cover` and `Prysm.Checkpoint.Encode.reject_length_cover`.
- State: disclosed. The component theorems and the `*_framed` cover theorems state the exact frame. The composition has no framed version.
- Related: `Prysm.BeaconBlockHeader.Decode.accept` hides three argument-area slots in one 24-byte existential. They are dead stack only. The statement is not changed.

### Docstrings that say more than their theorem

- What: the docstrings of the `Decode.reject_complete` theorems of `PendingDeposit`, `PowBlock`, `SyncCommitteeMessage` and `PendingConsolidation` say that the code reaches the `ssz.ErrSize` site. The theorem proves only `size ≠ N`.
  A comment in `lean/Prysm/ValidatorBalance/SpecDescription.lean` names the wrong Prysm tree.
- State: open. The fix is a `.lean` edit.

### Unreachable error wraps hold only with the callee specifications

- What: the theorems of an unreachable error wrap state a conditional skip: if the callee returns `rax = 0`, the code skips the wrap.
  Unreachability for every input holds only together with the callee specifications, such as `Prysm.Slot.Decode.accept_function_spec` and `Prysm.ValidatorIndex.Decode.accept_function_spec`.
- State: recorded. The theorems are not changed.

### Hand `Desc` is independent in content, not always in time

- What: for some types, the hand `Desc` is younger than the printed checker `Desc` of the same type.
- Effect: the hand `Desc` copies consensus-specs, but its independence from the checker is by content only.
- State: recorded. A new type must have its hand `Desc` written before the checker `Desc` is printed.

### Replayed review mutants carry earlier reference names

- What: `gen/desc/test_desc.py prepare` replays the review sources `gen/desc/review/r1_mutants.py`, `r2_mutants.py` and
  `r3_mutants.py` unchanged. Their mutants set `reference` to earlier names (`Fv1.scDesc`, `Fv1.luDesc`, ...); the checker
  table names the present `Spec` names.
- Effect: such a mutant fails at the reference check because of the name alone. `test_desc.py evaluate` asks only for a
  FAIL, so the case still counts as expected, but three mutants no longer test their own defect: `n10-ref-trailing-space`
  and `q27-ref-trailing-space` (a trailing space after a right name), and `q46-escaped-key`, whose replacement of the
  reference `Fv1.luDesc` by null matches nothing.
- Where: `gen/desc/review/r2_mutants.py` (`n10-ref-trailing-space`, reference `Fv1.luDesc`, now `Spec.listU64Desc`) and
  `r3_mutants.py` (`q27-ref-trailing-space`, reference `Fv1.scDesc`, now `Spec.scalarsDesc`; `q46-escaped-key`, reference `Fv1.luDesc`).
- State: open. The review sources are records, copied unchanged from the review. A fix translates the names in
  `test_desc.py` and needs a checker run with Lean.

### A code directory is not a Lake input

- What: a Lean module of a separate test ELF included `.S` files from a directory that `lean/lakefile.toml` did not declare as an input.
  A change in such a file did not make Lake build the proofs again.
- Where: the link set `prysm/go1.26.10/link-set` is an input.
  `ElfData.PrysmTarget.typeDeposit_Data_addr` comes from the data include of its data file. `gen/checks/deposit_data_include_check.py` checks this.
- State: closed. The module and the directory of that test ELF are deleted from the tree. Git history keeps them.

### Inventory script trusts its method list

- What: `gen/tools/proof_inventory.py run` trusts `prysm/go1.26.10/ssz-methods.json` for methods without a converted `.S` file. Only the `methods` mode and a `cmp` bind that file to the ELF.
  A development type without a mapping row ends in a `KeyError`, not in a FAIL line.
  19 mapped names are not in the `#print axioms` hand list `gen/axioms-lists/flat-fixed-size-types.lean`. `gen/tools/inventory_decls.lean` checks their axioms on every run.
- State: open.

### Open checker items of the flat encoder generator

- The macro `encoder_address_equation` is declared at the root level (`lean/Codec/EncodeFieldHelpers.lean`).
- A broken checker copy fails with a `KeyError`, not with a check result.
- The IR reader of the encoder generator accepts any untagged 8-byte field as `uint64`.
- The negative tests that compare the IR with the code change one theorem only. There are no whole-file mutants.
- `prysm/go1.26.10/evidence/generator-cases/encode-spec/layout_recomputation.py` is not a step of a gate script.
- State: open. Each needs a checker or test change.

### Paths that the proofs do not cover

- The stack growth path and the write barrier path of every function. The premises exclude them.
- The encoder growth branches (see the growslice entry), the length rejects with a small capacity, and the `moveSliceNoCapNoScan` branch of `PowBlock`, `HistoricalSummary` and `SigningData`.
- The frame separation premise of the encoders is not justified for every Go caller.
- The `IndexedAttestation` alignment and overflow rejects are proved only with the added premise that the error word is not zero.
- State: open. `prysm/proof-inventory.md` lists the paths not proved for each method.

### Recursion depth limits without a located cause

- What: four witness examples raise `maxRecDepth` and the cause is not known. The rule asks for a profiled cause for each raised limit.
- Where: `lean/Prysm/DataColumnsByRootIdentifier/WitnessEncodeFastPath.lean` (one place, limit 4000) and `lean/Prysm/DataColumnsByRootIdentifier/WitnessEncodeGrowFirstSite.lean` (three places, limit 8000).
- How it shows: the examples fail at 512 and at 2000. `WitnessEncodeGrowFirstSite.lean` also fails at 4000. The comment at each place says that the cause is not located.
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

- What: the contracts come from a reading of the Go 1.26.3 runtime source. A source comparison (`gen/checks/runtime_diff.py`) found the functions behind each contract unchanged in Go 1.26.10.
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

- What: some generated records contain absolute paths of the original machine, for example `prysm/go1.26.10/evidence/negative/result.json`.
  Two Python bytecode files in git history contain container paths. They are not in the current tree.
- How it shows: `git grep -nE "/workspace|fve2e-" -- fv/kraken ':!fv/kraken/lean/.lake'`.
- State: open. The user decides how to treat the history before publication.

### Two tracked files differ only in case

- What: `prysm/INVENTORY.json` and `prysm/inventory.json` were both tracked.
- Effect: on a file system that ignores case, only one exists, and `git status` shows a change that is not real.
- State: fixed. The per-method table is now `prysm/proof-inventory.json` and `prysm/proof-inventory.md`.
