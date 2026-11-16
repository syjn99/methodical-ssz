#!/usr/bin/env python3
"""Generator tests for `generator.py decoder` (default mode, `--steps`, `--whole-accept`). Tests that can fail.

usage: decoder_test.py <work-dir> <result.json>      (run from anywhere; one gated job; Python 3 stdlib)
exit 0 = every case has its expected exit code and output; 1 = a case differs; 2 = usage

Every case runs `gen/generator/generator.py` of the working tree. Mutants are written to <work-dir>, nothing in the repository.
default-mode cases (ids `mutant-*`, on the committed Eth1Data `.S` and IR):
 - mutants of the `.S` (one line changed or removed, found by exact text at a 1-based line):
   wrong length, missing memmove, an add on another register, offset-0 form with a wrong destination,
   offset-0 form at a non-zero SSZ offset, broken head of the first field, unrecognised directive in place
   of the add. Expected exit 2 (no field matches) or 3 (some fields match), and 0 bytes on stdout always.

step cases (`decoder --steps`; ids `steps-*`; mutated `.S` / IR copies in <work-dir> only):
 - steps-new-*: `--steps` on 10 real types: exit 0 twice (AttestationData: 3), identical, the expected
   covered fields; on exit 0 `kindcheck.py` PASS and = the committed file `Prysm/<Type>/GeneratedDecodeSteps.lean` when it exists.
 - adversarial inputs for the dataflow (SyncCommitteeMessage, PendingConsolidation, PendingPartialWithdrawal,
   Eth1Data): a receiver / argument register clobbered between set-up and block, set-up moves in another VALID order
   (covered) and in an invalid order (refused), an extra harmless move and a fall-through label (covered), `nop` at
   start / middle / end / doubled (covered), a `nop` replaced by `cld` (one byte, no step lemma: refused),
   displacements off by 8 against the IR (refused), source / destination registers swapped at the call (refused),
   an unknown callee in the code or in the IR (refused), a label inside a call / segment window (refused), field order
   wrong in the IR or the code (refused), a receiver register outside the lemma's set, a reload from another slot,
   the buffer slot overwritten, a store through an unknown base, an indexed / rip operand, an immediate store, an rsp
   change. Expected: exit 0 with every field covered (`kindcheck.py` PASS), or exit 3 with the stated covered fields,
   0 bytes on stdout unless exit 0; the summary's miss class is checked where stated. A covered mutant is a text result only (no Lean constant exists for
   mutated code): its theorems carry the mutated code's indices, never a parameter of the unmutated code.
 - steps-<what the input does>, table STEP_STACK_AND_SETUP_MUT (`rv` edits): seven inputs that do not
   establish the block entry must be refused (an 8-byte stack store overlapping a tracked
   slot: steps-stack-store-overlaps-*; a head that is not the `decode_prologue_segment` prologue: steps-head-spill-before-push,
   steps-head-no-frame), and steps-head-overlapping-spills too; steps-head-extra-nop is a head miss of class padding;
   steps-callee-source-offset-zero class other; stores to the return-address slot or below rsp, writes to r14 / rbp
   refused; the ten valid variants stay covered. steps-store-after-last-field is refused by the epilogue rule (exit 2).
 - table STEP_SIZE_CALLEE_EPILOGUE_MUT: the head size immediate must equal the IR SSZ fixed size
   (steps-head-size-*: exit 2, class other); a callee that is not the IR field's overlay type is refused
   (ValidatorIndex field calling Epoch.UnmarshalSSZ and the reverse); after the last field event only the plain return
   (`mov d(%rsp),%rax|%rbx`, `xor`, nops, labels, forward jmp, `add $F,%rsp; pop %rbp; retq`) is accepted: a store, a
   call or a wrong frame size there gives exit 2 with every field `reached` and not covered; a nop there stays covered.
   Every `--steps` case also checks the summary flag `reached` (true up to the first uncovered field, false after it,
   false for every field on a head miss); on exit 2 the summary lists every field.
 - steps-tail-*, table STEP_TAIL_JUMP_MUT: a `jmp` after the last field event to a label that is not in the file
   (`jmp runtime.abort`, `jmp *%rdx`, a tail `jmp` to Slot.UnmarshalSSZ): exit 2, every field not covered and
   `reached`.
 - steps-fail-closed-*: fail-closed. A harness (written to <work-dir>, run as one process per type on Eth1Data,
   SyncCommitteeMessage, PendingPartialWithdrawal) imports the working-tree `generator.py`, monkeypatches it and calls
   `main()`: an unexpected exception, a plain `StepStop` and `SystemExit(0)` injected in the head (`step_head`), at every
   `step_parse` / `step_label_index` call of the walk (each field, by the walk's current field), at every theorem-text
   call, in the epilogue (`step_epilogue` raising, or returning None / True / another value than STEP_EPILOGUE_OK), a walk
   that returns every field with a stop or without an end index, and an inner run that returns a text without the
   flags. Expected for every injection: exit 2 or 3 (exit 2 for an unexpected exception and SystemExit), 0 bytes on
   stdout, the summary's exit equal, fewer fields covered than the IR has. Control: no injection, exit 0.
whole-accept cases (`decoder --whole-accept`; ids `whole-accept-*`; mutated `.S` / IR copies in <work-dir> only):
 - whole-accept-new-*: `--whole-accept` on PendingDeposit, SyncCommitteeMessage, VoluntaryExit, PowBlock, ValidatorBalance: exit 0 twice,
   identical, every whole-accept theorem with its kind line, `kindcheck.py` PASS (rule 12: kind parameters recomputed from the
   IR and the `.S`); PendingPartialWithdrawal (interleaved fields) and AttestationData (nested fields): exit 2, 0 bytes.
 - adversarial inputs, each expected exit 2 with 0 bytes on stdout and `accept_generated: false` in the summary (no
   accept theorem): every class of the step rules (stack-store overlap / misaligned store, head variants, size
   immediate, epilogue jump to a missing label, truncated file, callee of another overlay type) and the whole-accept rules
   (spill to a non-home slot, a register spilled twice, an extra `rcx` spill, `dB != F + 24`, an `xor` epilogue in a
   frame other than 0x20, an epilogue load of a non-zero slot, a `nop` inside the accept epilogue, a malformed
   size-error block, a stack store of an input value, a load from a stack slot outside the layout, interleaved
   fields); statement-level IR mutants (a wrong Go offset, a wrong size, the field order swapped, a Go offset that
   the code matches but that is not the kind's running sum). Valid variants (an extra harmless move, another valid
   set-up order): exit 0 and kindcheck PASS.
 - whole-accept-fail-closed-*: fail-closed. A harness imports the working-tree `generator.py`, takes its `whole-accept` module (`whole_accept_module()`),
   monkeypatches it and calls `main()`: an unexpected exception, SystemExit(0) and a WholeAcceptRefuse injected in the step
   front end, the recomputed walk / epilogue, the head / epilogue / reject specification, every step rendering, every
   theorem renderer, and results without the flags (a missing kind line, an inner run that sets no flag). Expected for
   every injection: exit 2, 0 bytes on stdout, summary exit 2 and `accept_generated: false`. Control: exit 0.
"""
import json
import pathlib
import subprocess
import sys

HERE = pathlib.Path(__file__).resolve().parent
KR = HERE.parent.parent
S = "prysm/go1.26.10/link-set/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Eth1Data.UnmarshalSSZ.S"
ARGS = ["--const", "unmarshalSSZ", "--ir", "prysm/ir/ir-mainnet.json", "--type", "v1alpha1.Eth1Data",
        "--prefix", "Decode.generated_root", "--imports", "Codec.Bytes32Decode,Codec.Bytes32DecodeOffsetZero,Prysm.Eth1Data.Code", "--open", "Prysm.Eth1Data.Code"]

# (id, what, 1-based line, old text, new text or None = delete, expected exit, expected MATCH fields)
MUTANTS = [
    ("mutant-memmove-length", "wrong length: memmove count 0x10 in the offset-0 DepositRoot block", 31,
     "  mov $0x20,%ecx", "  mov $0x10,%ecx", 3, ["BlockHash"]),
    ("mutant-no-memmove", "missing memmove: the DepositRoot memmove call removed", 32,
     "  callq runtime.memmove", None, 3, ["BlockHash"]),
    ("mutant-add-register", "an add with a different register: BlockHash `add $0x28,%rsi`", 68,
     "  add $0x28,%rbx", "  add $0x28,%rsi", 3, ["DepositRoot"]),
    ("mutant-offset-zero-destination", "offset-0 form with a wrong destination: DepositRoot pointer stored at 0x10(%rdx)", 29,
     "  mov %rax,0x8(%rdx)", "  mov %rax,0x10(%rdx)", 3, ["BlockHash"]),
    ("mutant-offset-zero-at-offset-40", "offset-0 form at SSZ offset 40: the BlockHash add removed", 68,
     "  add $0x28,%rbx", None, 3, ["DepositRoot"]),
    ("mutant-both-fields", "both fields broken: DepositRoot length and the BlockHash add register", None,
     None, None, 2, []),
    ("mutant-offset-zero-source-register", "offset-0 form with the buffer reloaded into rsi (not the memmove source register)", 30,
     "  mov 0x38(%rsp),%rbx", "  mov 0x38(%rsp),%rsi", 3, ["BlockHash"]),
]


def run(argv, cwd):
    p = subprocess.run(argv, cwd=cwd, capture_output=True)
    return p.returncode, p.stdout, p.stderr.decode("utf-8", "replace")


def mutate(lines, line, old, new):
    if lines[line - 1] != old:
        raise SystemExit(f"mutant base mismatch at line {line}: {lines[line - 1]!r} != {old!r}")
    return lines[:line - 1] + ([] if new is None else [new]) + lines[line:]


IR = "prysm/ir/ir-mainnet.json"


def ir_edit(ir, tname, fn):
    """A copy of the IR with the field list of type `tname` (package suffix + name) changed by `fn`."""
    d = json.loads(ir)
    pkg, name = tname.rsplit(".", 1)
    for c in d["configs"]:
        for t in c.get("types", []):
            if t.get("name") == name and t.get("package", "").endswith("/" + pkg):
                fn(t)
    return json.dumps(d)


def ir_size(field, size):
    def fn(t):
        for f in t["ir"]["fields"]:
            if f["key"] == field:
                f["v"]["size"] = size
                f["v"]["fixed_size"] = size
    return fn


def ir_swap(a, b):
    def fn(t):
        fs = t["ir"]["fields"]
        i, j = [k for k, f in enumerate(fs) if f["key"] in (a, b)]
        fs[i], fs[j] = fs[j], fs[i]
    return fn


def edits(lines, eds):
    """Apply (1-based line, old text, new text or None = delete) edits, highest line first."""
    for line, old, new in sorted(eds, key=lambda e: -e[0]):
        lines = mutate(lines, line, old, new)
    return lines


PRIM = "github.com_OffchainLabs_prysm_v7_consensus_types_primitives."


def ir_overlay_name(field, name):
    def fn(t):
        for f in t["ir"]["fields"]:
            if f["key"] == field:
                f["v"]["name"] = name
                f["v"]["delegated_to"]["name"] = name
    return fn


PN = "github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1."


def step_case(sdir, tname, const, mod, fields, cov=None):
    return dict(S=f"prysm/go1.26.10/link-set/{sdir}/{PN}{tname}.UnmarshalSSZ.S", type=f"v1alpha1.{tname}",
                committed=f"lean/Prysm/{tname}/GeneratedDecodeSteps.lean", args=["--const", const, "--prefix", "Decode.generated_step",
                                                                               "--imports", mod, "--open", f"Prysm.{tname}.Code"],
                fields=fields, cov=fields if cov is None else cov)


STEP_CASES = {
    "Checkpoint": step_case("norm", "Checkpoint", "unmarshalSSZ", "Prysm.Checkpoint.Code", ["Epoch", "Root"]),
    "AttestationData": step_case("norm", "AttestationData", "unmarshalSSZ", "Prysm.AttestationData.Code",
              ["Slot", "CommitteeIndex", "BeaconBlockRoot", "Source", "Target"], ["Slot", "CommitteeIndex", "BeaconBlockRoot"]),
    "BeaconBlockHeader": step_case("norm", "BeaconBlockHeader", "unmarshalSSZ", "Prysm.BeaconBlockHeader.Code",
              ["Slot", "ProposerIndex", "ParentRoot", "StateRoot", "BodyRoot"]),
    "Eth1Data": step_case("norm", "Eth1Data", "unmarshalSSZ", "Prysm.Eth1Data.Code",
              ["DepositRoot", "DepositCount", "BlockHash"]),
    "BlobIdentifier": step_case("norm", "BlobIdentifier", "unmarshalSSZ", "Prysm.BlobIdentifier.Code", ["BlockRoot", "Index"]),
    "DepositMessage": step_case("norm", "DepositMessage", "unmarshalSSZ", "Prysm.BlobIdentifier.Code",
              ["PublicKey", "WithdrawalCredentials", "Amount"]),
    "Deposit_Data": step_case("norm", "Deposit_Data", "unmarshalSSZ", "Prysm.Deposit_Data.Code",
              ["PublicKey", "WithdrawalCredentials", "Amount", "Signature"]),
    "PendingPartialWithdrawal": step_case("norm", "PendingPartialWithdrawal", "unmarshalSSZ", "Prysm.Deposit_Data.Code",
              ["Index", "Amount", "WithdrawableEpoch"]),
    "SyncCommitteeMessage": step_case("norm", "SyncCommitteeMessage", "unmarshalSSZ", "Prysm.SyncCommitteeMessage.Code",
              ["Slot", "BlockRoot", "ValidatorIndex", "Signature"]),
    "PendingConsolidation": step_case("norm", "PendingConsolidation", "unmarshalSSZ", "Prysm.SyncCommitteeMessage.Code",
              ["SourceIndex", "TargetIndex"]),
}
SYNC_COMMITTEE_MESSAGE_FIELDS, PENDING_CONSOLIDATION_FIELDS, PENDING_PARTIAL_WITHDRAWAL_FIELDS = STEP_CASES["SyncCommitteeMessage"]["fields"], STEP_CASES["PendingConsolidation"]["fields"], STEP_CASES["PendingPartialWithdrawal"]["fields"]
SYNC_COMMITTEE_MESSAGE_LABEL = "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommitteeMessage.UnmarshalSSZ_"


def sync_committee_message_validator_index_setup(new):
    """SyncCommitteeMessage.ValidatorIndex set-up (lines 83–88) replaced by the lines `new`."""
    old = ["  mov 0x78(%rsp),%rbx", "  add $0x28,%rbx", "  mov 0x88(%rsp),%rdi", "  add $-0x28,%rdi", "  add $0x28,%rax",
           "  mov $0x8,%ecx"]

    def fn(L):
        assert L[82:88] == old, L[82:88]
        return L[:82] + new + L[88:]
    return fn


VALIDATOR_INDEX_SETUP = ["  mov 0x78(%rsp),%rbx", "  add $0x28,%rbx", "  mov 0x88(%rsp),%rdi", "  add $-0x28,%rdi", "  add $0x28,%rax",
      "  mov $0x8,%ecx"]
# (id, what, type key, .S edits or function, IR edit, exit, covered, miss class of the first uncovered field or None)
STEP_MUT = [
    ("steps-clobber-rax", "ValidatorIndex: `mov %rdx,%rax` after `add $0x28,%rax` (receiver clobbered before the call)", "SyncCommitteeMessage",
     sync_committee_message_validator_index_setup(VALIDATOR_INDEX_SETUP[:5] + ["  mov %rdx,%rax"] + VALIDATOR_INDEX_SETUP[5:]), None, 3, SYNC_COMMITTEE_MESSAGE_FIELDS[:2], "register"),
    ("steps-clobber-rbx-callee-arg", "ValidatorIndex: `mov 0x88(%rsp),%rbx` after the rbx set-up (source register clobbered)", "SyncCommitteeMessage",
     sync_committee_message_validator_index_setup(VALIDATOR_INDEX_SETUP[:2] + ["  mov 0x88(%rsp),%rbx"] + VALIDATOR_INDEX_SETUP[2:]), None, 3, SYNC_COMMITTEE_MESSAGE_FIELDS[:2], None),
    ("steps-order-valid", "ValidatorIndex: `add $0x28,%rax` first, then the rbx / rdi set-up (another valid order)", "SyncCommitteeMessage",
     sync_committee_message_validator_index_setup([VALIDATOR_INDEX_SETUP[4]] + VALIDATOR_INDEX_SETUP[:4] + [VALIDATOR_INDEX_SETUP[5]]), None, 0, SYNC_COMMITTEE_MESSAGE_FIELDS, None),
    ("steps-order-valid-ecx-first", "ValidatorIndex: `mov $0x8,%ecx` first (another valid order)", "SyncCommitteeMessage",
     sync_committee_message_validator_index_setup([VALIDATOR_INDEX_SETUP[5]] + VALIDATOR_INDEX_SETUP[:5]), None, 0, SYNC_COMMITTEE_MESSAGE_FIELDS, None),
    ("steps-order-invalid", "ValidatorIndex: `add $0x28,%rbx` before `mov 0x78(%rsp),%rbx` (the load overwrites the add)", "SyncCommitteeMessage",
     sync_committee_message_validator_index_setup([VALIDATOR_INDEX_SETUP[1], VALIDATOR_INDEX_SETUP[0]] + VALIDATOR_INDEX_SETUP[2:]), None, 3, SYNC_COMMITTEE_MESSAGE_FIELDS[:2], "set-up order"),
    ("steps-extra-harmless", "ValidatorIndex: an extra `mov %rdi,%rsi` in the set-up", "SyncCommitteeMessage",
     sync_committee_message_validator_index_setup(VALIDATOR_INDEX_SETUP[:4] + ["  mov %rdi,%rsi"] + VALIDATOR_INDEX_SETUP[4:]), None, 0, SYNC_COMMITTEE_MESSAGE_FIELDS, None),
    ("steps-label-fallthrough", "ValidatorIndex: a fall-through label between two set-up moves (label step)", "SyncCommitteeMessage",
     sync_committee_message_validator_index_setup(VALIDATOR_INDEX_SETUP[:2] + [f"{SYNC_COMMITTEE_MESSAGE_LABEL}zz:"] + VALIDATOR_INDEX_SETUP[2:]), None, 0, SYNC_COMMITTEE_MESSAGE_FIELDS, None),
    ("steps-nop-start", "ValidatorIndex: `nop` before the first set-up move", "SyncCommitteeMessage", sync_committee_message_validator_index_setup(["  nop"] + VALIDATOR_INDEX_SETUP), None, 0, SYNC_COMMITTEE_MESSAGE_FIELDS, None),
    ("steps-nop-middle", "ValidatorIndex: `nop` between `add $0x28,%rbx` and `mov 0x88(%rsp),%rdi`", "SyncCommitteeMessage",
     sync_committee_message_validator_index_setup(VALIDATOR_INDEX_SETUP[:2] + ["  nop"] + VALIDATOR_INDEX_SETUP[2:]), None, 0, SYNC_COMMITTEE_MESSAGE_FIELDS, None),
    ("steps-nop-end", "ValidatorIndex: `nop` between `mov $0x8,%ecx` and the `callq`", "SyncCommitteeMessage", sync_committee_message_validator_index_setup(VALIDATOR_INDEX_SETUP + ["  nop"]), None, 0, SYNC_COMMITTEE_MESSAGE_FIELDS, None),
    ("steps-nop-doubled-after-call", "ValidatorIndex: two `nop`s between the `callq` and `test`", "SyncCommitteeMessage",
     [(90, "  test %rax,%rax", "  nop\n  nop\n  test %rax,%rax")], None, 0, SYNC_COMMITTEE_MESSAGE_FIELDS, None),
    ("steps-nop-in-segment", "Signature: `nop` before `callq runtime.memmove` and two before makeslice", "SyncCommitteeMessage",
     [(141, "  callq runtime.memmove", "  nop\n  callq runtime.memmove"), (124, "  nop", "  nop\n  nop")], None, 0, SYNC_COMMITTEE_MESSAGE_FIELDS, None),
    ("steps-cld-for-nop-seg", "Signature: the `nop` before makeslice replaced by `cld` (one byte, no step lemma)", "SyncCommitteeMessage",
     [(124, "  nop", "  cld")], None, 3, SYNC_COMMITTEE_MESSAGE_FIELDS[:3], "new directive form"),
    ("steps-cld-for-nop-call", "TargetIndex: the `nop` after the `callq` replaced by `cld`", "PendingConsolidation",
     [(57, "  nop", "  cld")], None, 3, PENDING_CONSOLIDATION_FIELDS[:1], "new directive form"),
    ("steps-cld-in-setup", "TargetIndex: `cld` in the set-up (no step lemma)", "PendingConsolidation",
     [(53, "  mov 0x58(%rsp),%rax", "  cld\n  mov 0x58(%rsp),%rax")], None, 3, PENDING_CONSOLIDATION_FIELDS[:1], "new directive form"),
    ("steps-disp-f-off8", "ValidatorIndex: `add $0x30,%rax` (Go offset 0x28 in the IR)", "SyncCommitteeMessage",
     sync_committee_message_validator_index_setup(VALIDATOR_INDEX_SETUP[:4] + ["  add $0x30,%rax"] + VALIDATOR_INDEX_SETUP[5:]), None, 3, SYNC_COMMITTEE_MESSAGE_FIELDS[:2], "other"),
    ("steps-disp-src-off8", "ValidatorIndex: `add $0x30,%rbx` (SSZ offset 0x28 in the IR)", "SyncCommitteeMessage",
     sync_committee_message_validator_index_setup([VALIDATOR_INDEX_SETUP[0], "  add $0x30,%rbx"] + VALIDATOR_INDEX_SETUP[2:]), None, 3, SYNC_COMMITTEE_MESSAGE_FIELDS[:2], None),
    ("steps-swapped-call-regs", "WithdrawableEpoch: `mov %rsi,%rbx; mov %rdx,%rax` (source / destination swapped)", "PendingPartialWithdrawal",
     [(57, "  mov %rsi,%rax", "  mov %rsi,%rbx"), (58, "  mov %rdx,%rbx", "  mov %rdx,%rax")], None, 3, PENDING_PARTIAL_WITHDRAWAL_FIELDS[:2], "register"),
    ("steps-unknown-callee-code", "TargetIndex: `callq …Gwei.UnmarshalSSZ` in the code (IR ValidatorIndex)", "PendingConsolidation",
     [(56, f"  callq {PRIM}ValidatorIndex.UnmarshalSSZ", f"  callq {PRIM}Gwei.UnmarshalSSZ")], None, 3, PENDING_CONSOLIDATION_FIELDS[:1], None),
    ("steps-unknown-callee-ir", "TargetIndex: callee Gwei.UnmarshalSSZ in code and IR (no proved spec)", "PendingConsolidation",
     [(56, f"  callq {PRIM}ValidatorIndex.UnmarshalSSZ", f"  callq {PRIM}Gwei.UnmarshalSSZ")],
     ir_overlay_name("TargetIndex", "Gwei"), 3, PENDING_CONSOLIDATION_FIELDS[:1], "new field kind"),
    ("steps-label-in-call-window", "TargetIndex: the `nop` after the `callq` replaced by a label (inside the call window)", "PendingConsolidation",
     [(57, "  nop", "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingConsolidation.UnmarshalSSZ_zz:")],
     None, 3, PENDING_CONSOLIDATION_FIELDS[:1], "other"),
    ("steps-label-in-seg-window", "Signature: a label between `xor %ebx,%ebx` and `mov $0x60,%ecx` (inside the segment window)", "SyncCommitteeMessage",
     [(123, "  mov $0x60,%ecx", f"{SYNC_COMMITTEE_MESSAGE_LABEL}zz:\n  mov $0x60,%ecx")], None, 3, SYNC_COMMITTEE_MESSAGE_FIELDS[:3], "other"),
    ("steps-ir-order-swap", "IR order Amount / WithdrawableEpoch swapped (wrong field order)", "PendingPartialWithdrawal",
     [], ir_swap("Amount", "WithdrawableEpoch"), 3, PENDING_PARTIAL_WITHDRAWAL_FIELDS[:1], "set-up order"),
    ("steps-code-order-swap", "Eth1Data code: the DepositCount read moved after the BlockHash segment", "Eth1Data",
     lambda L: L[:47] + L[50:86] + L[47:50] + L[86:], None, 3, ["DepositRoot"], "set-up order"),
    ("steps-ry-rbx", "BlockRoot: receiver reloaded into rbx after memmove (not in the lemma's set)", "SyncCommitteeMessage",
     [(68, "  mov 0x70(%rsp),%rax", "  mov 0x70(%rsp),%rbx"), (69, "  movq $0x20,0x18(%rax)", "  movq $0x20,0x18(%rbx)"),
      (70, "  movq $0x20,0x20(%rax)", "  movq $0x20,0x20(%rbx)")], None, 3, SYNC_COMMITTEE_MESSAGE_FIELDS[:1], "register"),
    ("steps-reload-other-slot", "BlockRoot: second receiver reload from 0x68(%rsp)", "SyncCommitteeMessage",
     [(68, "  mov 0x70(%rsp),%rax", "  mov 0x68(%rsp),%rax")], None, 3, SYNC_COMMITTEE_MESSAGE_FIELDS[:1], "other"),
    ("steps-buffer-slot-overwritten", "Signature: `mov %rax,0x78(%rsp)` before the segment (buffer slot overwritten)", "SyncCommitteeMessage",
     [(119, "  mov %rbx,0x30(%rsp)", "  mov %rbx,0x30(%rsp)\n  mov %rax,0x78(%rsp)")], None, 3, SYNC_COMMITTEE_MESSAGE_FIELDS[:3], "register"),
    ("steps-store-unknown-base", "ValidatorIndex: `mov %rax,0x8(%rcx)` in the set-up (store through an unknown base)", "SyncCommitteeMessage",
     sync_committee_message_validator_index_setup(VALIDATOR_INDEX_SETUP[:2] + ["  mov %rax,0x8(%rcx)"] + VALIDATOR_INDEX_SETUP[2:]), None, 3, SYNC_COMMITTEE_MESSAGE_FIELDS[:2], "register"),
    ("steps-indexed-operand", "Amount: `mov 0x8(%rbx,%rcx,1),%r8` (index operand)", "PendingPartialWithdrawal",
     [(55, "  mov 0x8(%rbx),%r8", "  mov 0x8(%rbx,%rcx,1),%r8")], None, 3, PENDING_PARTIAL_WITHDRAWAL_FIELDS[:1], "new directive form"),
    ("steps-imm-store", "TargetIndex: `movq $0x0,0x40(%rsp)` in the set-up (immediate store)", "PendingConsolidation",
     [(53, "  mov 0x58(%rsp),%rax", "  movq $0x0,0x40(%rsp)\n  mov 0x58(%rsp),%rax")], None, 3, PENDING_CONSOLIDATION_FIELDS[:1], "new directive form"),
    ("steps-rip-load", "TargetIndex: `mov ssz.ErrSize(%rip),%rdi` in the set-up", "PendingConsolidation",
     [(53, "  mov 0x58(%rsp),%rax", "  mov ssz.ErrSize(%rip),%rdi\n  mov 0x58(%rsp),%rax")], None, 3, PENDING_CONSOLIDATION_FIELDS[:1], "new directive form"),
    ("steps-rsp-change", "TargetIndex: `add $0x8,%rsp` in the set-up", "PendingConsolidation",
     [(53, "  mov 0x58(%rsp),%rax", "  add $0x8,%rsp\n  mov 0x58(%rsp),%rax")], None, 3, PENDING_CONSOLIDATION_FIELDS[:1], None),
    ("steps-movi-len-16", "TargetIndex: `mov $0x10,%ecx` (rcx = 16 at the call)", "PendingConsolidation",
     [(55, "  mov $0x8,%ecx", "  mov $0x10,%ecx")], None, 3, PENDING_CONSOLIDATION_FIELDS[:1], None),
    ("steps-u64-src-disp", "Amount: `mov 0x10(%rbx),%r8` (SSZ offset 8 in the IR)", "PendingPartialWithdrawal",
     [(55, "  mov 0x8(%rbx),%r8", "  mov 0x10(%rbx),%r8")], None, 3, PENDING_PARTIAL_WITHDRAWAL_FIELDS[:1], "other"),
    ("steps-u64-dst-disp", "Amount: store to 0x18(%rax), the Go offset of WithdrawableEpoch", "PendingPartialWithdrawal",
     [(56, "  mov %r8,0x10(%rax)", "  mov %r8,0x18(%rax)")], None, 3, PENDING_PARTIAL_WITHDRAWAL_FIELDS[:1], "set-up order"),
]



def rv(eds):
    """Edits of an input `.S` file: (1-based line, old suffix, new); new None =
    delete, a list = replace by several, ("before", [..]) = insert before; directives indented, labels not."""
    def fn(L):
        L = list(L)
        for ln, old, new in sorted(eds, key=lambda x: -x[0]):
            assert L[ln - 1].strip().endswith(old) or L[ln - 1].strip() == old, (ln, L[ln - 1], old)
            ind = lambda xs: ["  " + x if not x.endswith(":") else x for x in xs]
            if new is None:
                del L[ln - 1]
            elif isinstance(new, tuple):
                L[ln - 1:ln - 1] = ind(new[1])
            elif isinstance(new, list):
                L[ln - 1:ln] = ind(new)
            else:
                L[ln - 1] = "  " + new
        return L
    return fn


ETH1_DATA_FIELDS = STEP_CASES["Eth1Data"]["fields"]
SYNC_COMMITTEE_MESSAGE_LABEL_STEM = SYNC_COMMITTEE_MESSAGE_LABEL[:-1]
# Inputs that stress the stack-store, head and set-up rules. Seven inputs in which
# the code does not establish the block entry must be refused; the eleven valid variants stay covered; plus
# head-miss classes and the frame / goroutine register rule.
STEP_STACK_AND_SETUP_MUT = [
    ("steps-stack-store-overlaps-buffer-slot", "8-byte stack store at 0x7c overlaps the buffer slot 0x78", "SyncCommitteeMessage",
     rv([(83, "mov 0x78(%rsp),%rbx", ("before", ["mov %rdi,0x7c(%rsp)"]))]), None, 3, SYNC_COMMITTEE_MESSAGE_FIELDS[:2], "other"),
    ("steps-stack-store-overlaps-buffer-slot-with-nops", "the same store with nops around it", "SyncCommitteeMessage",
     rv([(83, "mov 0x78(%rsp),%rbx", ("before", ["nop", "mov %rdi,0x7c(%rsp)", "nop"])),
         (88, "mov $0x8,%ecx", ("before", ["nop"]))]), None, 3, SYNC_COMMITTEE_MESSAGE_FIELDS[:2], "other"),
    ("steps-stack-store-overlaps-buffer-slot-eth1-data", "8-byte stack store at 0x3c overlaps the buffer slot 0x38", "Eth1Data",
     rv([(48, "mov 0x38(%rsp),%rsi", ("before", ["mov %rdx,0x3c(%rsp)"]))]), None, 3, ETH1_DATA_FIELDS[:1], "other"),
    ("steps-stack-store-overlaps-receiver-slot", "8-byte stack store at 0x34 overlaps the receiver slot 0x30 before the segment", "Eth1Data",
     rv([(51, "lea type__+387072(%rip),%rax", ("before", ["mov %rsi,0x34(%rsp)"]))]), None, 3, ETH1_DATA_FIELDS[:2], "other"),
    ("steps-stack-store-overlaps-buffer-slot-from-below", "8-byte stack store at 0x34 overlaps the buffer slot 0x38 from below", "Eth1Data",
     rv([(48, "mov 0x38(%rsp),%rsi", ("before", ["mov %rdx,0x34(%rsp)"]))]), None, 3, ETH1_DATA_FIELDS[:1], "other"),
    ("steps-head-spill-before-push", "head: receiver spilled before `push %rbp`", "SyncCommitteeMessage",
     rv([(5, "push %rbp", ("before", ["mov %rax,0x70(%rsp)"])), (9, "nop", None), (12, "mov %rax,0x70(%rsp)", None)]),
     None, 2, [], "other"),
    ("steps-head-no-frame", "head: `sub $0x60,%rsp` replaced by `nop` (frame never allocated)", "SyncCommitteeMessage",
     rv([(7, "sub $0x60,%rsp", "nop")]), None, 2, [], "other"),
    ("steps-head-overlapping-spills", "head: a spill at 0x74 and `mov %rcx,0x70(%rsp)` at directive 8", "SyncCommitteeMessage",
     rv([(9, "nop", "mov %rcx,0x70(%rsp)"), (12, "mov %rax,0x70(%rsp)", "mov %rax,0x74(%rsp)")]), None, 2, [], "other"),
    ("steps-head-extra-nop", "head: an extra `nop` moves `cmp $size,%rcx` to directive 10 (miss class padding)", "SyncCommitteeMessage",
     rv([(9, "nop", ["nop", "nop"])]), None, 2, [], "padding"),
    ("steps-callee-source-offset-zero", "ValidatorIndex source `add $0x0,%rbx` (a wrong offset is miss class other)", "SyncCommitteeMessage",
     rv([(84, "add $0x28,%rbx", "add $0x0,%rbx")]), None, 3, SYNC_COMMITTEE_MESSAGE_FIELDS[:2], "other"),
    ("steps-receiver-reloaded-after-add", "ValidatorIndex: receiver reloaded after its add (class set-up order)", "SyncCommitteeMessage",
     rv([(87, "add $0x28,%rax", ["add $0x28,%rax", "mov 0x70(%rsp),%rax"])]), None, 3, SYNC_COMMITTEE_MESSAGE_FIELDS[:2], "set-up order"),
    ("steps-store-return-address-slot", "ValidatorIndex: `mov %rdi,0x68(%rsp)` (the return-address slot, frame 0x60)", "SyncCommitteeMessage",
     sync_committee_message_validator_index_setup(VALIDATOR_INDEX_SETUP[:2] + ["  mov %rdi,0x68(%rsp)"] + VALIDATOR_INDEX_SETUP[2:]), None, 3, SYNC_COMMITTEE_MESSAGE_FIELDS[:2], "other"),
    ("steps-store-below-stack-pointer", "ValidatorIndex: `mov %rdi,-0x8(%rsp)` (below rsp)", "SyncCommitteeMessage",
     sync_committee_message_validator_index_setup(VALIDATOR_INDEX_SETUP[:2] + ["  mov %rdi,-0x8(%rsp)"] + VALIDATOR_INDEX_SETUP[2:]), None, 3, SYNC_COMMITTEE_MESSAGE_FIELDS[:2], "other"),
    ("steps-write-goroutine-register", "ValidatorIndex: `mov %rdx,%r14` in the set-up (goroutine register)", "SyncCommitteeMessage",
     sync_committee_message_validator_index_setup(VALIDATOR_INDEX_SETUP[:2] + ["  mov %rdx,%r14"] + VALIDATOR_INDEX_SETUP[2:]), None, 3, SYNC_COMMITTEE_MESSAGE_FIELDS[:2], "other"),
    ("steps-write-frame-pointer", "ValidatorIndex: `lea 0x8(%rax),%rbp` in the set-up (frame pointer)", "SyncCommitteeMessage",
     sync_committee_message_validator_index_setup(VALIDATOR_INDEX_SETUP[:2] + ["  lea 0x8(%rax),%rbp"] + VALIDATOR_INDEX_SETUP[2:]), None, 3, SYNC_COMMITTEE_MESSAGE_FIELDS[:2], "other"),
    # the eleven valid variants (covered)
    ("steps-fall-through-label", "fall-through label in the ValidatorIndex set-up", "SyncCommitteeMessage",
     rv([(87, "add $0x28,%rax", ("before", [SYNC_COMMITTEE_MESSAGE_LABEL_STEM + "_zz:"]))]), None, 0, SYNC_COMMITTEE_MESSAGE_FIELDS, None),
    ("steps-nops-at-25-positions", "nops at 25 positions", "SyncCommitteeMessage",
     rv([(x, "", ("before", ["nop"])) for x in (16, 17, 18, 19, 20, 48, 51, 53, 62, 65, 67, 70, 73, 82, 84, 86, 88, 89, 90,
                                                 91, 119, 126, 141, 147, 156)]), None, 0, SYNC_COMMITTEE_MESSAGE_FIELDS, None),
    ("steps-receiver-spill-and-reload", "spill + reload of the receiver through 0x48(%rsp)", "SyncCommitteeMessage",
     rv([(87, "add $0x28,%rax", ("before", ["mov %rax,0x48(%rsp)", "mov 0x48(%rsp),%rax"]))]), None, 0, SYNC_COMMITTEE_MESSAGE_FIELDS, None),
    ("steps-forward-jump-over-junk", "forward jmp over a junk directive", "SyncCommitteeMessage",
     rv([(87, "add $0x28,%rax", ("before", ["jmp " + SYNC_COMMITTEE_MESSAGE_LABEL_STEM + "_yy", "xor %eax,%eax", SYNC_COMMITTEE_MESSAGE_LABEL_STEM + "_yy:"]))]), None, 0, SYNC_COMMITTEE_MESSAGE_FIELDS, None),
    ("steps-count-register-16-minus-8", "rcx = 16 - 8", "SyncCommitteeMessage", rv([(88, "mov $0x8,%ecx", ["mov $0x10,%ecx", "add $-0x8,%rcx"])]), None, 0, SYNC_COMMITTEE_MESSAGE_FIELDS, None),
    ("steps-value-moved-through-rcx", "DepositCount value moved through rcx", "Eth1Data",
     rv([(50, "mov %rsi,0x20(%rdx)", ["mov %rsi,%rcx", "nop", "mov %rcx,0x20(%rdx)"])]), None, 0, ETH1_DATA_FIELDS, None),
    ("steps-store-after-last-field", "store after the last field event (epilogue rule, refused)", "Eth1Data",
     rv([(87, "xor %eax,%eax", ("before", ["mov %rsi,0x20(%rdx)"]))]), None, 2, [], "other"),
    ("steps-buffer-reloaded-after-call", "buffer reloaded from sp + 8 after the call", "PendingConsolidation",
     rv([(49, "mov 0x60(%rsp),%rbx", "mov 0x8(%rsp),%rbx")]), None, 0, PENDING_CONSOLIDATION_FIELDS, None),
    ("steps-receiver-in-other-slot-across-call", "receiver in another frame slot across the call", "PendingConsolidation",
     rv([(16, "add $0x8,%rax", ("before", ["mov %rax,0x30(%rsp)"])), (53, "mov 0x58(%rsp),%rax", "mov 0x30(%rsp),%rax")]),
     None, 0, PENDING_CONSOLIDATION_FIELDS, None),
    ("steps-head-without-nil-check", "no nil check in the head", "SyncCommitteeMessage", rv([(15, "test %al,(%rax)", None)]), None, 0, SYNC_COMMITTEE_MESSAGE_FIELDS, None),
    ("steps-aligned-store-to-neighbour-slot", "aligned store to the neighbour slot 0x40", "Eth1Data",
     rv([(48, "mov 0x38(%rsp),%rsi", ("before", ["mov %rdx,0x40(%rsp)"]))]), None, 0, ETH1_DATA_FIELDS, None),
]

# Head size immediate vs the IR, and the systematic pass (callee vs the IR overlay
# type, the directives after the last field event)
STEP_SIZE_CALLEE_EPILOGUE_MUT = [
    ("steps-head-size-0x10-against-ir-0x90", "head: `cmp $0x10,%rcx` (IR SSZ size 0x90)", "SyncCommitteeMessage",
     rv([(10, "cmp $0x90,%rcx", "cmp $0x10,%rcx")]), None, 2, [], "other"),
    ("steps-head-size-0x20-against-ir-0x48", "head: `cmp $0x20,%rcx` (IR SSZ size 0x48)", "Eth1Data",
     rv([(10, "cmp $0x48,%rcx", "cmp $0x20,%rcx")]), None, 2, [], "other"),
    ("steps-head-size-0x100-against-ir-0x48", "head: `cmp $0x100,%rcx` (IR SSZ size 0x48)", "Eth1Data",
     rv([(10, "cmp $0x48,%rcx", "cmp $0x100,%rcx")]), None, 2, [], "other"),
    ("steps-callee-epoch-for-validator-index", "Index (IR ValidatorIndex): `callq …Epoch.UnmarshalSSZ` (callee not the overlay type)", "PendingPartialWithdrawal",
     rv([(18, f"callq {PRIM}ValidatorIndex.UnmarshalSSZ", f"callq {PRIM}Epoch.UnmarshalSSZ")]), None, 2, [], "set-up order"),
    ("steps-callee-validator-index-for-epoch", "WithdrawableEpoch (IR Epoch): `callq …ValidatorIndex.UnmarshalSSZ`", "PendingPartialWithdrawal",
     rv([(60, f"callq {PRIM}Epoch.UnmarshalSSZ", f"callq {PRIM}ValidatorIndex.UnmarshalSSZ")]), None, 3, PENDING_PARTIAL_WITHDRAWAL_FIELDS[:2], "other"),
    ("steps-epilogue-call", "a `callq …Epoch.UnmarshalSSZ` after the last field event", "Eth1Data",
     rv([(87, "xor %eax,%eax", ("before", [f"callq {PRIM}Epoch.UnmarshalSSZ"]))]), None, 2, [], "other"),
    ("steps-epilogue-stack-store", "a stack store `mov %rsi,0x8(%rsp)` after the last field event", "Eth1Data",
     rv([(87, "xor %eax,%eax", ("before", ["mov %rsi,0x8(%rsp)"]))]), None, 2, [], "other"),
    ("steps-epilogue-other-frame", "`add $0x28,%rsp` (head frame 0x20) after the last field event", "Eth1Data",
     rv([(89, "add $0x20,%rsp", "add $0x28,%rsp")]), None, 2, [], "other"),
    ("steps-epilogue-nop-covered", "a `nop` in the epilogue (plain return: covered)", "Eth1Data",
     rv([(89, "add $0x20,%rsp", ("before", ["nop"]))]), None, 0, ETH1_DATA_FIELDS, None),
]

# An epilogue `jmp` to a label that is not in the file
STEP_TAIL_JUMP_MUT = [
    ("steps-tail-jump-to-runtime-abort", "Eth1Data: `jmp runtime.abort` in place of `xor %eax,%eax` after the last field event", "Eth1Data",
     rv([(87, "xor %eax,%eax", "jmp runtime.abort")]), None, 2, [], "other"),
    ("steps-tail-indirect-jump", "Eth1Data: `jmp *%rdx` in place of `xor %eax,%eax` after the last field event", "Eth1Data",
     rv([(87, "xor %eax,%eax", "jmp *%rdx")]), None, 2, [], "other"),
    ("steps-tail-jump-to-callee", "SyncCommitteeMessage: a tail `jmp …Slot.UnmarshalSSZ` after the last field event", "SyncCommitteeMessage",
     rv([(157, "mov 0x28(%rsp),%rax", ("before", ["jmp " + PRIM + "Slot.UnmarshalSSZ"]))]), None, 2, [], "other"),
]

# The fail-closed harness (written to <work-dir>; argv: generator.py config.json result.json; cwd = fv/kraken)
FAIL_CLOSED_HARNESS = r'''
import contextlib, importlib.util, io, json, pathlib, sys
spec = importlib.util.spec_from_file_location("generator_fail_closed", sys.argv[1])
sg = importlib.util.module_from_spec(spec)
spec.loader.exec_module(sg)
ARGV = list(sys.argv)  # call() replaces sys.argv
cfg = json.loads(pathlib.Path(ARGV[2]).read_text())
SUMMARY_PATH = pathlib.Path(cfg["summary"])


class Boom(Exception):
    """an exception class the generator does not know"""


def call():
    sys.argv = ["generator.py"] + cfg["argv"] + ["--summary", str(SUMMARY_PATH)]
    SUMMARY_PATH.unlink(missing_ok=True)
    so, se = io.StringIO(), io.StringIO()
    with contextlib.redirect_stdout(so), contextlib.redirect_stderr(se):
        try:
            sg.main()
            rc = 0
        except SystemExit as e:
            rc = e.code if isinstance(e.code, int) else (0 if e.code is None else 1)
        except BaseException as e:
            rc = "uncaught " + type(e).__name__
    sm = json.loads(SUMMARY_PATH.read_text()) if SUMMARY_PATH.exists() else None
    return rc, len(so.getvalue()), sm


def fire(kind, where):
    if kind == "unexpected":
        raise Boom("injected at " + where)
    if kind == "step_stop":
        raise sg.StepStop(0, "injected plain StepStop at " + where, "other")
    raise SystemExit(0)


def patched(name, fake, f=call):
    orig = getattr(sg, name)
    setattr(sg, name, fake)
    try:
        return f()
    finally:
        setattr(sg, name, orig)


res = []


def rec(phase, kind, where, r):
    rc, nso, sm = r
    res.append(dict(phase=phase, kind=kind, where=where, rc=rc, stdout=nso, summary_exit=(sm or {}).get("exit"),
                    covered=(sm or {}).get("covered"), total=(sm or {}).get("total")))


rec("control", "none", "", call())
for kind in ("unexpected", "step_stop", "sysexit0"):
    rec("head", kind, "step_head", patched("step_head", lambda *a, k=kind: fire(k, "step_head")))
rec("head", "returns None", "step_head", patched("step_head", lambda *a: None))
# the walk: count the step_parse / step_label_index calls and the current field of each (the walk's local `cur`)
for fn in ("step_parse", "step_label_index"):
    orig, seq = getattr(sg, fn), []

    def counter(*a, orig=orig, seq=seq):
        seq.append(sys._getframe(1).f_locals.get("cur"))
        return orig(*a)
    patched(fn, counter)
    for kind in ("unexpected", "step_stop", "sysexit0"):
        for n, cur in enumerate(seq):
            if kind == "sysexit0" and cur in seq[:n]:
                continue  # SystemExit(0): the first call of each field only
            cnt = [0]

            def inj(*a, orig=orig, n=n, kind=kind, cnt=cnt):
                cnt[0] += 1
                if cnt[0] == n + 1:
                    fire(kind, f"{fn} call {n}")
                return orig(*a)
            rec(f"field {cur}", kind, f"{fn} call {n}", patched(fn, inj))
# the theorem texts (after the walk): every call of the three text functions
seqt = []
origs = {fn: getattr(sg, fn) for fn in ("step_step_text", "step_call_text", "step_seg_text")}
for fn, o in origs.items():
    setattr(sg, fn, lambda *a, o=o, fn=fn: (seqt.append(fn), o(*a))[1])
call()
for fn, o in origs.items():
    setattr(sg, fn, o)
for kind in ("unexpected", "sysexit0"):
    for n in range(len(seqt)):
        cnt = [0]
        for fn, o in origs.items():
            def inj(*a, o=o, fn=fn, n=n, kind=kind, cnt=cnt):
                cnt[0] += 1
                if cnt[0] == n + 1:
                    fire(kind, f"text call {n}")
                return o(*a)
            setattr(sg, fn, inj)
        rec("text", kind, f"text call {n} ({seqt[n]})", call())
        for fn, o in origs.items():
            setattr(sg, fn, o)
for kind in ("unexpected", "step_stop", "sysexit0"):
    rec("epilogue", kind, "step_epilogue", patched("step_epilogue", lambda *a, k=kind: fire(k, "step_epilogue")))
rec("epilogue", "StepEpilogueMiss", "step_epilogue",
    patched("step_epilogue", lambda *a: (_ for _ in ()).throw(sg.StepEpilogueMiss(0, "injected", "other"))))
for v in (None, True, "ok", 0):
    rec("epilogue", f"returns {v!r}", "step_epilogue", patched("step_epilogue", lambda *a, v=v: v))
ow = sg.step_walk
rec("flags", "walk: every field done, with a stop", "step_walk",
    patched("step_walk", lambda *a: (lambda r: (r[0], sg.StepStop(0, "injected", "other"), r[2]))(ow(*a))))
rec("flags", "walk: every field done, no end index", "step_walk",
    patched("step_walk", lambda *a: (lambda r: (r[0], None, None))(ow(*a))))
oi = sg._decoder_step
rec("flags", "inner returns its full text, outer flags not set", "_decoder_step",
    patched("_decoder_step", lambda args, flags: oi(args, dict(flags))))
rec("flags", "inner sets two flags", "_decoder_step",
    patched("_decoder_step", lambda args, flags: (flags.update(head_ok=True, fields_complete=True), oi(args, dict(flags)))[1]))
pathlib.Path(ARGV[3]).write_text(json.dumps(res) + "\n")
'''


def fail_closed_cases(work, new):
    """Fail-closed injections (FAIL_CLOSED_HARNESS) on Eth1Data, SyncCommitteeMessage, PendingPartialWithdrawal."""
    res, bad = [], 0
    h = work / "fc_harness.py"
    h.write_text(FAIL_CLOSED_HARNESS)
    for key in ("Eth1Data", "SyncCommitteeMessage", "PendingPartialWithdrawal"):
        c = STEP_CASES[key]
        cfg, out = work / f"steps-fail-closed-{key}.cfg.json", work / f"steps-fail-closed-{key}.result.json"
        cfg.write_text(json.dumps(dict(argv=["decoder", "--steps", "--assembly", c["S"], "--ir", IR, "--type", c["type"]] + c["args"],
                                       summary=str(work / f"steps-fail-closed-{key}.summary.json"))))
        out.unlink(missing_ok=True)
        rc, so, se = run(["python3", "-I", "-B", str(h), str(new), str(cfg), str(out)], KR)
        R = json.loads(out.read_text()) if rc == 0 and out.exists() else []
        n = len(c["fields"])
        groups = {}
        for r in R:
            ph = r["phase"].split()[0] if not r["phase"].startswith("field") else r["phase"]
            groups.setdefault((ph, r["kind"].split(":")[0] if r["phase"] != "flags" else r["kind"]), []).append(r)
        for (ph, kind), rs in sorted(groups.items(), key=lambda x: str(x[0])):
            if ph == "control":
                ok = all(r["rc"] == 0 and r["stdout"] > 0 and r["covered"] == n for r in rs)
            else:
                ok = all(r["rc"] in ((2,) if kind in ("unexpected", "sysexit0") else (2, 3)) and r["stdout"] == 0
                         and r["summary_exit"] == r["rc"] and r["total"] == n and r["covered"] < n for r in rs)
            res.append(dict(id=f"steps-fail-closed-{key}-{ph.replace(' ', '')}-{kind.replace(' ', '_')}", expect="control: exit 0, all "
                            "covered" if ph == "control" else "exit 2 / 3 (2 for unexpected / SystemExit), 0 bytes, "
                            "summary exit equal, covered < total", exit=sorted({str(r["rc"]) for r in rs}),
                            stdout_bytes=sum(r["stdout"] for r in rs), injections=len(rs),
                            bad=[r for r in rs if not ok][:3], ok=bool(ok)))
            bad |= not ok
        # every IR field had injections in the walk, and every phase was injected
        fl = {r["phase"] for r in R}
        ok = rc == 0 and all(f"field {x}" in fl for x in range(n)) and {"head", "text", "epilogue", "flags", "control"} <= fl
        res.append(dict(id=f"steps-fail-closed-{key}-phases", expect=f"harness exit 0; injections in the head, fields 0..{n - 1}, "
                        "texts, epilogue, flags", exit=rc, stdout_bytes=0, injections=len(R),
                        phases=sorted(fl), stderr=se.strip()[-300:], ok=bool(ok)))
        bad |= not ok
    return res, bad


def step_cases(work, new):
    """`--steps` on real types and dataflow adversarial inputs."""
    res, bad = [], 0
    irt = (KR / IR).read_text()
    KC = ["python3", "-I", "-B", str(HERE / "kindcheck.py")]
    G = ["python3", "-I", "-B", str(new), "decoder", "--steps"]
    for key, c in STEP_CASES.items():
        outs = []
        for i in range(2):
            su = work / f"steps-new-{key}-{i}.json"
            su.unlink(missing_ok=True)
            rc, so, se = run(G + ["--assembly", c["S"], "--ir", IR, "--type", c["type"], "--summary", str(su)] + c["args"], KR)
            outs.append((rc, so, json.loads(su.read_text())))
        rc, so, sm = outs[0]
        part = c["cov"] != c["fields"]
        cov = [f["field"] for f in sm["fields"] if f["status"] == "covered"]
        kc = None
        if not part:
            f = work / f"steps-new-{key}.lean"
            f.write_bytes(so)
            kc = subprocess.run(KC + [str(f)], capture_output=True, text=True).returncode
        com = (KR / c["committed"]).read_bytes() if (KR / c["committed"]).exists() else None
        ok = (rc == (3 if part else 0) and outs[0][:2] == outs[1][:2] and cov == c["cov"]
              and kc == (None if part else 0) and (com is None or com == so) and (not part or so == b""))
        res.append(dict(id=f"steps-new-{key}", expect=f"exit {3 if part else 0} twice, identical, covered {c['cov']}"
                        + ("" if part else ", kindcheck PASS, = committed if present"), exit=rc, stdout_bytes=len(so), covered=cov,
                        kindcheck_exit=kc, committed_present=com is not None,
                        equals_committed=(com == so) if com is not None else None, ok=bool(ok)))
        bad |= not ok
    for (mid, what, key, eds, irf, want, covw, mcls) in STEP_MUT + STEP_STACK_AND_SETUP_MUT + STEP_SIZE_CALLEE_EPILOGUE_MUT + STEP_TAIL_JUMP_MUT:
        c = STEP_CASES[key]
        base = (KR / c["S"]).read_text().split("\n")
        lines = eds(base) if callable(eds) else edits(base, eds)
        fS = work / f"{mid}.S"
        fS.write_text("\n".join(lines))
        irp = KR / IR
        if irf:
            irp = work / f"{mid}.ir.json"
            irp.write_text(ir_edit(irt, c["type"], irf))
        su = work / f"{mid}.json"
        su.unlink(missing_ok=True)
        rc, so, se = run(G + ["--assembly", str(fS), "--ir", str(irp), "--type", c["type"], "--summary", str(su)] + c["args"], KR)
        sm = json.loads(su.read_text()) if su.exists() else {}
        cov = [f["field"] for f in sm.get("fields", []) if f.get("status") == "covered"] if rc != 2 else []
        unc = [f for f in sm.get("fields", []) if f.get("status") != "covered"]
        kcr = None
        if rc == 0:
            fo = work / f"{mid}.lean"
            fo.write_bytes(so)
            kcr = subprocess.run(KC + [str(fo)], capture_output=True, text=True).returncode
        # `reached` is true up to the first uncovered field and false after it (every field on a head miss)
        fl = sm.get("fields", [])
        x0 = next((x for x, f in enumerate(fl) if f.get("status") != "covered"), len(fl))
        head_miss = sm.get("head", {}).get("status") == "not covered"
        # on an epilogue miss every field was reached
        epilogue_miss = sm.get("epilogue", {}).get("status") == "not covered"
        reach_ok = all(f.get("reached") == (False if head_miss else True if epilogue_miss else x <= x0)
                       for x, f in enumerate(fl))
        ok = (rc == want and (so == b"") == (want != 0) and sm.get("exit") == want and cov == covw
              and kcr == {0: 0}.get(want) and (mcls is None or (unc and unc[0].get("miss_class") == mcls))
              and reach_ok and (want != 2 or len(fl) == len(c["fields"])))
        res.append(dict(id=mid, what=what, expect=f"exit {want}, covered {covw}" + (f", miss class {mcls}" if mcls else ""),
                        exit=rc, stdout_bytes=len(so), covered=cov, kindcheck_exit=kcr,
                        uncovered=[(f["field"], f.get("miss_class"), f.get("reason")) for f in unc], ok=bool(ok)))
        bad |= not ok
    return res, bad


# ---------------------------------------------------------------------------------------------- whole-accept

def whole_accept_case(sdir, tname, const, mod):
    return dict(S=f"prysm/go1.26.10/link-set/{sdir}/{PN}{tname}.UnmarshalSSZ.S", type=f"v1alpha1.{tname}",
                args=["--const", const, "--prefix", "Decode.generated", "--imports", mod, "--open", f"Prysm.{tname}.Code"])


WHOLE_ACCEPT_CASES = {
    "PendingDeposit": whole_accept_case("norm", "PendingDeposit", "unmarshalSSZ", "Prysm.PendingDeposit.Code"),
    "SyncCommitteeMessage": whole_accept_case("norm", "SyncCommitteeMessage", "unmarshalSSZ", "Prysm.SyncCommitteeMessage.Code"),
    "VoluntaryExit": whole_accept_case("norm", "VoluntaryExit", "unmarshalSSZ", "Prysm.PendingDeposit.Code"),
    "PowBlock": whole_accept_case("norm", "PowBlock", "unmarshalSSZ", "Prysm.PendingDeposit.Code"),
    "ValidatorBalance": whole_accept_case("norm", "ValidatorBalance", "unmarshalSSZ", "Prysm.PendingDeposit.Code"),
    "PendingPartialWithdrawal": whole_accept_case("norm", "PendingPartialWithdrawal", "unmarshalSSZ", "Prysm.Deposit_Data.Code"),
    "AttestationData": whole_accept_case("norm", "AttestationData", "unmarshalSSZ", "Prysm.AttestationData.Code"),
}


def ir_goff(field, off):
    def fn(t):
        for f in t["go_fields"]:
            if f["name"] == field:
                f["offset_gc_amd64"] = off
    return fn


# (id, what, type key, .S edit function or None, IR edit or None, expected exit)
WHOLE_ACCEPT_MUT = [
    # classes of the step rules (the step front end refuses; whole-accept emits nothing)
    ("whole-accept-store-misaligned", "PendingDeposit Amount: `mov %rsi,0x2c(%rsp)` before the receiver store (misaligned stack store)",
     "PendingDeposit", rv([(88, "mov %rsi,0x38(%rdx)", ("before", ["mov %rsi,0x2c(%rsp)"]))]), None, 2),
    ("whole-accept-store-overlap-bf", "PendingDeposit Amount: `mov %rdx,0x58(%rsp)` overwrites the buffer slot before its reload",
     "PendingDeposit", rv([(86, "mov 0x58(%rsp),%rsi", ("before", ["mov %rdx,0x58(%rsp)"]))]), None, 2),
    ("whole-accept-head-spill-before-push", "VoluntaryExit: a spill `mov %rax,0x58(%rsp)` before `push %rbp`", "VoluntaryExit",
     rv([(5, "push %rbp", ("before", ["mov %rax,0x58(%rsp)"]))]), None, 2),
    ("whole-accept-head-no-frame", "VoluntaryExit: `sub $0x48,%rsp` removed (frame never allocated)", "VoluntaryExit",
     rv([(7, "sub $0x48,%rsp", "nop")]), None, 2),
    ("whole-accept-head-nop-moved", "VoluntaryExit: the head `nop` moved before `cmp 0x10(%r14),%rsp`", "VoluntaryExit",
     rv([(9, "nop", None), (3, "cmp 0x10(%r14),%rsp", ("before", ["nop"]))]), None, 2),
    ("whole-accept-size-imm", "VoluntaryExit: `cmp $0x18,%rcx` (IR SSZ size 16)", "VoluntaryExit", rv([(10, "cmp $0x10,%rcx", "cmp $0x18,%rcx")]), None, 2),
    ("whole-accept-epilogue-jmp-missing", "PowBlock: `jmp runtime.abort` in place of `xor %eax,%eax` after the last field event", "PowBlock",
     rv([(120, "xor %eax,%eax", "jmp runtime.abort")]), None, 2),
    ("whole-accept-truncated", "SyncCommitteeMessage `.S` cut inside the Signature segment", "SyncCommitteeMessage", lambda L: L[:140], None, 2),
    ("whole-accept-truncated-epilogue", "VoluntaryExit `.S` cut after `add $0x48,%rsp` of the accept epilogue", "VoluntaryExit", lambda L: L[:87], None, 2),
    ("whole-accept-callee-other-type", "VoluntaryExit: the ValidatorIndex field calls Epoch.UnmarshalSSZ", "VoluntaryExit",
     lambda L: [l.replace("ValidatorIndex.UnmarshalSSZ", "Epoch.UnmarshalSSZ") for l in L], None, 2),
    # whole-accept rules (the step front end covers these inputs; whole-accept refuses)
    ("whole-accept-head-rdi-not-home", "PendingDeposit: `mov %rdi,0x70(%rsp)` (rdi home slot 0x68)", "PendingDeposit",
     rv([(13, "mov %rdi,0x68(%rsp)", "mov %rdi,0x70(%rsp)")]), None, 2),
    ("whole-accept-head-spill-twice", "PendingDeposit: `mov %rax,0x50(%rsp)` twice", "PendingDeposit",
     rv([(12, "mov %rax,0x50(%rsp)", ["mov %rax,0x50(%rsp)", "mov %rax,0x50(%rsp)"])]), None, 2),
    ("whole-accept-head-rcx-spill", "VoluntaryExit: an extra spill `mov %rcx,0x68(%rsp)` (no rcx slot in the kind)", "VoluntaryExit",
     rv([(15, "test %al,(%rax)", ("before", ["mov %rcx,0x68(%rsp)"]))]), None, 2),
    ("whole-accept-head-db", "ValidatorBalance: decoderPrologue spills rbx to 0x48 (dB != F + 24)", "ValidatorBalance",
     rv([(8, "mov %rbx,0x50(%rsp)", "mov %rbx,0x48(%rsp)")]), None, 2),
    ("whole-accept-epilogue-xor-frame48", "VoluntaryExit: `xor %eax,%eax; xor %ebx,%ebx` before `add $0x48,%rsp` (no xor lemma in frame 0x48)",
     "VoluntaryExit", rv([(87, "add $0x48,%rsp", ("before", ["xor %eax,%eax", "xor %ebx,%ebx"]))]), None, 2),
    ("whole-accept-epilogue-load-ptr-slot", "SyncCommitteeMessage: epilogue `mov 0x38(%rsp),%rax` (the pointer slot, not a zero slot)", "SyncCommitteeMessage",
     rv([(157, "mov 0x28(%rsp),%rax", "mov 0x38(%rsp),%rax")]), None, 2),
    ("whole-accept-epilogue-nop", "PendingDeposit: a `nop` between `add $0x40,%rsp` and `pop %rbp` of the accept epilogue", "PendingDeposit",
     rv([(163, "pop %rbp", ("before", ["nop"]))]), None, 2),
    ("whole-accept-reject-errsize", "SyncCommitteeMessage: size-error block loads ssz.ErrOffset", "SyncCommitteeMessage",
     rv([(163, "mov ssz.ErrSize(%rip),%rax", "mov ssz.ErrOffset(%rip),%rax")]), None, 2),
    ("whole-accept-reject-frame", "VoluntaryExit: size-error block `add $0x40,%rsp` (frame 0x48)", "VoluntaryExit",
     rv([(93, "add $0x48,%rsp", "add $0x40,%rsp")]), None, 2),
    ("whole-accept-store-input", "PendingDeposit Amount: `mov %rsi,0x30(%rsp)` stores the input word into a frame slot", "PendingDeposit",
     rv([(88, "mov %rsi,0x38(%rdx)", ("before", ["mov %rsi,0x30(%rsp)"]))]), None, 2),
    ("whole-accept-load-outside-layout", "ValidatorBalance Balance: `mov 0x30(%rsp),%rsi` (no stack chunk at 0x30)", "ValidatorBalance",
     rv([(52, "mov %rcx,0x10(%rdx)", ("before", ["mov 0x30(%rsp),%rsi"]))]), None, 2),
    ("whole-accept-interleaved", "real PendingPartialWithdrawal: the Epoch set-up runs inside the Amount field", "PendingPartialWithdrawal", None, None, 2),
    ("whole-accept-nested", "real AttestationData: Source / Target are nested containers (step exit 3)", "AttestationData", None, None, 2),
    # statement-level IR mutants
    ("whole-accept-ir-goff", "IR: PowBlock ParentHash Go offset 32 (code 24)", "PowBlock", None, ir_goff("ParentHash", 32), 2),
    ("whole-accept-ir-size", "IR: PowBlock TotalDifficulty of 48 bytes (code 32)", "PowBlock", None, ir_size("TotalDifficulty", 48), 2),
    ("whole-accept-ir-order", "IR: VoluntaryExit Epoch / ValidatorIndex order swapped", "VoluntaryExit", None, ir_swap("Epoch", "ValidatorIndex"), 2),
    ("whole-accept-ir-goff-code", "IR and code: ValidatorBalance Balance at Go offset 24 (code store 0x18; not the running sum 16)", "ValidatorBalance",
     rv([(52, "mov %rcx,0x10(%rdx)", "mov %rcx,0x18(%rdx)")]), ir_goff("Balance", 24), 2),
    ("whole-accept-ir-goff-first", "IR: VoluntaryExit Epoch Go offset 0 (code 8, state word)", "VoluntaryExit", None, ir_goff("Epoch", 0), 2),
    # valid variants: generated, kindcheck PASS
    ("whole-accept-valid-extra-move", "SyncCommitteeMessage: an extra `mov %rdi,%rsi` in the ValidatorIndex set-up", "SyncCommitteeMessage",
     sync_committee_message_validator_index_setup(VALIDATOR_INDEX_SETUP[:4] + ["  mov %rdi,%rsi"] + VALIDATOR_INDEX_SETUP[4:]), None, 0),
    ("whole-accept-valid-order", "SyncCommitteeMessage: ValidatorIndex set-up with `mov $0x8,%ecx` first", "SyncCommitteeMessage",
     sync_committee_message_validator_index_setup([VALIDATOR_INDEX_SETUP[5]] + VALIDATOR_INDEX_SETUP[:5]), None, 0),
]


def whole_accept_run(work, new, mid, c, S=None, ir=None, extra=()):
    su = work / f"{mid}.whole-accept.json"
    su.unlink(missing_ok=True)
    rc, so, se = run(["python3", "-I", "-B", str(new), "decoder", "--whole-accept", "--assembly", S or c["S"], "--ir", ir or IR,
                      "--type", c["type"], "--summary", str(su)] + c["args"] + list(extra), KR)
    sm = json.loads(su.read_text()) if su.exists() else {}
    return rc, so, se, sm


def whole_accept_cases(work, new):
    """`--whole-accept` on real types, adversarial inputs, valid variants."""
    res, bad = [], 0
    KC = ["python3", "-I", "-B", str(HERE / "kindcheck.py")]
    irt = (KR / IR).read_text()
    for key in ("PendingDeposit", "SyncCommitteeMessage", "VoluntaryExit", "PowBlock", "ValidatorBalance", "PendingPartialWithdrawal", "AttestationData"):
        c = WHOLE_ACCEPT_CASES[key]
        r1, r2 = whole_accept_run(work, new, f"whole-accept-new-{key}-1", c), whole_accept_run(work, new, f"whole-accept-new-{key}-2", c)
        want = 2 if key in ("PendingPartialWithdrawal", "AttestationData") else 0
        kc = None
        if r1[0] == 0:
            f = work / f"whole-accept-new-{key}.lean"
            f.write_bytes(r1[1])
            kc = subprocess.run(KC + [str(f)], capture_output=True, text=True).returncode
        t = r1[1].decode()
        pre = c["args"][3]
        thm = all(f"\ntheorem {pre}_{x} : " in t and f"\ntheorem {pre}_{x}_kind : " in t
                  for x in ("head", "field_1", "epilogue", "accept", "reject")) if want == 0 else True
        ok = (r1[0] == want and r1[:2] == r2[:2] and (r1[1] == b"") == (want != 0) and thm and kc == (0 if want == 0 else None)
              and r1[3].get("exit") == want and r1[3].get("accept_generated") == (want == 0))
        res.append(dict(id=f"whole-accept-new-{key}", expect=f"exit {want} twice, identical" + (", every whole-accept theorem kinded, kindcheck "
                        "PASS" if want == 0 else ", 0 bytes, accept_generated false"), exit=r1[0], stdout_bytes=len(r1[1]),
                        kindcheck_exit=kc, reason=r1[3].get("reason", "")[:300], ok=bool(ok)))
        bad |= not ok
    for (mid, what, key, eds, irf, want) in WHOLE_ACCEPT_MUT:
        c = WHOLE_ACCEPT_CASES[key]
        S = None
        if eds is not None:
            lines = eds((KR / c["S"]).read_text().split("\n"))
            fS = work / f"{mid}.S"
            fS.write_text("\n".join(lines))
            S = str(fS)
        irp = None
        if irf is not None:
            irp = work / f"{mid}.ir.json"
            irp.write_text(ir_edit(irt, c["type"], irf))
            irp = str(irp)
        rc, so, se, sm = whole_accept_run(work, new, mid, c, S, irp)
        kc = None
        if rc == 0:
            f = work / f"{mid}.lean"
            f.write_bytes(so)
            kc = subprocess.run(KC + [str(f)], capture_output=True, text=True).returncode
        ok = (rc == want and (so == b"") == (want != 0) and sm.get("exit") == want
              and sm.get("accept_generated") == (want == 0) and (want != 0 or kc == 0)
              and (want == 0 or "theorem" not in so.decode()))
        res.append(dict(id=mid, what=what, expect=f"exit {want}" + (", kindcheck PASS" if want == 0 else
                        ", 0 bytes, no accept theorem"), exit=rc, stdout_bytes=len(so), kindcheck_exit=kc,
                        reason=sm.get("reason", "")[:300], ok=bool(ok)))
        bad |= not ok
    return res, bad


# the whole-accept fail-closed harness (written to <work-dir>; argv: generator.py config.json result.json; cwd = fv/kraken)
WHOLE_ACCEPT_FAIL_CLOSED_HARNESS = r"""
import contextlib, importlib.util, io, json, pathlib, sys
spec = importlib.util.spec_from_file_location("generator_whole_accept_fail_closed", sys.argv[1])
sg = importlib.util.module_from_spec(spec)
spec.loader.exec_module(sg)
whole_accept_gen = sg.whole_accept_module()
ARGV = list(sys.argv)
cfg = json.loads(pathlib.Path(ARGV[2]).read_text())
SUMMARY_PATH = pathlib.Path(cfg["summary"])


class Boom(Exception):
    pass


def call():
    sys.argv = ["generator.py"] + cfg["argv"] + ["--summary", str(SUMMARY_PATH)]
    SUMMARY_PATH.unlink(missing_ok=True)
    so, se = io.StringIO(), io.StringIO()
    with contextlib.redirect_stdout(so), contextlib.redirect_stderr(se):
        try:
            sg.main()
            rc = 0
        except SystemExit as e:
            rc = e.code if isinstance(e.code, int) else (0 if e.code is None else 1)
        except BaseException as e:
            rc = "uncaught " + type(e).__name__
    sm = json.loads(SUMMARY_PATH.read_text()) if SUMMARY_PATH.exists() else None
    return rc, len(so.getvalue()), sm


def fire(kind, where):
    if kind == "unexpected":
        raise Boom("injected at " + where)
    if kind == "refuse":
        raise whole_accept_gen.WholeAcceptRefuse("injected at " + where)
    raise SystemExit(0)


def patched(obj, name, fake):
    orig = getattr(obj, name)
    setattr(obj, name, fake)
    try:
        return call()
    finally:
        setattr(obj, name, orig)


res = []


def rec(phase, kind, where, r):
    rc, nso, sm = r
    res.append(dict(phase=phase, kind=kind, where=where, rc=rc, stdout=nso, summary_exit=(sm or {}).get("exit"),
                    acc=(sm or {}).get("accept_generated")))


rec("control", "none", "", call())
KINDS = ("unexpected", "refuse", "sysexit0")
# phase step: the front end and the recomputed walk / epilogue
for kind in KINDS:
    rec("step", kind, "decoder_step", patched(sg, "decoder_step", lambda *a, k=kind: fire(k, "decoder_step")))
    rec("step", kind, "step_walk", patched(sg, "step_walk", lambda *a, k=kind: fire(k, "step_walk")))
    rec("step", kind, "step_epilogue", patched(sg, "step_epilogue", lambda *a, k=kind: fire(k, "step_epilogue")))
o4 = sg.decoder_step
rec("step", "returns None", "decoder_step", patched(sg, "decoder_step", lambda *a: None))
rec("step", "returns a cut text", "decoder_step", patched(sg, "decoder_step", lambda *a: o4(*a)[:-20]))
ow = sg.step_walk
rec("step", "walk with a stop", "step_walk", patched(sg, "step_walk", lambda *a: (lambda r: (r[0], sg.StepStop(0, "x", "other"), r[2]))(ow(*a))))
rec("step", "epilogue returns True", "step_epilogue", patched(sg, "step_epilogue", lambda *a: True))
# phase derive: the specifications and every step rendering
for fn in ("whole_accept_derive", "whole_accept_head_spec", "whole_accept_epilogue_spec", "whole_accept_reject_spec"):
    for kind in KINDS:
        rec("derive", kind, fn, patched(whole_accept_gen, fn, lambda *a, k=kind, fn=fn: fire(k, fn)))
ostep, seq = whole_accept_gen.whole_accept_step, []
setattr(whole_accept_gen, "whole_accept_step", lambda *a: (seq.append(1), ostep(*a))[1])
call()
setattr(whole_accept_gen, "whole_accept_step", ostep)
for kind in KINDS:
    for n in range(len(seq)):
        cnt = [0]

        def inj(*a, n=n, kind=kind, cnt=cnt):
            cnt[0] += 1
            if cnt[0] == n + 1:
                fire(kind, f"whole_accept_step call {n}")
            return ostep(*a)
        rec("derive", kind, f"whole_accept_step call {n}", patched(whole_accept_gen, "whole_accept_step", inj))
# phase render: every theorem renderer (each call), the kind recorder
for meth in ("head", "field", "f_u64", "f_bytes", "f_call", "epilogue", "accept", "reject", "layout", "binders", "mem"):
    om, seqm = getattr(whole_accept_gen.T, meth), []
    setattr(whole_accept_gen.T, meth, lambda self, *a, om=om, seqm=seqm: (seqm.append(1), om(self, *a))[1])
    call()
    setattr(whole_accept_gen.T, meth, om)
    for kind in KINDS:
        for n in range(len(seqm)):
            cnt = [0]

            def inj(self, *a, n=n, kind=kind, cnt=cnt, om=om, meth=meth):
                cnt[0] += 1
                if cnt[0] == n + 1:
                    fire(kind, f"T.{meth} call {n}")
                return om(self, *a)
            rec("render", kind, f"T.{meth} call {n}", patched(whole_accept_gen.T, meth, inj))
ok_ = whole_accept_gen.T.kind
rec("flags", "a kind line not recorded", "T.kind", patched(whole_accept_gen.T, "kind", lambda self, name, kind, extra: (
    ok_(self, name, kind, extra), self.kinds_emitted.pop() if name.endswith("_field_1") else None)[0]))
rec("flags", "a kind line dropped from the text", "T.body", patched(whole_accept_gen.T, "body", (lambda ob: lambda self: ob(self).replace(
    "_epilogue_kind :", "_epilogue_kinx :", 1))(whole_accept_gen.T.body)))
oi = sg._decoder_whole_accept
rec("flags", "inner returns its text, outer flags not set", "_decoder_whole_accept",
    patched(sg, "_decoder_whole_accept", lambda args, flags: oi(args, dict(flags))))
rec("flags", "inner sets four of five flags", "_decoder_whole_accept", patched(sg, "_decoder_whole_accept", lambda args, flags: (
    lambda t: (flags.update({k: True for k in sg.WHOLE_ACCEPT_FLAGS[:4]}), t)[1])(oi(args, dict(flags)))))
pathlib.Path(ARGV[3]).write_text(json.dumps(res) + "\n")
"""


WHOLE_ACCEPT_FAIL_CLOSED_KEYS = ("PendingDeposit", "SyncCommitteeMessage", "VoluntaryExit", "PowBlock", "ValidatorBalance")


def whole_accept_fc_cases(work, new, keys=None):
    res, bad = [], 0
    h = work / "whole_accept_fail_closed_harness.py"
    h.write_text(WHOLE_ACCEPT_FAIL_CLOSED_HARNESS)
    for key in (keys or WHOLE_ACCEPT_FAIL_CLOSED_KEYS):
        c = WHOLE_ACCEPT_CASES[key]
        cfg, out = work / f"whole-accept-fail-closed-{key}.cfg.json", work / f"whole-accept-fail-closed-{key}.result.json"
        cfg.write_text(json.dumps(dict(argv=["decoder", "--whole-accept", "--assembly", c["S"], "--ir", IR, "--type", c["type"]] + c["args"],
                                       summary=str(work / f"whole-accept-fail-closed-{key}.summary.json"))))
        out.unlink(missing_ok=True)
        rc, so, se = run(["python3", "-I", "-B", str(h), str(new), str(cfg), str(out)], KR)
        R = json.loads(out.read_text()) if rc == 0 and out.exists() else []
        groups = {}
        for r in R:
            groups.setdefault((r["phase"], r["kind"]), []).append(r)
        for (ph, kind), rs in sorted(groups.items()):
            if ph == "control":
                ok = all(r["rc"] == 0 and r["stdout"] > 0 and r["acc"] is True for r in rs)
            else:
                ok = all(r["rc"] == 2 and r["stdout"] == 0 and r["summary_exit"] == 2 and r["acc"] is False for r in rs)
            res.append(dict(id=f"whole-accept-fail-closed-{key}-{ph}-{kind.replace(' ', '_')}", expect="control: exit 0" if ph == "control"
                            else "exit 2, 0 bytes, summary exit 2, accept_generated false", exit=sorted({str(r["rc"]) for r in rs}),
                            stdout_bytes=sum(r["stdout"] for r in rs), injections=len(rs),
                            bad=[r for r in rs if not ok][:3], ok=bool(ok)))
            bad |= not ok
        fl = {r["phase"] for r in R}
        ok = rc == 0 and {"control", "step", "derive", "render", "flags"} <= fl and len(R) > 50
        res.append(dict(id=f"whole-accept-fail-closed-{key}-phases", expect="harness exit 0; injections in step, derive, render, flags",
                        exit=rc, stdout_bytes=0, injections=len(R), phases=sorted(fl), stderr=se.strip()[-300:], ok=bool(ok)))
        bad |= not ok
    return res, bad


def main(work, out):
    work.mkdir(parents=True, exist_ok=True)
    res, bad = [], 0
    new = KR / "gen" / "generator" / "generator.py"

    base = (KR / S).read_text().split("\n")
    for (mid, what, line, o, n, want, match) in MUTANTS:
        if mid == "mutant-both-fields":
            lines = mutate(mutate(base, 31, "  mov $0x20,%ecx", "  mov $0x10,%ecx"), 68, "  add $0x28,%rbx", "  add $0x28,%rsi")
        else:
            lines = mutate(base, line, o, n)
        f = work / f"{mid}.S"
        f.write_text("\n".join(lines))
        rc, so, se = run(["python3", "-I", str(new), "decoder", "--assembly", str(f)] + ARGS, KR)
        got = sorted(l.split()[3].rstrip(":") for l in se.split("\n") if ": MATCH form" in l)
        ok = rc == want and so == b"" and (want == 2 or got == sorted(match))
        res.append(dict(id=mid, what=what, expect=f"exit {want}, 0 bytes" + (f", MATCH {match}" if want == 3 else ""),
                        exit=rc, stdout_bytes=len(so), matched=got, stderr=se.strip().split("\n"), ok=bool(ok)))
        bad |= not ok

    r4, b4 = step_cases(work, new)
    res += r4
    bad |= b4
    r5, b5 = fail_closed_cases(work, new)
    res += r5
    bad |= b5
    r6, b6 = whole_accept_cases(work, new)
    res += r6
    bad |= b6
    r7, b7 = whole_accept_fc_cases(work, new)
    res += r7
    bad |= b7

    out.write_text(json.dumps(dict(cases=res, passed=sum(r["ok"] for r in res), total=len(res)), indent=1) + "\n")
    print(f"decoder_test: {sum(r['ok'] for r in res)}/{len(res)} as expected")
    for r in res:
        print(("OK  " if r["ok"] else "BAD ") + r["id"], "exit", r["exit"], "stdout", r["stdout_bytes"])
    return 1 if bad else 0


if __name__ == "__main__":
    if len(sys.argv) != 3:
        print(__doc__)
        sys.exit(2)
    sys.exit(main(pathlib.Path(sys.argv[1]), pathlib.Path(sys.argv[2])))
