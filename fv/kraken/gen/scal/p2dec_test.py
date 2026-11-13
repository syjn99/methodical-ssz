#!/usr/bin/env python3
"""Generator tests for the extension of `scalgen.py decoder` to a 32-byte field at SSZ offset 0 (offset-0 form). Tests that can fail.

usage: p2dec_test.py <work-dir> <result.json>      (run from anywhere; one gated job; Python 3 stdlib + git)
exit 0 = every case has its expected exit code and output; 1 = a case differs; 2 = usage

Cases (all on the committed Eth1Data `.S` and IR; mutants are written to <work-dir>, nothing in the repo):
 - old-gen: the frozen generator (git blob OLD_BLOB, method freeze 56dfc27) on Eth1Data: exit 2, 0 bytes on
   stdout, stderr = the committed record line of `prysm/go1.26.10/e2e/e1/gen-e1dec.raw.txt` (historical record).
 - new-gen: the working-tree generator on Eth1Data: exit 0, both fields (DepositRoot offset-0 form,
   BlockHash add form), stdout = the committed `lean/Prysm/Eth1Data/GeneratedDecodeRootFieldSegments.lean`, two runs byte-identical.
 - mutants of the `.S` (one line changed or removed, found by exact text at a 1-based line):
   wrong length, missing memmove, an add on another register, offset-0 form with a wrong destination,
   offset-0 form at a non-zero SSZ offset, broken head of the first field, unrecognised directive in place
   of the add. Expected exit 2 (no field matches) or 3 (some fields match), and 0 bytes on stdout always.
 - partial: one mutant again with `--partial-out`: the file starts with `/-! PARTIAL OUTPUT` and names the
   missing field; stdout stays empty.

field-segment cases (`decoder --field-segments`; ids `field-segments-*`; mutated `.S` and IR copies in <work-dir> only):
 - field-segments-compat-*: the default mode (no `--field-segments`) on BlobIdentifier / DepositMessage still prints the committed
   files of hold-out types BlobIdentifier and DepositMessage, `Prysm/BlobIdentifier/GeneratedDecodeRootFieldSegments.lean` / `Prysm/DepositMessage/GeneratedDecodeRootFieldSegments.lean` byte for byte.
 - field-segments-new-*: `--field-segments` on Eth1Data, BlobIdentifier, DepositMessage: exit 0 twice, identical, = the committed
   raw files `Prysm/Eth1Data/GeneratedDecodeFieldSegments.lean`, `Prysm/BlobIdentifier/GeneratedDecodeFieldSegments.lean`, `Prysm/DepositMessage/GeneratedDecodeFieldSegments.lean`, with every field covered.
 - adversarial `.S` / IR mutants: wrong size immediates, a size other than 32 / 48 / 96, mismatched registers
   in the uint64 triple, base register not rsp / rdx, a scratch register outside the lemma's list, wrong
   displacement against the IR, truncated `.S`, swapped field order (IR and code), a delegated overlay
   field (real BeaconBlockHeader). Expected: the field is "not covered" (no theorem with its name, exit 3) or
   exit 2; 0 bytes on stdout whenever the exit code is not 0; the `--summary` JSON agrees with the exit code.
 - field-segments-syn48-add: a synthetic `.S` / IR where DepositMessage.WithdrawalCredentials is a 48-byte add-form field
   (no development site has one): the theorem text has the add-form 48 shape and the parameters of the
   synthetic code. Text check only (no Lean code constant for a synthetic `.S`: not kernel-checked).
 - field-segments-partial: a mutant with `--partial-out`: the file is marked PARTIAL and `kindcheck.py` rejects it.
 - field-segments-compose-*: `--compose` = the committed `Prysm/BlobIdentifier/GeneratedDecodeAcceptComposition.lean` / `Prysm/DepositMessage/GeneratedDecodeAcceptComposition.lean` / `Prysm/Eth1Data/GeneratedDecodeAcceptComposition.lean` (two runs,
   identical; kindcheck PASS "identity-checked"); without `--same-as` the run warns on stderr and kindcheck
   rejects the file (no statement check); a field not covered, a tail store from another register and a
   shifted epilogue give exit 2 and 0 bytes.

field-segment fix cases (ids `field-segments-fix-*`):
 - field-segments-partial (changed): the `--field-segments --partial-out` file is a Lean module: imports first, then the PARTIAL header
   with an `UNCOVERED-JSON:` line; `kindcheck.py` exit 1 by default, exit 3 with `--partial`.
 - field-segments-fix-bh-partial: real BeaconBlockHeader (Slot, ProposerIndex are delegated overlay fields): exit 3, 0 bytes on
   stdout, partial file = the committed `lean/Prysm/BeaconBlockHeader/GeneratedDecodeFieldSegmentsPartial.lean`, two runs identical, kindcheck
   default exit 1, `--partial` exit 3 with `PARTIAL 3/5 fields`.
 - field-segments-fix-compose-*: `--compose` refusals, exit 2, 0 bytes, no partial file even with `--partial-out`: partial
   coverage (BeaconBlockHeader), frame 0x28, a non-contiguous field (a `nop` between two fields), uint64 first
   field (IR order of BlobIdentifier swapped: displacement 0, not covered).
 - field-segments-fix-no-same-as-marker: `--compose` without `--same-as` still exits 0; the theorem line carries
   `-- UNCHECKED STATEMENT` and the header says the statement is checked by nobody; kindcheck exit 1.
 - field-segments-fix-same-as-generated: `--same-as Prysm.BlobIdentifier.Decode.accept_generated_composition` (a generated theorem): exit 0, kindcheck
   exit 1.
 - field-segments-fix-same-as-prop: `--same-as-prop Prysm.BlobIdentifier.Decode.hand_statement`: exit 0, the Prop identity line, kindcheck PASS; the
   test fixture `field-segments-fix-bi-prop-fixture.lean` (the output with a scratch `abbrev` equal to the type of
   `Bi.bi_e2e_accept_main`) is written to <work-dir> for a separate gated `lake env lean`.

call-segment cases (`decoder --call-segments`; ids `call-segments-*`; mutated `.S` / IR copies in <work-dir> only):
 - call-segments-new-*: `--call-segments` on PendingPartialWithdrawal, Deposit_Data, BeaconBlockHeader: exit 0 twice, identical,
   every field covered, = the committed raw files `Prysm/PendingPartialWithdrawal/GeneratedDecodeCallSegments.lean`, `Prysm/Deposit_Data/GeneratedDecodeCallSegments.lean`, `Prysm/BeaconBlockHeader/GeneratedDecodeCallSegments.lean` when they
   exist; AttestationData: exit 3, Slot / CommitteeIndex / BeaconBlockRoot covered, Source / Target not
   (nested containers), partial file = committed `Prysm/AttestationData/GeneratedDecodeCallSegmentsPartial.lean` when it exists; `kindcheck.py` PASS
   (`--partial`: exit 3).
 - adversarial `.S` / IR mutants per call-segment shape: wrong callee symbol, callee without a proved spec (IR),
   `test` / `je` missing, `je` to a missing or an earlier label, set-up with an extra or a missing move, `nop` in
   an unobserved position (between `add` and `mov $0x8,%ecx`, after the `callq`, before `memmove`, before
   `mov $n,%ecx`, in the offset-0 form), two `nop`s, the two-directive read with swapped registers, wrong
   displacements against the IR, rdx as its register (clobbers the `lea` set-up), `lea` displacements against
   the IR, a reload set-up with another rdi constant or register, IR order swapped (SSZ offset of a first-form
   callee field not 0). Expected: the field is not covered (exit 3; no theorem whose name has the field) or
   exit 2; 0 bytes on stdout whenever the exit code is not 0; `--summary` agrees.
 - call-segments-compose-*: `--call-segments --compose` refuses callee / two-directive types (PendingPartialWithdrawal,
   BeaconBlockHeader: exit 2, 0 bytes); Deposit_Data composes (exit 0) with the `decAcceptKind` `_kind` line
   and the identity with `Prysm.Deposit_Data.Decode.accept_statement`; kindcheck PASS; = committed `Prysm/Deposit_Data/GeneratedDecodeAcceptComposition.lean` when it exists.

step cases (`decoder --steps`; ids `steps-*`; mutated `.S` / IR copies in <work-dir> only):
 - steps-new-*: `--steps` on the 10 development types: exit 0 twice (AttestationData: 3), identical, the expected
   covered fields, `kindcheck.py` PASS (`--partial`: exit 3), = the committed raw file `Gen4*.lean` when it exists.
 - steps-compose-refuse: `--steps --compose` exits 2 with the reason, 0 bytes, no file.
 - adversarial inputs for the dataflow (SyncCommitteeMessage, PendingConsolidation, PendingPartialWithdrawal,
   Eth1Data): a receiver / argument register clobbered between set-up and block, set-up moves in another VALID order
   (covered) and in an invalid order (refused), an extra harmless move and a fall-through label (covered), `nop` at
   start / middle / end / doubled (covered), a `nop` replaced by `cld` (one byte, no step lemma: refused),
   displacements off by 8 against the IR (refused), source / destination registers swapped at the call (refused),
   an unknown callee in the code or in the IR (refused), a label inside a call / segment window (refused), field order
   wrong in the IR or the code (refused), a receiver register outside the lemma's set, a reload from another slot,
   the buffer slot overwritten, a store through an unknown base, an indexed / rip operand, an immediate store, an rsp
   change. Expected: exit 0 with every field covered, or exit 3 with the stated covered fields (no theorem of an
   uncovered field: `kindcheck.py --partial` exit 3 on the partial file), 0 bytes on stdout unless exit 0; the
   summary's miss class is checked where stated. A covered mutant is a text result only (no Lean constant exists for
   mutated code): its theorems carry the mutated code's indices, never a parameter of the unmutated code.
 - steps-review-*: the reviewer's inputs (`rv` edits). The seven the step walker had accepted without the
   block entry being established (a05, a15, a29, a31, b05: an 8-byte stack store overlapping a tracked slot; b01, b02:
   head not the `decpro_seg` prologue) and b03 must be refused; a41 (extra head `nop`) is a head miss of class
   padding; a13 (wrong source offset) class other; stores to the return-address slot or below rsp, writes to r14 /
   rbp refused; the ten valid variants (a08, a14, a16, a19, a21, a27, a35, a38, b04, b06) stay covered. a34 (a
   store after the last field event) is refused by the epilogue rule (exit 2).
 - steps-review2-*: the reviewer's inputs and the systematic pass. The head size immediate must equal the IR
   SSZ fixed size (c34, d15, d16: exit 2, class other); a callee that is not the IR field's overlay type is refused
   (ValidatorIndex field calling Epoch.UnmarshalSSZ and the reverse); after the last field event only the plain return
   (`mov d(%rsp),%rax|%rbx`, `xor`, nops, labels, forward jmp, `add $F,%rsp; pop %rbp; retq`) is accepted: a store, a
   call or a wrong frame size there gives exit 2 with every field `reached` and not covered; a nop there stays covered.
   Every `--steps` case also checks the summary flag `reached` (true up to the first uncovered field, false after it,
   false for every field on a head miss); on exit 2 the summary lists every field.
 - steps-review3-*: the reviewer's inputs: a `jmp` after the last field event to a label that is not in
   the file (x01 `jmp runtime.abort`, x02 `jmp *%rdx`, x03 a tail `jmp` to Slot.UnmarshalSSZ): exit 2, every field not
   covered and `reached`.
 - steps-fail-closed-*: fail-closed. A harness (written to <work-dir>, run as one process per type on Eth1Data,
   SyncCommitteeMessage, PendingPartialWithdrawal) imports the working-tree `scalgen.py`, monkeypatches it and calls
   `main()`: an unexpected exception, a plain `G4Stop` and `SystemExit(0)` injected in the head (`g4_head`), at every
   `g4_parse` / `g4_label_index` call of the walk (each field, by the walk's current field), at every theorem-text
   call, in the epilogue (`g4_epilogue` raising, or returning None / True / another value than G4_EPI_OK), a walk
   that returns every field with a stop or without an end index, and an inner run that returns a text without the
   flags. Expected for every injection: exit 2 or 3 (exit 2 for an unexpected exception and SystemExit), 0 bytes on
   stdout, the summary's exit equal, fewer fields covered than the IR has. Control: no injection, exit 0.
whole-accept cases (`decoder --whole-accept`; ids `whole-accept-*`; mutated `.S` / IR copies in <work-dir> only):
 - whole-accept-new-*: `--whole-accept` on PendingDeposit, SyncCommitteeMessage, VoluntaryExit, PowBlock, ValidatorBalance: exit 0 twice,
   identical, every whole-accept theorem with its kind line, `kindcheck.py` PASS (rule 12: kind parameters recomputed from the
   IR and the `.S`); PendingPartialWithdrawal (interleaved fields) and AttestationData (nested fields): exit 2, 0 bytes.
 - adversarial inputs, each expected exit 2 with 0 bytes on stdout and `accept_generated: false` in the summary (no
   accept theorem): every class of the step reviews (stack-store overlap / misaligned store, head variants, size
   immediate, epilogue jump to a missing label, truncated file, callee of another overlay type) and the whole-accept rules
   (spill to a non-home slot, a register spilled twice, an extra `rcx` spill, `dB != F + 24`, an `xor` epilogue in a
   frame other than 0x20, an epilogue load of a non-zero slot, a `nop` inside the accept epilogue, a malformed
   size-error block, a stack store of an input value, a load from a stack slot outside the layout, interleaved
   fields); statement-level IR mutants (a wrong Go offset, a wrong size, the field order swapped, a Go offset that
   the code matches but that is not the kind's running sum). Valid variants (an extra harmless move, another valid
   set-up order): exit 0 and kindcheck PASS.
 - whole-accept-fail-closed-*: fail-closed. A harness imports the working-tree `scalgen.py`, takes its `gen5` module (`g5_module()`),
   monkeypatches it and calls `main()`: an unexpected exception, SystemExit(0) and a G5Refuse injected in the step
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
OLD_BLOB = "78e3339bc0ff3f20b6daa9a28582c97d7df9f712"
S = "prysm/go1.26.10/link-set/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Eth1Data.UnmarshalSSZ.S"
RECORD = "prysm/go1.26.10/e2e/e1/gen-e1dec.raw.txt"
COMMITTED = "lean/Prysm/Eth1Data/GeneratedDecodeRootFieldSegments.lean"
ARGS = ["--const", "unmarshalSSZ", "--ir", "prysm/ir/ir-mainnet.json", "--type", "v1alpha1.Eth1Data",
        "--prefix", "Decode.generated_root", "--imports", "Codec.Bytes32Decode,Codec.Bytes32DecodeOffsetZero,Prysm.Eth1Data.Code", "--open", "Prysm.Eth1Data.Code"]
OLD_ARGS = ["--const", "unmarshalSSZ", "--ir", "prysm/ir/ir-mainnet.json", "--type", "v1alpha1.Eth1Data",
            "--prefix", "Decode.generated_root", "--imports", "Codec.Bytes32Decode,Prysm.Eth1Data.Code", "--open", "Prysm.Eth1Data.Code"]

# (id, what, 1-based line, old text, new text or None = delete, expected exit, expected MATCH fields)
MUTANTS = [
    ("mutant-len", "wrong length: memmove count 0x10 in the offset-0 DepositRoot block", 31,
     "  mov $0x20,%ecx", "  mov $0x10,%ecx", 3, ["BlockHash"]),
    ("mutant-nomemmove", "missing memmove: the DepositRoot memmove call removed", 32,
     "  callq runtime.memmove", None, 3, ["BlockHash"]),
    ("mutant-addreg", "an add with a different register: BlockHash `add $0x28,%rsi`", 68,
     "  add $0x28,%rbx", "  add $0x28,%rsi", 3, ["DepositRoot"]),
    ("mutant-z-dest", "offset-0 form with a wrong destination: DepositRoot pointer stored at 0x10(%rdx)", 29,
     "  mov %rax,0x8(%rdx)", "  mov %rax,0x10(%rdx)", 3, ["BlockHash"]),
    ("mutant-z-nonzero", "offset-0 form at SSZ offset 40: the BlockHash add removed", 68,
     "  add $0x28,%rbx", None, 3, ["DepositRoot"]),
    ("mutant-both", "both fields broken: DepositRoot length and the BlockHash add register", None,
     None, None, 2, []),
    ("mutant-z-srcreg", "offset-0 form with the buffer reloaded into rsi (not the memmove source register)", 30,
     "  mov 0x38(%rsp),%rbx", "  mov 0x38(%rsp),%rsi", 3, ["BlockHash"]),
]


def run(argv, cwd):
    p = subprocess.run(argv, cwd=cwd, capture_output=True)
    return p.returncode, p.stdout, p.stderr.decode("utf-8", "replace")


def mutate(lines, line, old, new):
    if lines[line - 1] != old:
        raise SystemExit(f"mutant base mismatch at line {line}: {lines[line - 1]!r} != {old!r}")
    return lines[:line - 1] + ([] if new is None else [new]) + lines[line:]


H3N = "prysm/go1.26.10/link-set/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1."
E1S = S
IR = "prysm/ir/ir-mainnet.json"
G2 = {
    "E1": dict(S=E1S, type="v1alpha1.Eth1Data", committed="lean/Prysm/Eth1Data/GeneratedDecodeFieldSegments.lean",
               args=["--const", "unmarshalSSZ", "--prefix", "Decode.generated_field", "--imports",
                     "Codec.Bytes32Decode,Codec.Bytes32DecodeOffsetZero,Codec.InlineUint64,Prysm.Eth1Data.Code", "--open", "Prysm.Eth1Data.Code"],
               fields=["DepositRoot", "DepositCount", "BlockHash"]),
    "BI": dict(S=H3N + "BlobIdentifier.UnmarshalSSZ.S", type="v1alpha1.BlobIdentifier",
               committed="lean/Prysm/BlobIdentifier/GeneratedDecodeFieldSegments.lean", old="lean/Prysm/BlobIdentifier/GeneratedDecodeRootFieldSegments.lean",
               args=["--const", "unmarshalSSZ", "--prefix", "Decode.generated_field", "--imports",
                     "Codec.Bytes32Decode,Codec.Bytes32DecodeOffsetZero,Codec.InlineUint64,Prysm.BlobIdentifier.Code", "--open", "Prysm.BlobIdentifier.Code"],
               old_args=["--const", "unmarshalSSZ", "--prefix", "Decode.generated_root", "--imports",
                         "Codec.Bytes32Decode,Codec.Bytes32DecodeOffsetZero,Prysm.BlobIdentifier.Code", "--open", "Prysm.BlobIdentifier.Code"],
               fields=["BlockRoot", "Index"]),
    "DM": dict(S=H3N + "DepositMessage.UnmarshalSSZ.S", type="v1alpha1.DepositMessage",
               committed="lean/Prysm/DepositMessage/GeneratedDecodeFieldSegments.lean", old="lean/Prysm/DepositMessage/GeneratedDecodeRootFieldSegments.lean",
               args=["--const", "unmarshalSSZ", "--prefix", "Decode.generated_field", "--imports",
                     "Codec.Bytes32Decode,Codec.FixedBytesDecode,Codec.InlineUint64,Prysm.BlobIdentifier.Code", "--open", "Prysm.DepositMessage.Code"],
               old_args=["--const", "unmarshalSSZ", "--prefix", "Decode.generated_root", "--imports",
                         "Codec.Bytes32Decode,Codec.Bytes32DecodeOffsetZero,Prysm.BlobIdentifier.Code", "--open", "Prysm.DepositMessage.Code"],
               fields=["PublicKey", "WithdrawalCredentials", "Amount"]),
    "BH": dict(S="prysm/go1.26.10/link-set/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1."
                 "BeaconBlockHeader.UnmarshalSSZ.S", type="v1alpha1.BeaconBlockHeader",
               args=["--const", "unmarshalSSZ", "--prefix", "Decode.generated_field", "--imports",
                     "Codec.Bytes32Decode,Prysm.BeaconBlockHeader.Code", "--open", "Prysm.BeaconBlockHeader.Code"],
               fields=["Slot", "ProposerIndex", "ParentRoot", "StateRoot", "BodyRoot"]),
}


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


# (id, what, type key, .S edits or a function of the lines, IR edit or None, expected exit, expected covered)
G2_MUT = [
    ("field-segments-size-imm-head", "PublicKey makeslice size immediate 0x20 instead of 0x30 (IR 48)", "DM",
     [(16, "  mov $0x30,%ecx", "  mov $0x20,%ecx")], None, 3, ["WithdrawalCredentials", "Amount"]),
    ("field-segments-size-imm-memmove", "PublicKey memmove count 0x20 instead of 0x30 (offset-0 form)", "DM",
     [(31, "  mov $0x30,%ecx", "  mov $0x20,%ecx")], None, 3, ["WithdrawalCredentials", "Amount"]),
    ("field-segments-size-imm-len", "PublicKey len store 0x20 instead of 0x30 after memmove", "DM",
     [(34, "  movq $0x30,0x8(%rdx)", "  movq $0x20,0x8(%rdx)")], None, 3, ["WithdrawalCredentials", "Amount"]),
    ("field-segments-size-64", "PublicKey of 64 bytes in IR and code (size outside 32/48/96)", "DM",
     [(16, "  mov $0x30,%ecx", "  mov $0x40,%ecx"), (20, "  movq $0x30,0x10(%rdx)", "  movq $0x40,0x10(%rdx)"),
      (31, "  mov $0x30,%ecx", "  mov $0x40,%ecx"), (34, "  movq $0x30,0x8(%rdx)", "  movq $0x40,0x8(%rdx)"),
      (35, "  movq $0x30,0x10(%rdx)", "  movq $0x40,0x10(%rdx)")], ir_size("PublicKey", 64), 2, []),
    ("field-segments-size-20-ir", "PublicKey declared 20 bytes in the IR, code unchanged", "DM", [], ir_size("PublicKey", 20), 2, []),
    ("field-segments-u64-reg-mismatch-load", "Amount: `mov 0x50(%rcx),%rsi` (load into another register)", "DM",
     [(85, "  mov 0x50(%rcx),%rcx", "  mov 0x50(%rcx),%rsi")], None, 3, ["PublicKey", "WithdrawalCredentials"]),
    ("field-segments-u64-reg-mismatch-store", "Amount: `mov %rsi,0x30(%rdx)` (store from another register)", "DM",
     [(86, "  mov %rcx,0x30(%rdx)", "  mov %rsi,0x30(%rdx)")], None, 3, ["PublicKey", "WithdrawalCredentials"]),
    ("field-segments-u64-reg-mismatch-reload", "Amount: buffer reloaded into rdi, read through rcx", "DM",
     [(84, "  mov 0x38(%rsp),%rcx", "  mov 0x38(%rsp),%rdi")], None, 3, ["PublicKey", "WithdrawalCredentials"]),
    ("field-segments-u64-base-not-rsp", "Amount: buffer reload from 0x38(%rbp)", "DM",
     [(84, "  mov 0x38(%rsp),%rcx", "  mov 0x38(%rbp),%rcx")], None, 3, ["PublicKey", "WithdrawalCredentials"]),
    ("field-segments-u64-base-not-rdx", "Amount: store to 0x30(%rax) (receiver not in rdx)", "DM",
     [(86, "  mov %rcx,0x30(%rdx)", "  mov %rcx,0x30(%rax)")], None, 3, ["PublicKey", "WithdrawalCredentials"]),
    ("field-segments-u64-reg-rbp", "Amount: scratch register rbp (not in U64InlineReg)", "DM",
     [(84, "  mov 0x38(%rsp),%rcx", "  mov 0x38(%rsp),%rbp"), (85, "  mov 0x50(%rcx),%rcx", "  mov 0x50(%rbp),%rbp"),
      (86, "  mov %rcx,0x30(%rdx)", "  mov %rbp,0x30(%rdx)")], None, 3, ["PublicKey", "WithdrawalCredentials"]),
    ("field-segments-u64-src-disp", "Amount: source displacement 0x48 against IR SSZ offset 80", "DM",
     [(85, "  mov 0x50(%rcx),%rcx", "  mov 0x48(%rcx),%rcx")], None, 3, ["PublicKey", "WithdrawalCredentials"]),
    ("field-segments-u64-dst-disp", "Amount: receiver displacement 0x38 against IR Go offset 48", "DM",
     [(86, "  mov %rcx,0x30(%rdx)", "  mov %rcx,0x38(%rdx)")], None, 3, ["PublicKey", "WithdrawalCredentials"]),
    ("field-segments-u64-32bit", "Index: 32-bit register form `mov 0x20(%rcx),%ecx`", "BI",
     [(49, "  mov 0x20(%rcx),%rcx", "  mov 0x20(%rcx),%ecx")], None, 3, ["BlockRoot"]),
    ("field-segments-truncated-after-wc", "DepositMessage `.S` cut after directive 83 (Amount read missing)", "DM",
     lambda L: L[:84], None, 3, ["PublicKey", "WithdrawalCredentials"]),
    ("field-segments-truncated-in-pk", "DepositMessage `.S` cut inside the PublicKey segment (line 30)", "DM",
     lambda L: L[:30], None, 2, []),
    ("field-segments-ir-order-swap", "IR field order PublicKey / WithdrawalCredentials swapped (SSZ offsets move)", "DM",
     [], ir_swap("PublicKey", "WithdrawalCredentials"), 3, ["Amount"]),
    ("field-segments-code-order-swap", "Eth1Data code: the DepositCount read moved after the BlockHash segment", "E1",
     lambda L: L[:47] + L[50:86] + L[47:50] + L[86:], None, 2, []),
    ("field-segments-overlay", "real BeaconBlockHeader: Slot / ProposerIndex are delegated overlay fields", "BH",
     [], None, 3, ["ParentRoot", "StateRoot", "BodyRoot"]),
]


def gen2_cases(work, new):
    res, bad = [], 0
    irt = (KR / IR).read_text()
    # compatibility: default mode = committed files of hold-out types BlobIdentifier and DepositMessage
    for key in ("BI", "DM"):
        c = G2[key]
        rc, so, se = run(["python3", "-I", str(new), "decoder", "--S", c["S"], "--ir", IR, "--type", c["type"]]
                         + c["old_args"], KR)
        ok = rc == 0 and so == (KR / c["old"]).read_bytes()
        res.append(dict(id=f"field-segments-compat-{key}", expect=f"default mode exit 0, stdout = {c['old']}", exit=rc,
                        stdout_bytes=len(so), ok=bool(ok)))
        bad |= not ok
    # field-segment runs, twice, = committed raw output
    for key in ("E1", "BI", "DM"):
        c = G2[key]
        outs = []
        for i in range(2):
            sm = work / f"field-segments-new-{key}-{i}.json"
            rc, so, se = run(["python3", "-I", str(new), "decoder", "--field-segments", "--summary", str(sm), "--S", c["S"],
                              "--ir", IR, "--type", c["type"]] + c["args"], KR)
            outs.append((rc, so, json.loads(sm.read_text())))
        com = (KR / c["committed"]).read_bytes() if (KR / c["committed"]).exists() else None
        sm = outs[0][2]
        cov = [f["field"] for f in sm["fields"] if f["status"] == "covered"]
        ok = (all(r == 0 for r, _, _ in outs) and outs[0][1] == outs[1][1] and outs[0][1] == com
              and cov == c["fields"] and sm["exit"] == 0)
        res.append(dict(id=f"field-segments-new-{key}", expect=f"exit 0 twice, identical, = {c['committed']}, covered {c['fields']}",
                        exit=[r for r, _, _ in outs], stdout_bytes=len(outs[0][1]), deterministic=outs[0][1] == outs[1][1],
                        equals_committed=outs[0][1] == com, covered=cov, ok=bool(ok)))
        bad |= not ok
    # adversarial mutants
    for (mid, what, key, eds, iredit, want, cov_want) in G2_MUT:
        c = G2[key]
        base = (KR / c["S"]).read_text().split("\n")
        lines = eds(base) if callable(eds) else edits(base, eds)
        f = work / f"{mid}.S"
        f.write_text("\n".join(lines))
        irp = IR
        if iredit:
            irf = work / f"{mid}.ir.json"
            irf.write_text(ir_edit(irt, c["type"], iredit))
            irp = str(irf)
        sm = work / f"{mid}.summary.json"
        if sm.exists():
            sm.unlink()
        rc, so, se = run(["python3", "-I", str(new), "decoder", "--field-segments", "--summary", str(sm), "--S", str(f),
                          "--ir", irp, "--type", c["type"]] + c["args"], KR)
        s = json.loads(sm.read_text()) if sm.exists() else {}
        cov = [x["field"] for x in s.get("fields", []) if x.get("status") == "covered"]
        reasons = {x["field"]: x.get("reason") for x in s.get("fields", []) if x.get("status") != "covered"}
        ok = rc == want and so == b"" and s.get("exit") == rc and (want == 2 or cov == cov_want)
        res.append(dict(id=mid, what=what, expect=f"exit {want}, 0 bytes" + (f", covered {cov_want}" if want == 3 else ""),
                        exit=rc, stdout_bytes=len(so), covered=cov, not_covered=reasons,
                        stderr=se.strip().split("\n")[-6:], ok=bool(ok)))
        bad |= not ok
    # synthetic 48-byte add-form field (no development site)
    c = G2["DM"]
    base = (KR / c["S"]).read_text().split("\n")
    lines = edits(base, [(50, "  mov $0x20,%ecx", "  mov $0x30,%ecx"), (54, "  movq $0x20,0x28(%rdx)", "  movq $0x30,0x28(%rdx)"),
                         (67, "  mov $0x20,%ecx", "  mov $0x30,%ecx"), (70, "  movq $0x20,0x20(%rdx)", "  movq $0x30,0x20(%rdx)"),
                         (71, "  movq $0x20,0x28(%rdx)", "  movq $0x30,0x28(%rdx)"),
                         (85, "  mov 0x50(%rcx),%rcx", "  mov 0x60(%rcx),%rcx")])
    f = work / "field-segments-syn48-add.S"
    f.write_text("\n".join(lines))
    irf = work / "field-segments-syn48-add.ir.json"
    irf.write_text(ir_edit(irt, c["type"], ir_size("WithdrawalCredentials", 48)))
    rc, so, se = run(["python3", "-I", str(new), "decoder", "--field-segments", "--S", str(f), "--ir", str(irf), "--type", c["type"]]
                     + c["args"], KR)
    t = so.decode()
    want = ["@Codec.bytesDecSegKind h 48 unmarshalSSZ 47 61 48 56 24 24 32 40 48 := by",
            "with_reducible exact Codec.bytesdec_seg 48 (Or.inr (Or.inl rfl)) _ _ _ _ _ _ _ _ _ (k + 47) (k + 61) hA hB hl",
            "(hroot : root.length = 48)", "(hav : 48 ≤ avail)", "⋆ Heap (avail - 48)", "Eq ((Int.toBytes 8 48).At aL)",
            "Eq ((Int.toBytes 8 48).At aC)", "(hSrc : bf + (48 : Int64).toBitVec = aSrc)",
            "@Codec.u64DecInlineSegKind h unmarshalSSZ 83 56 96 48 := by"]
    miss = [w for w in want if w not in t]
    ok = rc == 0 and not miss and "length = 32" not in t.split("Decode.generated_field_WithdrawalCredentials_seg")[1].split("theorem")[0]
    res.append(dict(id="field-segments-syn48-add", what="synthetic 48-byte add-form field (text check only, not kernel-checked)",
                    expect="exit 0; add-form 48 shape with the synthetic parameters", exit=rc, stdout_bytes=len(so),
                    missing=miss, ok=bool(ok)))
    bad |= not ok
    # partial output on request, then kindcheck must reject it
    f = work / "field-segments-u64-src-disp.S"
    po = work / "field-segments-partial.lean"
    if po.exists():
        po.unlink()
    rc, so, se = run(["python3", "-I", str(new), "decoder", "--field-segments", "--S", str(f), "--partial-out", str(po), "--ir", IR,
                      "--type", c["type"]] + c["args"], KR)
    pt = po.read_text() if po.exists() else ""
    kc = subprocess.run(["python3", "-I", "-B", str(HERE / "kindcheck.py"), str(po)], capture_output=True, text=True)
    kp = subprocess.run(["python3", "-I", "-B", str(HERE / "kindcheck.py"), "--partial", str(po)], capture_output=True, text=True)
    ph = [l for l in pt.split("\n") if "PARTIAL OUTPUT" in l]
    uj = [json.loads(l.split(": ", 1)[1]) for l in pt.split("\n") if l.startswith("UNCOVERED-JSON: ")]
    ok = (rc == 3 and so == b"" and pt.startswith("import ") and len(ph) == 1 and "NOT generated: Amount" in ph[0]
          and uj and [u["field"] for u in uj[0]] == ["Amount"] and "Decode.generated_field_Amount_seg" not in pt
          and kc.returncode == 1 and kp.returncode == 3 and "PARTIAL 2/3 fields" in kp.stdout)
    res.append(dict(id="field-segments-partial", expect="exit 3, Lean-module PARTIAL file without Amount, kindcheck exit 1, --partial exit 3",
                    exit=rc, stdout_bytes=len(so), partial_header=ph, kindcheck_exit=kc.returncode,
                    kindcheck_partial_exit=kp.returncode, ok=bool(ok)))
    bad |= not ok
    # composition (`--compose`)
    CP = {"BI": ("Decode.accept_generated_composition", "Prysm.BlobIdentifier.Decode.accept", "lean/Prysm/BlobIdentifier/GeneratedDecodeAcceptComposition.lean",
                 "Codec.DecoderHeadEpilogue,Prysm.BlobIdentifier.GeneratedDecodeFieldSegments,Prysm.BlobIdentifier.DecodeAccept"),
          "DM": ("Decode.accept_generated_composition", "Prysm.DepositMessage.Decode.accept", "lean/Prysm/DepositMessage/GeneratedDecodeAcceptComposition.lean",
                 "Codec.DecoderHeadEpilogue,Prysm.DepositMessage.GeneratedDecodeFieldSegments,Prysm.DepositMessage.DecodeAccept"),
          "E1": ("Decode.accept_generated_composition", "Prysm.Eth1Data.Decode.accept", "lean/Prysm/Eth1Data/GeneratedDecodeAcceptComposition.lean",
                 "Codec.DecoderHeadEpilogue,Prysm.Eth1Data.GeneratedDecodeFieldSegments,Prysm.Eth1Data.DecodeAccept")}

    def cargs(key, same=True):
        c = G2[key]
        nm, ha, _, imps = CP[key]
        a = list(c["args"])
        a[a.index("--imports") + 1] = imps
        return (["decoder", "--field-segments", "--compose", "--name", nm] + (["--same-as", ha] if same else [])
                + ["--ir", IR, "--type", c["type"]] + a)

    for key in ("BI", "DM", "E1"):
        outs = [run(["python3", "-I", str(new)] + cargs(key) + ["--S", G2[key]["S"]], KR) for _ in range(2)]
        com = (KR / CP[key][2]).read_bytes() if (KR / CP[key][2]).exists() else None
        tf = work / f"field-segments-compose-{key}.lean"
        tf.write_bytes(outs[0][1])
        kc = subprocess.run(["python3", "-I", str(HERE / "kindcheck.py"), str(tf)], capture_output=True, text=True)
        ok = (outs[0][0] == 0 and outs[1][0] == 0 and outs[0][1] == outs[1][1] == com and kc.returncode == 0
              and f"identity against {CP[key][1]} — statement evidence only if" in kc.stdout)
        res.append(dict(id=f"field-segments-compose-new-{key}", expect=f"exit 0 twice, identical, = {CP[key][2]}, kindcheck identity PASS",
                        exit=[o[0] for o in outs], stdout_bytes=len(outs[0][1]), equals_committed=outs[0][1] == com,
                        kindcheck_exit=kc.returncode, ok=bool(ok)))
        bad |= not ok
    rc, so, se = run(["python3", "-I", str(new)] + cargs("BI", same=False) + ["--S", G2["BI"]["S"]], KR)
    tf = work / "field-segments-compose-nosame.lean"
    tf.write_bytes(so)
    kc = subprocess.run(["python3", "-I", str(HERE / "kindcheck.py"), str(tf)], capture_output=True, text=True)
    ok = rc == 0 and "NOT checked" in se and "NO statement check" in so.decode() and kc.returncode == 1
    res.append(dict(id="field-segments-compose-no-same-as", expect="exit 0, stderr says NOT checked, kindcheck exit 1", exit=rc,
                    stdout_bytes=len(so), kindcheck_exit=kc.returncode, ok=bool(ok)))
    bad |= not ok
    base = (KR / G2["DM"]["S"]).read_text().split("\n")
    for (mid, what, eds) in [
            ("field-segments-compose-not-covered", "Amount not covered (source displacement 0x48)", [(85, "  mov 0x50(%rcx),%rcx", "  mov 0x48(%rcx),%rcx")]),
            ("field-segments-compose-tail-reg", "PublicKey tail store from rsi instead of rdi", [(47, "  mov %rdi,(%rdx)", "  mov %rsi,(%rdx)")]),
            ("field-segments-compose-epilogue", "epilogue frame 0x28", [(89, "  add $0x20,%rsp", "  add $0x28,%rsp")])]:
        f = work / f"{mid}.S"
        f.write_text("\n".join(edits(base, eds)))
        rc, so, se = run(["python3", "-I", str(new)] + cargs("DM") + ["--S", str(f)], KR)
        ok = rc == 2 and so == b""
        res.append(dict(id=mid, what=what, expect="exit 2, 0 bytes", exit=rc, stdout_bytes=len(so),
                        stderr=se.strip().split("\n")[-1:], ok=bool(ok)))
        bad |= not ok
    r2, b2 = g2f_cases(work, new, cargs, CP, irt)
    return res + r2, bad | b2


GEN2_BH_PARTIAL = "lean/Prysm/BeaconBlockHeader/GeneratedDecodeFieldSegmentsPartial.lean"


def g2f_cases(work, new, cargs, CP, irt):
    """field-segment fix cases: partial output as a Lean module, compose refusals, statement markers."""
    res, bad = [], 0
    KC = ["python3", "-I", "-B", str(HERE / "kindcheck.py")]
    c = G2["BH"]
    outs = []
    for i in range(2):
        po = work / f"field-segments-fix-bh-partial-{i}.lean"
        if po.exists():
            po.unlink()
        rc, so, se = run(["python3", "-I", "-B", str(new), "decoder", "--field-segments", "--partial-out", str(po), "--S", c["S"],
                          "--ir", IR, "--type", c["type"]] + c["args"], KR)
        outs.append((rc, so, po.read_bytes() if po.exists() else b""))
    po = work / "field-segments-fix-bh-partial-0.lean"
    kc = subprocess.run(KC + [str(po)], capture_output=True, text=True)
    kp = subprocess.run(KC + ["--partial", str(po)], capture_output=True, text=True)
    com = (KR / GEN2_BH_PARTIAL).read_bytes() if (KR / GEN2_BH_PARTIAL).exists() else None
    pt = outs[0][2].decode()
    uj = [json.loads(l.split(": ", 1)[1]) for l in pt.split("\n") if l.startswith("UNCOVERED-JSON: ")]
    ok = (all(o[0] == 3 and o[1] == b"" for o in outs) and outs[0][2] == outs[1][2] and outs[0][2] == com
          and uj and [u["field"] for u in uj[0]] == ["Slot", "ProposerIndex"]
          and all("delegated overlay" in u["reason"] for u in uj[0])
          and kc.returncode == 1 and kp.returncode == 3 and "PARTIAL 3/5 fields" in kp.stdout)
    res.append(dict(id="field-segments-fix-bh-partial", expect=f"exit 3 twice, 0 bytes, file = {GEN2_BH_PARTIAL}, kindcheck 1, --partial 3",
                    exit=[o[0] for o in outs], stdout_bytes=len(outs[0][1]), equals_committed=outs[0][2] == com,
                    uncovered=uj, kindcheck_exit=kc.returncode, kindcheck_partial_exit=kp.returncode, ok=bool(ok)))
    bad |= not ok
    # --compose refusals
    dm = (KR / G2["DM"]["S"]).read_text().split("\n")
    bia = ["decoder", "--field-segments", "--compose", "--name", "Decode.accept_generated_composition", "--same-as", "Prysm.BlobIdentifier.Decode.accept"]
    for (mid, what, base_args, S_text, ir_text) in [
            ("field-segments-fix-compose-partial-bh", "partial coverage: real BeaconBlockHeader (3 of 5 fields)",
             ["decoder", "--field-segments", "--compose", "--name", "bh_e2e_accept_main_gc", "--ir", IR, "--type", c["type"]] + c["args"],
             None, None),
            ("field-segments-fix-compose-frame-0x28", "DepositMessage frame 0x28 (prologue and epilogue)", cargs("DM"),
             "\n".join(edits(dm, [(7, "  sub $0x20,%rsp", "  sub $0x28,%rsp"), (89, "  add $0x20,%rsp", "  add $0x28,%rsp")])), None),
            ("field-segments-fix-compose-not-contiguous", "DepositMessage: a nop between the PublicKey tail and WithdrawalCredentials",
             cargs("DM"), "\n".join(edits(dm, [(47, "  mov %rdi,(%rdx)", "  mov %rdi,(%rdx)\n  nop")])), None),
            ("field-segments-fix-compose-u64-first", "BlobIdentifier IR order swapped: uint64 Index first (displacement 0)",
             cargs("BI"), None, ir_edit(irt, G2["BI"]["type"], ir_swap("BlockRoot", "Index")))]:
        a = list(base_args)
        S = c["S"] if mid == "field-segments-fix-compose-partial-bh" else (G2["DM"]["S"] if mid != "field-segments-fix-compose-u64-first" else G2["BI"]["S"])
        if S_text is not None:
            f = work / f"{mid}.S"
            f.write_text(S_text)
            S = str(f)
        if ir_text is not None:
            f = work / f"{mid}.ir.json"
            f.write_text(ir_text)
            a[a.index("--ir") + 1] = str(f)
        po = work / f"{mid}.partial.lean"
        if po.exists():
            po.unlink()
        rc, so, se = run(["python3", "-I", "-B", str(new)] + a + ["--S", S, "--partial-out", str(po)], KR)
        ok = rc == 2 and so == b"" and not po.exists() and "no template match" in se
        res.append(dict(id=mid, what=what, expect="exit 2, 0 bytes, no partial file", exit=rc, stdout_bytes=len(so),
                        partial_file=po.exists(), stderr=se.strip().split("\n")[-1:], ok=bool(ok)))
        bad |= not ok
    # --compose without --same-as: marker
    rc, so, se = run(["python3", "-I", "-B", str(new)] + cargs("BI", same=False) + ["--S", G2["BI"]["S"]], KR)
    tf = work / "field-segments-fix-nosame.lean"
    tf.write_bytes(so)
    kc = subprocess.run(KC + [str(tf)], capture_output=True, text=True)
    th = [l for l in so.decode().split("\n") if l.startswith("theorem ")]
    ok = (rc == 0 and th and th[0].endswith("-- UNCHECKED STATEMENT: checked by nobody") and len(th) == 1
          and "checked by nobody" in so.decode().split("-/")[0] and kc.returncode == 1)
    res.append(dict(id="field-segments-fix-no-same-as-marker", expect="exit 0, UNCHECKED STATEMENT on the theorem line, kindcheck 1",
                    exit=rc, stdout_bytes=len(so), theorem_line_end=th[0][-45:] if th else None,
                    kindcheck_exit=kc.returncode, ok=bool(ok)))
    bad |= not ok
    # --same-as a generated theorem
    a = cargs("BI")
    a[a.index("--same-as") + 1] = "Prysm.BlobIdentifier.Decode.accept_generated_composition"
    a[a.index("--name") + 1] = "bi_selfgen_gc"  # the reviewer's case: another name, right-hand side generated
    rc, so, se = run(["python3", "-I", "-B", str(new)] + a + ["--S", G2["BI"]["S"]], KR)
    tf = work / "field-segments-fix-same-as-generated.lean"
    tf.write_bytes(so)
    kc = subprocess.run(KC + [str(tf)], capture_output=True, text=True)
    ok = rc == 0 and kc.returncode == 1 and "is a generated name" in kc.stdout
    res.append(dict(id="field-segments-fix-same-as-generated", expect="exit 0, kindcheck exit 1 (generated right-hand side)", exit=rc,
                    stdout_bytes=len(so), kindcheck_exit=kc.returncode, ok=bool(ok)))
    bad |= not ok
    # --same-as-prop
    a = cargs("BI")
    a[a.index("--same-as"):a.index("--same-as") + 2] = ["--same-as-prop", "Prysm.BlobIdentifier.Decode.hand_statement"]
    rc, so, se = run(["python3", "-I", "-B", str(new)] + a + ["--S", G2["BI"]["S"]], KR)
    t = so.decode()
    tf = work / "field-segments-fix-same-as-prop.lean"
    tf.write_bytes(so)
    kc = subprocess.run(KC + [str(tf)], capture_output=True, text=True)
    line = "    type_of% (@Decode.accept_generated_composition h) = @Prysm.BlobIdentifier.Decode.hand_statement h := by"
    com = (KR / CP["BI"][2]).read_text()
    ok = (rc == 0 and line in t and kc.returncode == 0 and "identity against Prysm.BlobIdentifier.Decode.hand_statement" in kc.stdout
          and t.split("\n/-- Statement check")[0].replace("Prysm.BlobIdentifier.Decode.hand_statement", "Prysm.BlobIdentifier.Decode.accept")
          == com.split("\n/-- Statement check")[0])
    imps, rest = t.split("\n\n", 1)
    (work / "field-segments-fix-bi-prop-fixture.lean").write_text(
        imps + "\n\n-- TEST FIXTURE (scratch, not in the library): a Prop-valued abbrev equal to the type of the hand\n"
        "-- theorem `Prysm.BlobIdentifier.Decode.accept`.\n"
        "abbrev Prysm.BlobIdentifier.Decode.hand_statement [h : Host] : Prop := type_of% (@Prysm.BlobIdentifier.Decode.accept h)\n\n" + rest)
    res.append(dict(id="field-segments-fix-same-as-prop", expect="exit 0, Prop identity line, kindcheck PASS; fixture written",
                    exit=rc, stdout_bytes=len(so), kindcheck_exit=kc.returncode, ok=bool(ok)))
    bad |= not ok
    return res, bad


H4N = "prysm/go1.26.10/link-set/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1."
G3 = {
    "PW": dict(S=H4N + "PendingPartialWithdrawal.UnmarshalSSZ.S", type="v1alpha1.PendingPartialWithdrawal",
               committed="lean/Prysm/PendingPartialWithdrawal/GeneratedDecodeCallSegments.lean",
               args=["--const", "unmarshalSSZ", "--prefix", "Decode.generated_call", "--imports", "Prysm.Deposit_Data.Code", "--open", "Prysm.PendingPartialWithdrawal.Code"],
               fields=["Index", "Amount", "WithdrawableEpoch"]),
    "DD": dict(S=H4N + "Deposit_Data.UnmarshalSSZ.S", type="v1alpha1.Deposit_Data", committed="lean/Prysm/Deposit_Data/GeneratedDecodeCallSegments.lean",
               args=["--const", "unmarshalSSZ", "--prefix", "Decode.generated_call", "--imports",
                     "Codec.Bytes32Decode,Codec.Bytes32DecodeOffsetZero,Codec.FixedBytesDecode,Codec.FixedBytesDecodePadding,Codec.InlineUint64,Prysm.Deposit_Data.Code",
                     "--open", "Prysm.Deposit_Data.Code"],
               fields=["PublicKey", "WithdrawalCredentials", "Amount", "Signature"]),
    "BH": dict(S=G2["BH"]["S"], type="v1alpha1.BeaconBlockHeader", committed="lean/Prysm/BeaconBlockHeader/GeneratedDecodeCallSegments.lean",
               args=["--const", "unmarshalSSZ", "--prefix", "Decode.generated_call", "--imports", "Codec.Bytes32Decode,Prysm.BeaconBlockHeader.Code",
                     "--open", "Prysm.BeaconBlockHeader.Code"],
               fields=["Slot", "ProposerIndex", "ParentRoot", "StateRoot", "BodyRoot"]),
    "AD": dict(S="prysm/go1.26.10/link-set/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1."
                 "AttestationData.UnmarshalSSZ.S", type="v1alpha1.AttestationData",
               committed="lean/Prysm/AttestationData/GeneratedDecodeCallSegmentsPartial.lean",
               args=["--const", "unmarshalSSZ", "--prefix", "Decode.generated_call", "--imports", "Codec.Bytes32Decode,Prysm.AttestationData.Code",
                     "--open", "Prysm.AttestationData.Code"],
               fields=["Slot", "CommitteeIndex", "BeaconBlockRoot", "Source", "Target"]),
}
PWL = "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingPartialWithdrawal.UnmarshalSSZ_"
PRIM = "github.com_OffchainLabs_prysm_v7_consensus_types_primitives."


def ir_overlay_name(field, name):
    def fn(t):
        for f in t["ir"]["fields"]:
            if f["key"] == field:
                f["v"]["name"] = name
                f["v"]["delegated_to"]["name"] = name
    return fn


# (id, what, type key, .S edits (1-based line, old, new or None) or a function of the lines, IR edit, exit, covered)
G3_MUT = [
    ("call-segments-wrong-callee", "Index: call to Epoch.UnmarshalSSZ (IR ValidatorIndex)", "PW",
     [(18, f"  callq {PRIM}ValidatorIndex.UnmarshalSSZ", f"  callq {PRIM}Epoch.UnmarshalSSZ")], None, 3,
     ["Amount", "WithdrawableEpoch"]),
    ("call-segments-callee-no-spec", "Index: callee Gwei.UnmarshalSSZ in code and IR (no proved callee spec)", "PW",
     [(18, f"  callq {PRIM}ValidatorIndex.UnmarshalSSZ", f"  callq {PRIM}Gwei.UnmarshalSSZ")], ir_overlay_name("Index", "Gwei"), 3,
     ["Amount", "WithdrawableEpoch"]),
    ("call-segments-test-missing", "Index: `test %rax,%rax` after the call removed", "PW", [(19, "  test %rax,%rax", None)], None, 3,
     ["Amount", "WithdrawableEpoch"]),
    ("call-segments-je-missing", "Index: `je` after the test replaced by `jne`", "PW",
     [(20, f"  je {PWL}b9", f"  jne {PWL}b9")], None, 3, ["Amount", "WithdrawableEpoch"]),
    ("call-segments-je-no-label", "Index: `je` to a label that does not exist", "PW",
     [(20, f"  je {PWL}b9", f"  je {PWL}zz")], None, 3, ["Amount", "WithdrawableEpoch"]),
    ("call-segments-je-earlier-label", "Index: `je` to the entry label (before the call)", "PW",
     [(20, f"  je {PWL}b9", f"  je {PWL}0")], None, 3, ["Amount", "WithdrawableEpoch"]),
    ("call-segments-setup-extra-move", "Index: `mov %rax,%rdx` between `add` and `mov $0x8,%ecx`", "PW",
     [(17, "  mov $0x8,%ecx", "  mov %rax,%rdx\n  mov $0x8,%ecx")], None, 3, ["Amount", "WithdrawableEpoch"]),
    ("call-segments-setup-missing-move", "Index: `mov $0x8,%ecx` removed", "PW", [(17, "  mov $0x8,%ecx", None)], None, 3,
     ["Amount", "WithdrawableEpoch"]),
    ("call-segments-setup-nop-between", "Index: `nop` between `add $0x8,%rax` and `mov $0x8,%ecx` (unobserved position)", "PW",
     [(17, "  mov $0x8,%ecx", "  nop\n  mov $0x8,%ecx")], None, 3, ["Amount", "WithdrawableEpoch"]),
    ("call-segments-nop-after-call", "Index: `nop` between the `callq` and `test`", "PW",
     [(19, "  test %rax,%rax", "  nop\n  test %rax,%rax")], None, 3, ["Amount", "WithdrawableEpoch"]),
    ("call-segments-first-add-other-reg", "Index: `add $0x8,%rbx` instead of rax", "PW", [(16, "  add $0x8,%rax", "  add $0x8,%rbx")], None, 3,
     ["Amount", "WithdrawableEpoch"]),
    ("call-segments-rr-swapped", "Amount: `mov 0x8(%rax),%r8; mov %r8,0x10(%rbx)` (bases swapped)", "PW",
     [(55, "  mov 0x8(%rbx),%r8", "  mov 0x8(%rax),%r8"), (56, "  mov %r8,0x10(%rax)", "  mov %r8,0x10(%rbx)")], None, 3, ["Index"]),
    ("call-segments-rr-two-regs", "Amount: `mov 0x8(%rbx),%r8; mov %r9,0x10(%rax)`", "PW",
     [(56, "  mov %r8,0x10(%rax)", "  mov %r9,0x10(%rax)")], None, 3, ["Index"]),
    ("call-segments-rr-src-disp", "Amount: source displacement 0x10 against IR SSZ offset 8", "PW",
     [(55, "  mov 0x8(%rbx),%r8", "  mov 0x10(%rbx),%r8")], None, 3, ["Index"]),
    ("call-segments-rr-dst-disp", "Amount: receiver displacement 0x18 against IR Go offset 16", "PW",
     [(56, "  mov %r8,0x10(%rax)", "  mov %r8,0x18(%rax)")], None, 3, ["Index"]),
    ("call-segments-rr-reg-rdx", "Amount read through rdx (clobbers the `lea` set-up register)", "PW",
     [(55, "  mov 0x8(%rbx),%r8", "  mov 0x8(%rbx),%rdx"), (56, "  mov %r8,0x10(%rax)", "  mov %rdx,0x10(%rax)")], None, 3,
     ["Index", "Amount"]),
    ("call-segments-rr-reg-rbp", "Amount read through rbp (not in U64ScratchRegister)", "PW",
     [(55, "  mov 0x8(%rbx),%r8", "  mov 0x8(%rbx),%rbp"), (56, "  mov %r8,0x10(%rax)", "  mov %rbp,0x10(%rax)")], None, 3,
     ["Index"]),
    ("call-segments-lea-src-disp", "WithdrawableEpoch: `lea 0x18(%rbx),%rdx` against IR SSZ offset 16", "PW",
     [(50, "  lea 0x10(%rbx),%rdx", "  lea 0x18(%rbx),%rdx")], None, 3, ["Index", "Amount"]),
    ("call-segments-lea-f-disp", "WithdrawableEpoch: `lea 0x20(%rax),%rsi` against IR Go offset 24", "PW",
     [(54, "  lea 0x18(%rax),%rsi", "  lea 0x20(%rax),%rsi")], None, 3, ["Index", "Amount"]),
    ("call-segments-lea-extra-move", "WithdrawableEpoch: an extra `mov %rdx,%rcx` before `mov %rsi,%rax`", "PW",
     [(57, "  mov %rsi,%rax", "  mov %rdx,%rcx\n  mov %rsi,%rax")], None, 3, ["Index", "Amount"]),
    ("call-segments-ir-swap-index-amount", "IR order Index / Amount swapped (Index at SSZ offset 8, Amount at 0)", "PW",
     [], ir_swap("Index", "Amount"), 2, []),
    ("call-segments-reload-c", "ProposerIndex: `add $-0x10,%rdi` (observed: minus the SSZ offset 8)", "BH",
     [(51, "  add $-0x8,%rdi", "  add $-0x10,%rdi")], None, 3, ["Slot", "ParentRoot", "StateRoot", "BodyRoot"]),
    ("call-segments-reload-reg", "ProposerIndex: buffer reloaded into rcx", "BH",
     [(48, "  mov 0x78(%rsp),%rbx", "  mov 0x78(%rsp),%rcx")], None, 3, ["Slot", "ParentRoot", "StateRoot", "BodyRoot"]),
    ("call-segments-two-nops-setup", "ProposerIndex: two `nop`s before the call", "BH",
     [(55, "  nop", "  nop\n  nop")], None, 3, ["Slot", "ParentRoot", "StateRoot", "BodyRoot"]),
    ("call-segments-reload-src-disp", "ProposerIndex: `add $0x10,%rbx` against IR SSZ offset 8", "BH",
     [(49, "  add $0x8,%rbx", "  add $0x10,%rbx")], None, 3, ["Slot", "ParentRoot", "StateRoot", "BodyRoot"]),
    ("call-segments-pad-two-nops", "WithdrawalCredentials: two `nop`s before makeslice", "DD",
     [(51, "  nop", "  nop\n  nop")], None, 3, ["PublicKey", "Amount", "Signature"]),
    ("call-segments-pad-before-memmove", "WithdrawalCredentials: `nop` before `callq runtime.memmove`", "DD",
     [(68, "  callq runtime.memmove", "  nop\n  callq runtime.memmove")], None, 3, ["PublicKey", "Amount", "Signature"]),
    ("call-segments-pad-before-size", "WithdrawalCredentials: `nop` before `mov $0x20,%ecx` (moved)", "DD",
     [(50, "  mov $0x20,%ecx", "  nop"), (51, "  nop", "  mov $0x20,%ecx")], None, 3, ["PublicKey", "Amount", "Signature"]),
    ("call-segments-pad-offset0", "PublicKey (offset-0 form): `nop` before makeslice", "DD",
     [(17, "  callq runtime.makeslice", "  nop\n  callq runtime.makeslice")], None, 3,
     ["WithdrawalCredentials", "Amount", "Signature"]),
]


def g3_cases(work, new):
    """The call-segment shapes, their adversarial inputs and the compose refusals / Deposit_Data (`DD`) composition."""
    res, bad = [], 0
    irt = (KR / IR).read_text()
    KC = ["python3", "-I", "-B", str(HERE / "kindcheck.py")]
    G = ["python3", "-I", "-B", str(new), "decoder", "--call-segments"]
    for key in ("PW", "DD", "BH", "AD"):
        c = G3[key]
        outs = []
        for i in range(2):
            po, su = work / f"call-segments-new-{key}-{i}.partial.lean", work / f"call-segments-new-{key}-{i}.json"
            for q in (po, su):
                if q.exists():
                    q.unlink()
            rc, so, se = run(G + ["--S", c["S"], "--ir", IR, "--type", c["type"], "--summary", str(su),
                                  "--partial-out", str(po)] + c["args"], KR)
            outs.append((rc, so, po.read_bytes() if po.exists() else b"", json.loads(su.read_text())))
        rc, so, pt, sm = outs[0]
        cov = [f["field"] for f in sm["fields"] if f["status"] == "covered"]
        text = so if key != "AD" else pt
        f = work / f"call-segments-new-{key}.lean"
        f.write_bytes(text)
        kc = subprocess.run(KC + (["--partial"] if key == "AD" else []) + [str(f)], capture_output=True, text=True)
        com = (KR / c["committed"]).read_bytes() if (KR / c["committed"]).exists() else None
        want_cov = c["fields"][:3] if key == "AD" else c["fields"]
        ok = (rc == (3 if key == "AD" else 0) and outs[0][:3] == outs[1][:3] and cov == want_cov
              and kc.returncode == (3 if key == "AD" else 0) and (com is None or com == text)
              and (key != "AD" or so == b""))
        res.append(dict(id=f"call-segments-new-{key}", expect=f"exit {3 if key == 'AD' else 0} twice, identical, covered {want_cov}, "
                        f"kindcheck PASS, = committed if present", exit=rc, stdout_bytes=len(so), covered=cov,
                        kindcheck_exit=kc.returncode, committed_present=com is not None,
                        equals_committed=(com == text) if com is not None else None, ok=bool(ok)))
        bad |= not ok
    for (mid, what, key, eds, irf, want, covw) in G3_MUT:
        c = G3[key]
        base = (KR / c["S"]).read_text().split("\n")
        lines = eds(base) if callable(eds) else edits(base, eds)
        fS = work / f"{mid}.S"
        fS.write_text("\n".join(lines))
        irp = KR / IR
        if irf:
            irp = work / f"{mid}.ir.json"
            irp.write_text(ir_edit(irt, c["type"], irf))
        po, su = work / f"{mid}.partial.lean", work / f"{mid}.json"
        for q in (po, su):
            if q.exists():
                q.unlink()
        rc, so, se = run(G + ["--S", str(fS), "--ir", str(irp), "--type", c["type"], "--summary", str(su),
                              "--partial-out", str(po)] + c["args"], KR)
        sm = json.loads(su.read_text()) if su.exists() else {}
        cov = [f["field"] for f in sm.get("fields", []) if f.get("status") == "covered"] if rc != 2 else []
        pt = po.read_text() if po.exists() else ""
        thm = [l.split()[1] for l in pt.split("\n") if l.startswith("theorem ")]
        unc = [f for f in c["fields"] if f not in covw]
        leak = [n for n in thm if any(f"_{u}_" in n for u in unc)]
        ok = (rc == want and so == b"" and sm.get("exit") == want and (want == 2 or cov == covw) and not leak
              and (want != 2 or not po.exists()))
        res.append(dict(id=mid, what=what, expect=f"exit {want}, 0 bytes" + (f", covered {covw}" if want == 3 else ""),
                        exit=rc, stdout_bytes=len(so), covered=cov, theorems_for_uncovered=leak,
                        reasons=[f.get("reason") for f in sm.get("fields", []) if f.get("status") != "covered"],
                        ok=bool(ok)))
        bad |= not ok
    # compose: refusals for callee / two-directive types, Deposit_Data composed with decAcceptKind
    for key in ("PW", "BH"):
        c = G3[key]
        po = work / f"call-segments-compose-{key}.partial.lean"
        if po.exists():
            po.unlink()
        rc, so, se = run(G + ["--compose", "--name", "x_g3", "--S", c["S"], "--ir", IR, "--type", c["type"],
                              "--partial-out", str(po)] + c["args"], KR)
        ok = rc == 2 and so == b"" and not po.exists() and "no composition" in se
        res.append(dict(id=f"call-segments-compose-refuse-{key}", expect="exit 2, 0 bytes, no file", exit=rc, stdout_bytes=len(so),
                        stderr=se.strip()[:300], ok=bool(ok)))
        bad |= not ok
    c = G3["DD"]
    outs = [run(G + ["--compose", "--name", "Decode.accept_generated_composition", "--same-as-prop", "Prysm.Deposit_Data.Decode.accept_statement",
                     "--S", c["S"], "--ir", IR, "--type", c["type"], "--const", "unmarshalSSZ", "--prefix", "Decode.generated_call",
                     "--imports", "Codec.DecoderHeadEpilogue,Prysm.Deposit_Data.GeneratedDecodeCallSegments,Prysm.Deposit_Data.Statements", "--open", "Prysm.Deposit_Data.Code"], KR)
            for _ in range(2)]
    rc, so, se = outs[0]
    f = work / "call-segments-compose-DD.lean"
    f.write_bytes(so)
    kc = subprocess.run(KC + [str(f)], capture_output=True, text=True)
    com = KR / "lean/Prysm/Deposit_Data/GeneratedDecodeAcceptComposition.lean"
    com = com.read_bytes() if com.exists() else None
    t = so.decode()
    ok = (rc == 0 and outs[0] == outs[1] and kc.returncode == 0 and "decAcceptKind" in kc.stdout
          and "@Codec.decAcceptKind h unmarshalSSZ true [.bytes 48, .bytes 32, .u64, .bytes 96] 106 := by" in t
          and "set_option maxHeartbeats 200000 in\ntheorem Decode.accept_generated_composition_kind" in t
          and "UNCHECKED" not in t and (com is None or com == so))
    res.append(dict(id="call-segments-compose-DD", expect="exit 0 twice, identical, decAcceptKind line + Prop identity, kindcheck PASS",
                    exit=rc, stdout_bytes=len(so), kindcheck_exit=kc.returncode, committed_present=com is not None,
                    ok=bool(ok)))
    bad |= not ok
    # --call-segments without a call-segment shape (Eth1Data) covers what --field-segments covers, with the same theorem text
    c2 = G2["E1"]
    rc, so, se = run(G + ["--S", c2["S"], "--ir", IR, "--type", c2["type"]] + c2["args"], KR)
    com = (KR / c2["committed"]).read_text()
    body = lambda s: s.split("namespace Prysm.Eth1Data\n", 1)[1]
    ok = rc == 0 and body(so.decode()) == body(com)
    res.append(dict(id="call-segments-e1-same-theorems-as-gen2", expect="exit 0, theorem text = committed Gen2E1Dec.lean body",
                    exit=rc, stdout_bytes=len(so), ok=bool(ok)))
    bad |= not ok
    return res, bad


H5N = "prysm/go1.26.10/link-set/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1."
PN = "github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1."


def g4c(sdir, tname, const, mod, pre, out, fields, cov=None):
    return dict(S=f"prysm/go1.26.10/link-set/{sdir}/{PN}{tname}.UnmarshalSSZ.S", type=f"v1alpha1.{tname}",
                committed=f"lean/Prysm/{tname}/GeneratedDecodeSteps" + ("Partial" if out.endswith("Partial") else "") + ".lean", args=["--const", const, "--prefix", "Decode.generated_step", "--imports", mod,
                                                             "--open", f"Prysm.{tname}.Code"],
                fields=fields, cov=fields if cov is None else cov)


G4 = {
    "CP": g4c("norm", "Checkpoint", "unmarshalSSZ", "Prysm.Checkpoint.Code", "cp", "Gen4CpDec", ["Epoch", "Root"]),
    "AD": g4c("norm", "AttestationData", "unmarshalSSZ", "Prysm.AttestationData.Code", "ad", "Gen4AdDecPartial",
              ["Slot", "CommitteeIndex", "BeaconBlockRoot", "Source", "Target"], ["Slot", "CommitteeIndex", "BeaconBlockRoot"]),
    "BH": g4c("norm", "BeaconBlockHeader", "unmarshalSSZ", "Prysm.BeaconBlockHeader.Code", "bh", "Gen4BhDec",
              ["Slot", "ProposerIndex", "ParentRoot", "StateRoot", "BodyRoot"]),
    "E1": g4c("norm", "Eth1Data", "unmarshalSSZ", "Prysm.Eth1Data.Code", "e1", "Gen4E1Dec",
              ["DepositRoot", "DepositCount", "BlockHash"]),
    "BI": g4c("norm", "BlobIdentifier", "unmarshalSSZ", "Prysm.BlobIdentifier.Code", "bi", "Gen4BiDec", ["BlockRoot", "Index"]),
    "DM": g4c("norm", "DepositMessage", "unmarshalSSZ", "Prysm.BlobIdentifier.Code", "dm", "Gen4DmDec",
              ["PublicKey", "WithdrawalCredentials", "Amount"]),
    "DD": g4c("norm", "Deposit_Data", "unmarshalSSZ", "Prysm.Deposit_Data.Code", "dd", "Gen4DdDec",
              ["PublicKey", "WithdrawalCredentials", "Amount", "Signature"]),
    "PW": g4c("norm", "PendingPartialWithdrawal", "unmarshalSSZ", "Prysm.Deposit_Data.Code", "pw", "Gen4PwDec",
              ["Index", "Amount", "WithdrawableEpoch"]),
    "SM": g4c("norm", "SyncCommitteeMessage", "unmarshalSSZ", "Prysm.SyncCommitteeMessage.Code", "sm", "Gen4SmDec",
              ["Slot", "BlockRoot", "ValidatorIndex", "Signature"]),
    "PC": g4c("norm", "PendingConsolidation", "unmarshalSSZ", "Prysm.SyncCommitteeMessage.Code", "pc", "Gen4PcDec",
              ["SourceIndex", "TargetIndex"]),
}
SMF, PCF, PWF = G4["SM"]["fields"], G4["PC"]["fields"], G4["PW"]["fields"]
SML = "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommitteeMessage.UnmarshalSSZ_"


def sm_vi(new):
    """SyncCommitteeMessage.ValidatorIndex set-up (lines 83–88) replaced by the lines `new`."""
    old = ["  mov 0x78(%rsp),%rbx", "  add $0x28,%rbx", "  mov 0x88(%rsp),%rdi", "  add $-0x28,%rdi", "  add $0x28,%rax",
           "  mov $0x8,%ecx"]

    def fn(L):
        assert L[82:88] == old, L[82:88]
        return L[:82] + new + L[88:]
    return fn


VI = ["  mov 0x78(%rsp),%rbx", "  add $0x28,%rbx", "  mov 0x88(%rsp),%rdi", "  add $-0x28,%rdi", "  add $0x28,%rax",
      "  mov $0x8,%ecx"]
# (id, what, type key, .S edits or function, IR edit, exit, covered, miss class of the first uncovered field or None)
G4_MUT = [
    ("steps-clobber-rax", "ValidatorIndex: `mov %rdx,%rax` after `add $0x28,%rax` (receiver clobbered before the call)", "SM",
     sm_vi(VI[:5] + ["  mov %rdx,%rax"] + VI[5:]), None, 3, SMF[:2], "register"),
    ("steps-clobber-rbx-callee-arg", "ValidatorIndex: `mov 0x88(%rsp),%rbx` after the rbx set-up (source register clobbered)", "SM",
     sm_vi(VI[:2] + ["  mov 0x88(%rsp),%rbx"] + VI[2:]), None, 3, SMF[:2], None),
    ("steps-order-valid", "ValidatorIndex: `add $0x28,%rax` first, then the rbx / rdi set-up (another valid order)", "SM",
     sm_vi([VI[4]] + VI[:4] + [VI[5]]), None, 0, SMF, None),
    ("steps-order-valid-ecx-first", "ValidatorIndex: `mov $0x8,%ecx` first (another valid order)", "SM",
     sm_vi([VI[5]] + VI[:5]), None, 0, SMF, None),
    ("steps-order-invalid", "ValidatorIndex: `add $0x28,%rbx` before `mov 0x78(%rsp),%rbx` (the load overwrites the add)", "SM",
     sm_vi([VI[1], VI[0]] + VI[2:]), None, 3, SMF[:2], "set-up order"),
    ("steps-extra-harmless", "ValidatorIndex: an extra `mov %rdi,%rsi` in the set-up", "SM",
     sm_vi(VI[:4] + ["  mov %rdi,%rsi"] + VI[4:]), None, 0, SMF, None),
    ("steps-label-fallthrough", "ValidatorIndex: a fall-through label between two set-up moves (label step)", "SM",
     sm_vi(VI[:2] + [f"{SML}zz:"] + VI[2:]), None, 0, SMF, None),
    ("steps-nop-start", "ValidatorIndex: `nop` before the first set-up move", "SM", sm_vi(["  nop"] + VI), None, 0, SMF, None),
    ("steps-nop-middle", "ValidatorIndex: `nop` between `add $0x28,%rbx` and `mov 0x88(%rsp),%rdi`", "SM",
     sm_vi(VI[:2] + ["  nop"] + VI[2:]), None, 0, SMF, None),
    ("steps-nop-end", "ValidatorIndex: `nop` between `mov $0x8,%ecx` and the `callq`", "SM", sm_vi(VI + ["  nop"]), None, 0, SMF, None),
    ("steps-nop-doubled-after-call", "ValidatorIndex: two `nop`s between the `callq` and `test`", "SM",
     [(90, "  test %rax,%rax", "  nop\n  nop\n  test %rax,%rax")], None, 0, SMF, None),
    ("steps-nop-in-segment", "Signature: `nop` before `callq runtime.memmove` and two before makeslice", "SM",
     [(141, "  callq runtime.memmove", "  nop\n  callq runtime.memmove"), (124, "  nop", "  nop\n  nop")], None, 0, SMF, None),
    ("steps-cld-for-nop-seg", "Signature: the `nop` before makeslice replaced by `cld` (one byte, no step lemma)", "SM",
     [(124, "  nop", "  cld")], None, 3, SMF[:3], "new directive form"),
    ("steps-cld-for-nop-call", "TargetIndex: the `nop` after the `callq` replaced by `cld`", "PC",
     [(57, "  nop", "  cld")], None, 3, PCF[:1], "new directive form"),
    ("steps-cld-in-setup", "TargetIndex: `cld` in the set-up (no step lemma)", "PC",
     [(53, "  mov 0x58(%rsp),%rax", "  cld\n  mov 0x58(%rsp),%rax")], None, 3, PCF[:1], "new directive form"),
    ("steps-disp-f-off8", "ValidatorIndex: `add $0x30,%rax` (Go offset 0x28 in the IR)", "SM",
     sm_vi(VI[:4] + ["  add $0x30,%rax"] + VI[5:]), None, 3, SMF[:2], "other"),
    ("steps-disp-src-off8", "ValidatorIndex: `add $0x30,%rbx` (SSZ offset 0x28 in the IR)", "SM",
     sm_vi([VI[0], "  add $0x30,%rbx"] + VI[2:]), None, 3, SMF[:2], None),
    ("steps-swapped-call-regs", "WithdrawableEpoch: `mov %rsi,%rbx; mov %rdx,%rax` (source / destination swapped)", "PW",
     [(57, "  mov %rsi,%rax", "  mov %rsi,%rbx"), (58, "  mov %rdx,%rbx", "  mov %rdx,%rax")], None, 3, PWF[:2], "register"),
    ("steps-unknown-callee-code", "TargetIndex: `callq …Gwei.UnmarshalSSZ` in the code (IR ValidatorIndex)", "PC",
     [(56, f"  callq {PRIM}ValidatorIndex.UnmarshalSSZ", f"  callq {PRIM}Gwei.UnmarshalSSZ")], None, 3, PCF[:1], None),
    ("steps-unknown-callee-ir", "TargetIndex: callee Gwei.UnmarshalSSZ in code and IR (no proved spec)", "PC",
     [(56, f"  callq {PRIM}ValidatorIndex.UnmarshalSSZ", f"  callq {PRIM}Gwei.UnmarshalSSZ")],
     ir_overlay_name("TargetIndex", "Gwei"), 3, PCF[:1], "new field kind"),
    ("steps-label-in-call-window", "TargetIndex: the `nop` after the `callq` replaced by a label (inside the call window)", "PC",
     [(57, "  nop", "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingConsolidation.UnmarshalSSZ_zz:")],
     None, 3, PCF[:1], "other"),
    ("steps-label-in-seg-window", "Signature: a label between `xor %ebx,%ebx` and `mov $0x60,%ecx` (inside the segment window)", "SM",
     [(123, "  mov $0x60,%ecx", f"{SML}zz:\n  mov $0x60,%ecx")], None, 3, SMF[:3], "other"),
    ("steps-ir-order-swap", "IR order Amount / WithdrawableEpoch swapped (wrong field order)", "PW",
     [], ir_swap("Amount", "WithdrawableEpoch"), 3, PWF[:1], "set-up order"),
    ("steps-code-order-swap", "Eth1Data code: the DepositCount read moved after the BlockHash segment", "E1",
     lambda L: L[:47] + L[50:86] + L[47:50] + L[86:], None, 3, ["DepositRoot"], "set-up order"),
    ("steps-ry-rbx", "BlockRoot: receiver reloaded into rbx after memmove (not in the lemma's set)", "SM",
     [(68, "  mov 0x70(%rsp),%rax", "  mov 0x70(%rsp),%rbx"), (69, "  movq $0x20,0x18(%rax)", "  movq $0x20,0x18(%rbx)"),
      (70, "  movq $0x20,0x20(%rax)", "  movq $0x20,0x20(%rbx)")], None, 3, SMF[:1], "register"),
    ("steps-reload-other-slot", "BlockRoot: second receiver reload from 0x68(%rsp)", "SM",
     [(68, "  mov 0x70(%rsp),%rax", "  mov 0x68(%rsp),%rax")], None, 3, SMF[:1], "other"),
    ("steps-buffer-slot-overwritten", "Signature: `mov %rax,0x78(%rsp)` before the segment (buffer slot overwritten)", "SM",
     [(119, "  mov %rbx,0x30(%rsp)", "  mov %rbx,0x30(%rsp)\n  mov %rax,0x78(%rsp)")], None, 3, SMF[:3], "register"),
    ("steps-store-unknown-base", "ValidatorIndex: `mov %rax,0x8(%rcx)` in the set-up (store through an unknown base)", "SM",
     sm_vi(VI[:2] + ["  mov %rax,0x8(%rcx)"] + VI[2:]), None, 3, SMF[:2], "register"),
    ("steps-indexed-operand", "Amount: `mov 0x8(%rbx,%rcx,1),%r8` (index operand)", "PW",
     [(55, "  mov 0x8(%rbx),%r8", "  mov 0x8(%rbx,%rcx,1),%r8")], None, 3, PWF[:1], "new directive form"),
    ("steps-imm-store", "TargetIndex: `movq $0x0,0x40(%rsp)` in the set-up (immediate store)", "PC",
     [(53, "  mov 0x58(%rsp),%rax", "  movq $0x0,0x40(%rsp)\n  mov 0x58(%rsp),%rax")], None, 3, PCF[:1], "new directive form"),
    ("steps-rip-load", "TargetIndex: `mov ssz.ErrSize(%rip),%rdi` in the set-up", "PC",
     [(53, "  mov 0x58(%rsp),%rax", "  mov ssz.ErrSize(%rip),%rdi\n  mov 0x58(%rsp),%rax")], None, 3, PCF[:1], "new directive form"),
    ("steps-rsp-change", "TargetIndex: `add $0x8,%rsp` in the set-up", "PC",
     [(53, "  mov 0x58(%rsp),%rax", "  add $0x8,%rsp\n  mov 0x58(%rsp),%rax")], None, 3, PCF[:1], None),
    ("steps-movi-len-16", "TargetIndex: `mov $0x10,%ecx` (rcx = 16 at the call)", "PC",
     [(55, "  mov $0x8,%ecx", "  mov $0x10,%ecx")], None, 3, PCF[:1], None),
    ("steps-u64-src-disp", "Amount: `mov 0x10(%rbx),%r8` (SSZ offset 8 in the IR)", "PW",
     [(55, "  mov 0x8(%rbx),%r8", "  mov 0x10(%rbx),%r8")], None, 3, PWF[:1], "other"),
    ("steps-u64-dst-disp", "Amount: store to 0x18(%rax), the Go offset of WithdrawableEpoch", "PW",
     [(56, "  mov %r8,0x10(%rax)", "  mov %r8,0x18(%rax)")], None, 3, PWF[:1], "set-up order"),
]



def rv(eds):
    """Edits in the form of the reviewer's scripts (`tmp/exp4.py`, `exp5.py`): (1-based line, old suffix, new); new None =
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


E1F = G4["E1"]["fields"]
SMJ = SML[:-1]
# The reviewer's inputs (ids `steps-review-<reviewer id>`). The seven inputs the step walker accepted although
# the code does not establish the block entry must be refused; the eleven valid variants stay covered; plus
# head-miss classes and the frame / goroutine register rule.
G4F_MUT = [
    ("steps-review-a05", "8-byte stack store at 0x7c overlaps the buffer slot 0x78 (M1a)", "SM",
     rv([(83, "mov 0x78(%rsp),%rbx", ("before", ["mov %rdi,0x7c(%rsp)"]))]), None, 3, SMF[:2], "other"),
    ("steps-review-a15", "a05 with nops around the store (M1a)", "SM",
     rv([(83, "mov 0x78(%rsp),%rbx", ("before", ["nop", "mov %rdi,0x7c(%rsp)", "nop"])),
         (88, "mov $0x8,%ecx", ("before", ["nop"]))]), None, 3, SMF[:2], "other"),
    ("steps-review-a29", "8-byte stack store at 0x3c overlaps the buffer slot 0x38 (M1a)", "E1",
     rv([(48, "mov 0x38(%rsp),%rsi", ("before", ["mov %rdx,0x3c(%rsp)"]))]), None, 3, E1F[:1], "other"),
    ("steps-review-a31", "8-byte stack store at 0x34 overlaps the receiver slot 0x30 before the segment (M1a)", "E1",
     rv([(51, "lea type__+387072(%rip),%rax", ("before", ["mov %rsi,0x34(%rsp)"]))]), None, 3, E1F[:2], "other"),
    ("steps-review-b05", "8-byte stack store at 0x34 overlaps the buffer slot 0x38 from below (M1a)", "E1",
     rv([(48, "mov 0x38(%rsp),%rsi", ("before", ["mov %rdx,0x34(%rsp)"]))]), None, 3, E1F[:1], "other"),
    ("steps-review-b01", "head: receiver spilled before `push %rbp` (M1b)", "SM",
     rv([(5, "push %rbp", ("before", ["mov %rax,0x70(%rsp)"])), (9, "nop", None), (12, "mov %rax,0x70(%rsp)", None)]),
     None, 2, [], "other"),
    ("steps-review-b02", "head: `sub $0x60,%rsp` replaced by `nop` (frame never allocated) (M1b)", "SM",
     rv([(7, "sub $0x60,%rsp", "nop")]), None, 2, [], "other"),
    ("steps-review-b03", "head: a spill at 0x74 and `mov %rcx,0x70(%rsp)` at directive 8 (M1b)", "SM",
     rv([(9, "nop", "mov %rcx,0x70(%rsp)"), (12, "mov %rax,0x70(%rsp)", "mov %rax,0x74(%rsp)")]), None, 2, [], "other"),
    ("steps-review-a41", "head: an extra `nop` moves `cmp $size,%rcx` to directive 10 (S1: class padding)", "SM",
     rv([(9, "nop", ["nop", "nop"])]), None, 2, [], "padding"),
    ("steps-review-a13", "ValidatorIndex source `add $0x0,%rbx` (S1: wrong offset is class other)", "SM",
     rv([(84, "add $0x28,%rbx", "add $0x0,%rbx")]), None, 3, SMF[:2], "other"),
    ("steps-review-a43", "ValidatorIndex: receiver reloaded after its add (class set-up order)", "SM",
     rv([(87, "add $0x28,%rax", ["add $0x28,%rax", "mov 0x70(%rsp),%rax"])]), None, 3, SMF[:2], "set-up order"),
    ("steps-review-store-retaddr", "ValidatorIndex: `mov %rdi,0x68(%rsp)` (the return-address slot, frame 0x60)", "SM",
     sm_vi(VI[:2] + ["  mov %rdi,0x68(%rsp)"] + VI[2:]), None, 3, SMF[:2], "other"),
    ("steps-review-store-below-sp", "ValidatorIndex: `mov %rdi,-0x8(%rsp)` (below rsp)", "SM",
     sm_vi(VI[:2] + ["  mov %rdi,-0x8(%rsp)"] + VI[2:]), None, 3, SMF[:2], "other"),
    ("steps-review-write-r14", "ValidatorIndex: `mov %rdx,%r14` in the set-up (goroutine register)", "SM",
     sm_vi(VI[:2] + ["  mov %rdx,%r14"] + VI[2:]), None, 3, SMF[:2], "other"),
    ("steps-review-write-rbp", "ValidatorIndex: `lea 0x8(%rax),%rbp` in the set-up (frame pointer)", "SM",
     sm_vi(VI[:2] + ["  lea 0x8(%rax),%rbp"] + VI[2:]), None, 3, SMF[:2], "other"),
    # the eleven valid variants of the reviewer (covered)
    ("steps-review-a08", "fall-through label in the ValidatorIndex set-up", "SM",
     rv([(87, "add $0x28,%rax", ("before", [SMJ + "_zz:"]))]), None, 0, SMF, None),
    ("steps-review-a14", "nops at 25 positions", "SM",
     rv([(x, "", ("before", ["nop"])) for x in (16, 17, 18, 19, 20, 48, 51, 53, 62, 65, 67, 70, 73, 82, 84, 86, 88, 89, 90,
                                                 91, 119, 126, 141, 147, 156)]), None, 0, SMF, None),
    ("steps-review-a16", "spill + reload of the receiver through 0x48(%rsp)", "SM",
     rv([(87, "add $0x28,%rax", ("before", ["mov %rax,0x48(%rsp)", "mov 0x48(%rsp),%rax"]))]), None, 0, SMF, None),
    ("steps-review-a19", "forward jmp over a junk directive", "SM",
     rv([(87, "add $0x28,%rax", ("before", ["jmp " + SMJ + "_yy", "xor %eax,%eax", SMJ + "_yy:"]))]), None, 0, SMF, None),
    ("steps-review-a21", "rcx = 16 - 8", "SM", rv([(88, "mov $0x8,%ecx", ["mov $0x10,%ecx", "add $-0x8,%rcx"])]), None, 0, SMF, None),
    ("steps-review-a27", "DepositCount value moved through rcx", "E1",
     rv([(50, "mov %rsi,0x20(%rdx)", ["mov %rsi,%rcx", "nop", "mov %rcx,0x20(%rdx)"])]), None, 0, E1F, None),
    ("steps-review-a34", "store after the last field event (second review: epilogue rule, refused)", "E1",
     rv([(87, "xor %eax,%eax", ("before", ["mov %rsi,0x20(%rdx)"]))]), None, 2, [], "other"),
    ("steps-review-a35", "buffer reloaded from sp + 8 after the call", "PC",
     rv([(49, "mov 0x60(%rsp),%rbx", "mov 0x8(%rsp),%rbx")]), None, 0, PCF, None),
    ("steps-review-a38", "receiver in another frame slot across the call", "PC",
     rv([(16, "add $0x8,%rax", ("before", ["mov %rax,0x30(%rsp)"])), (53, "mov 0x58(%rsp),%rax", "mov 0x30(%rsp),%rax")]),
     None, 0, PCF, None),
    ("steps-review-b04", "no nil check in the head", "SM", rv([(15, "test %al,(%rax)", None)]), None, 0, SMF, None),
    ("steps-review-b06", "aligned store to the neighbour slot 0x40", "E1",
     rv([(48, "mov 0x38(%rsp),%rsi", ("before", ["mov %rdx,0x40(%rsp)"]))]), None, 0, E1F, None),
]

# Head size immediate vs the IR, and the systematic pass (callee vs the IR overlay
# type, the directives after the last field event)
G4F2_MUT = [
    ("steps-review2-c34", "head: `cmp $0x10,%rcx` (IR SSZ size 0x90) (M3)", "SM",
     rv([(10, "cmp $0x90,%rcx", "cmp $0x10,%rcx")]), None, 2, [], "other"),
    ("steps-review2-d15", "head: `cmp $0x20,%rcx` (IR SSZ size 0x48) (M3)", "E1",
     rv([(10, "cmp $0x48,%rcx", "cmp $0x20,%rcx")]), None, 2, [], "other"),
    ("steps-review2-d16", "head: `cmp $0x100,%rcx` (IR SSZ size 0x48) (M3)", "E1",
     rv([(10, "cmp $0x48,%rcx", "cmp $0x100,%rcx")]), None, 2, [], "other"),
    ("steps-review2-callee-vi-epoch", "Index (IR ValidatorIndex): `callq …Epoch.UnmarshalSSZ` (callee not the overlay type)", "PW",
     rv([(18, f"callq {PRIM}ValidatorIndex.UnmarshalSSZ", f"callq {PRIM}Epoch.UnmarshalSSZ")]), None, 2, [], "set-up order"),
    ("steps-review2-callee-epoch-vi", "WithdrawableEpoch (IR Epoch): `callq …ValidatorIndex.UnmarshalSSZ`", "PW",
     rv([(60, f"callq {PRIM}Epoch.UnmarshalSSZ", f"callq {PRIM}ValidatorIndex.UnmarshalSSZ")]), None, 3, PWF[:2], "other"),
    ("steps-review2-epi-call", "a `callq …Epoch.UnmarshalSSZ` after the last field event", "E1",
     rv([(87, "xor %eax,%eax", ("before", [f"callq {PRIM}Epoch.UnmarshalSSZ"]))]), None, 2, [], "other"),
    ("steps-review2-epi-store-rsp", "a stack store `mov %rsi,0x8(%rsp)` after the last field event", "E1",
     rv([(87, "xor %eax,%eax", ("before", ["mov %rsi,0x8(%rsp)"]))]), None, 2, [], "other"),
    ("steps-review2-epi-frame", "`add $0x28,%rsp` (head frame 0x20) after the last field event", "E1",
     rv([(89, "add $0x20,%rsp", "add $0x28,%rsp")]), None, 2, [], "other"),
    ("steps-review2-epi-nop-valid", "a `nop` in the epilogue (plain return: covered)", "E1",
     rv([(89, "add $0x20,%rsp", ("before", ["nop"]))]), None, 0, E1F, None),
]

# An epilogue `jmp` to a label that is not in the file
G4F3_MUT = [
    ("steps-review3-x01", "Eth1Data: `jmp runtime.abort` in place of `xor %eax,%eax` after the last field event (M4)", "E1",
     rv([(87, "xor %eax,%eax", "jmp runtime.abort")]), None, 2, [], "other"),
    ("steps-review3-x02", "Eth1Data: `jmp *%rdx` in place of `xor %eax,%eax` after the last field event (M4)", "E1",
     rv([(87, "xor %eax,%eax", "jmp *%rdx")]), None, 2, [], "other"),
    ("steps-review3-x03", "SyncCommitteeMessage: a tail `jmp …Slot.UnmarshalSSZ` after the last field event (M4)", "SM",
     rv([(157, "mov 0x28(%rsp),%rax", ("before", ["jmp " + PRIM + "Slot.UnmarshalSSZ"]))]), None, 2, [], "other"),
]

# The fail-closed harness (written to <work-dir>; argv: scalgen.py config.json result.json; cwd = fv/kraken)
FC_HARNESS = r'''
import contextlib, importlib.util, io, json, pathlib, sys
spec = importlib.util.spec_from_file_location("scalgen_fc", sys.argv[1])
sg = importlib.util.module_from_spec(spec)
spec.loader.exec_module(sg)
ARGV = list(sys.argv)  # call() replaces sys.argv
cfg = json.loads(pathlib.Path(ARGV[2]).read_text())
SU = pathlib.Path(cfg["summary"])


class Boom(Exception):
    """an exception class the generator does not know"""


def call():
    sys.argv = ["scalgen.py"] + cfg["argv"] + ["--summary", str(SU)]
    SU.unlink(missing_ok=True)
    so, se = io.StringIO(), io.StringIO()
    with contextlib.redirect_stdout(so), contextlib.redirect_stderr(se):
        try:
            sg.main()
            rc = 0
        except SystemExit as e:
            rc = e.code if isinstance(e.code, int) else (0 if e.code is None else 1)
        except BaseException as e:
            rc = "uncaught " + type(e).__name__
    sm = json.loads(SU.read_text()) if SU.exists() else None
    return rc, len(so.getvalue()), sm


def fire(kind, where):
    if kind == "unexpected":
        raise Boom("injected at " + where)
    if kind == "g4stop":
        raise sg.G4Stop(0, "injected plain G4Stop at " + where, "other")
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
    res.append(dict(phase=phase, kind=kind, where=where, rc=rc, stdout=nso, sm_exit=(sm or {}).get("exit"),
                    covered=(sm or {}).get("covered"), total=(sm or {}).get("total")))


rec("control", "none", "", call())
for kind in ("unexpected", "g4stop", "sysexit0"):
    rec("head", kind, "g4_head", patched("g4_head", lambda *a, k=kind: fire(k, "g4_head")))
rec("head", "returns None", "g4_head", patched("g4_head", lambda *a: None))
# the walk: count the g4_parse / g4_label_index calls and the current field of each (the walk's local `cur`)
for fn in ("g4_parse", "g4_label_index"):
    orig, seq = getattr(sg, fn), []

    def counter(*a, orig=orig, seq=seq):
        seq.append(sys._getframe(1).f_locals.get("cur"))
        return orig(*a)
    patched(fn, counter)
    for kind in ("unexpected", "g4stop", "sysexit0"):
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
origs = {fn: getattr(sg, fn) for fn in ("g4_step_text", "g4_call_text", "g4_seg_text")}
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
for kind in ("unexpected", "g4stop", "sysexit0"):
    rec("epilogue", kind, "g4_epilogue", patched("g4_epilogue", lambda *a, k=kind: fire(k, "g4_epilogue")))
rec("epilogue", "G4EpiMiss", "g4_epilogue",
    patched("g4_epilogue", lambda *a: (_ for _ in ()).throw(sg.G4EpiMiss(0, "injected", "other"))))
for v in (None, True, "ok", 0):
    rec("epilogue", f"returns {v!r}", "g4_epilogue", patched("g4_epilogue", lambda *a, v=v: v))
ow = sg.g4_walk
rec("flags", "walk: every field done, with a stop", "g4_walk",
    patched("g4_walk", lambda *a: (lambda r: (r[0], sg.G4Stop(0, "injected", "other"), r[2]))(ow(*a))))
rec("flags", "walk: every field done, no end index", "g4_walk",
    patched("g4_walk", lambda *a: (lambda r: (r[0], None, None))(ow(*a))))
oi = sg._p2dec_gen4
rec("flags", "inner returns its full text, outer flags not set", "_p2dec_gen4",
    patched("_p2dec_gen4", lambda args, flags: oi(args, dict(flags))))
rec("flags", "inner sets two flags", "_p2dec_gen4",
    patched("_p2dec_gen4", lambda args, flags: (flags.update(head_ok=True, fields_complete=True), oi(args, dict(flags)))[1]))
pathlib.Path(ARGV[3]).write_text(json.dumps(res) + "\n")
'''


def fc_cases(work, new):
    """Fail-closed injections (FC_HARNESS) on Eth1Data, SyncCommitteeMessage, PendingPartialWithdrawal."""
    res, bad = [], 0
    h = work / "fc_harness.py"
    h.write_text(FC_HARNESS)
    for key in ("E1", "SM", "PW"):
        c = G4[key]
        cfg, out = work / f"steps-fail-closed-{key}.cfg.json", work / f"steps-fail-closed-{key}.result.json"
        cfg.write_text(json.dumps(dict(argv=["decoder", "--steps", "--S", c["S"], "--ir", IR, "--type", c["type"]] + c["args"],
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
                         and r["sm_exit"] == r["rc"] and r["total"] == n and r["covered"] < n for r in rs)
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


def g4_cases(work, new):
    """`--steps` on the development types, compose refusal, dataflow adversarial inputs."""
    res, bad = [], 0
    irt = (KR / IR).read_text()
    KC = ["python3", "-I", "-B", str(HERE / "kindcheck.py")]
    G = ["python3", "-I", "-B", str(new), "decoder", "--steps"]
    for key, c in G4.items():
        outs = []
        for i in range(2):
            po, su = work / f"steps-new-{key}-{i}.partial.lean", work / f"steps-new-{key}-{i}.json"
            for q in (po, su):
                if q.exists():
                    q.unlink()
            rc, so, se = run(G + ["--S", c["S"], "--ir", IR, "--type", c["type"], "--summary", str(su),
                                  "--partial-out", str(po)] + c["args"], KR)
            outs.append((rc, so, po.read_bytes() if po.exists() else b"", json.loads(su.read_text())))
        rc, so, pt, sm = outs[0]
        part = c["cov"] != c["fields"]
        cov = [f["field"] for f in sm["fields"] if f["status"] == "covered"]
        text = pt if part else so
        f = work / f"steps-new-{key}.lean"
        f.write_bytes(text)
        kc = subprocess.run(KC + (["--partial"] if part else []) + [str(f)], capture_output=True, text=True)
        com = (KR / c["committed"]).read_bytes() if (KR / c["committed"]).exists() else None
        ok = (rc == (3 if part else 0) and outs[0][:3] == outs[1][:3] and cov == c["cov"]
              and kc.returncode == (3 if part else 0) and (com is None or com == text) and (not part or so == b""))
        res.append(dict(id=f"steps-new-{key}", expect=f"exit {3 if part else 0} twice, identical, covered {c['cov']}, "
                        f"kindcheck PASS, = committed if present", exit=rc, stdout_bytes=len(so), covered=cov,
                        kindcheck_exit=kc.returncode, committed_present=com is not None,
                        equals_committed=(com == text) if com is not None else None, ok=bool(ok)))
        bad |= not ok
    c = G4["SM"]
    po = work / "steps-compose.partial.lean"
    if po.exists():
        po.unlink()
    rc, so, se = run(G + ["--compose", "--name", "x_g4", "--S", c["S"], "--ir", IR, "--type", c["type"],
                          "--partial-out", str(po)] + c["args"], KR)
    ok = rc == 2 and so == b"" and not po.exists() and "--steps --compose: refused" in se
    res.append(dict(id="steps-compose-refuse", expect="exit 2, 0 bytes, no file, reason", exit=rc, stdout_bytes=len(so),
                    stderr=se.strip()[:300], ok=bool(ok)))
    bad |= not ok
    for (mid, what, key, eds, irf, want, covw, mcls) in G4_MUT + G4F_MUT + G4F2_MUT + G4F3_MUT:
        c = G4[key]
        base = (KR / c["S"]).read_text().split("\n")
        lines = eds(base) if callable(eds) else edits(base, eds)
        fS = work / f"{mid}.S"
        fS.write_text("\n".join(lines))
        irp = KR / IR
        if irf:
            irp = work / f"{mid}.ir.json"
            irp.write_text(ir_edit(irt, c["type"], irf))
        po, su = work / f"{mid}.partial.lean", work / f"{mid}.json"
        for q in (po, su):
            if q.exists():
                q.unlink()
        rc, so, se = run(G + ["--S", str(fS), "--ir", str(irp), "--type", c["type"], "--summary", str(su),
                              "--partial-out", str(po)] + c["args"], KR)
        sm = json.loads(su.read_text()) if su.exists() else {}
        cov = [f["field"] for f in sm.get("fields", []) if f.get("status") == "covered"] if rc != 2 else []
        unc = [f for f in sm.get("fields", []) if f.get("status") != "covered"]
        kcr = None
        if rc == 3:
            kcr = subprocess.run(KC + ["--partial", str(po)], capture_output=True, text=True).returncode
        elif rc == 0:
            fo = work / f"{mid}.lean"
            fo.write_bytes(so)
            kcr = subprocess.run(KC + [str(fo)], capture_output=True, text=True).returncode
        # `reached` is true up to the first uncovered field and false after it (every field on a head miss)
        fl = sm.get("fields", [])
        x0 = next((x for x, f in enumerate(fl) if f.get("status") != "covered"), len(fl))
        head_miss = sm.get("head", {}).get("status") == "not covered"
        # on an epilogue miss every field was reached
        epi_miss = sm.get("epilogue", {}).get("status") == "not covered"
        reach_ok = all(f.get("reached") == (False if head_miss else True if epi_miss else x <= x0)
                       for x, f in enumerate(fl))
        ok = (rc == want and (so == b"") == (want != 0) and sm.get("exit") == want and cov == covw
              and kcr == {3: 3, 0: 0}.get(want) and (mcls is None or (unc and unc[0].get("miss_class") == mcls))
              and reach_ok and (want != 2 or len(fl) == len(c["fields"])))
        res.append(dict(id=mid, what=what, expect=f"exit {want}, covered {covw}" + (f", miss class {mcls}" if mcls else ""),
                        exit=rc, stdout_bytes=len(so), covered=cov, kindcheck_exit=kcr,
                        uncovered=[(f["field"], f.get("miss_class"), f.get("reason")) for f in unc], ok=bool(ok)))
        bad |= not ok
    return res, bad


# ---------------------------------------------------------------------------------------------- whole-accept

def g5c(sdir, tname, const, mod, pre, extra=()):
    return dict(S=f"prysm/go1.26.10/link-set/{sdir}/{PN}{tname}.UnmarshalSSZ.S", type=f"v1alpha1.{tname}",
                args=["--const", const, "--prefix", "Decode.generated", "--imports", mod, "--open", f"Prysm.{tname}.Code", *extra])


G5 = {
    "PD": g5c("norm", "PendingDeposit", "unmarshalSSZ", "Prysm.PendingDeposit.Code", "pd",
              ["--same-as-prop", "Prysm.PendingDeposit.Decode.accept_statement"]),
    "SM": g5c("norm", "SyncCommitteeMessage", "unmarshalSSZ", "Prysm.SyncCommitteeMessage.Code", "sm",
              ["--same-as-prop", "Prysm.SyncCommitteeMessage.Decode.accept_statement"]),
    "VE": g5c("norm", "VoluntaryExit", "unmarshalSSZ", "Prysm.PendingDeposit.Code", "ve"),
    "PB": g5c("norm", "PowBlock", "unmarshalSSZ", "Prysm.PendingDeposit.Code", "pb", ["--same-as-prop", "Prysm.PowBlock.Decode.accept_statement"]),
    "VB": g5c("norm", "ValidatorBalance", "unmarshalSSZ", "Prysm.PendingDeposit.Code", "vb"),
    "PW": g5c("norm", "PendingPartialWithdrawal", "unmarshalSSZ", "Prysm.Deposit_Data.Code", "pw"),
    "AD": g5c("norm", "AttestationData", "unmarshalSSZ", "Prysm.AttestationData.Code", "ad"),
}


def ir_goff(field, off):
    def fn(t):
        for f in t["go_fields"]:
            if f["name"] == field:
                f["offset_gc_amd64"] = off
    return fn


PDL = "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingDeposit.UnmarshalSSZ_"
# (id, what, type key, .S edit function or None, IR edit or None, expected exit)
G5_MUT = [
    # classes of the step reviews (the step front end refuses; whole-accept emits nothing)
    ("whole-accept-store-misaligned", "PendingDeposit Amount: `mov %rsi,0x2c(%rsp)` before the receiver store (misaligned stack store)",
     "PD", rv([(88, "mov %rsi,0x38(%rdx)", ("before", ["mov %rsi,0x2c(%rsp)"]))]), None, 2),
    ("whole-accept-store-overlap-bf", "PendingDeposit Amount: `mov %rdx,0x58(%rsp)` overwrites the buffer slot before its reload",
     "PD", rv([(86, "mov 0x58(%rsp),%rsi", ("before", ["mov %rdx,0x58(%rsp)"]))]), None, 2),
    ("whole-accept-head-spill-before-push", "VoluntaryExit: a spill `mov %rax,0x58(%rsp)` before `push %rbp`", "VE",
     rv([(5, "push %rbp", ("before", ["mov %rax,0x58(%rsp)"]))]), None, 2),
    ("whole-accept-head-no-frame", "VoluntaryExit: `sub $0x48,%rsp` removed (frame never allocated)", "VE",
     rv([(7, "sub $0x48,%rsp", "nop")]), None, 2),
    ("whole-accept-head-nop-moved", "VoluntaryExit: the head `nop` moved before `cmp 0x10(%r14),%rsp`", "VE",
     rv([(9, "nop", None), (3, "cmp 0x10(%r14),%rsp", ("before", ["nop"]))]), None, 2),
    ("whole-accept-size-imm", "VoluntaryExit: `cmp $0x18,%rcx` (IR SSZ size 16)", "VE", rv([(10, "cmp $0x10,%rcx", "cmp $0x18,%rcx")]), None, 2),
    ("whole-accept-epi-jmp-missing", "PowBlock: `jmp runtime.abort` in place of `xor %eax,%eax` after the last field event", "PB",
     rv([(120, "xor %eax,%eax", "jmp runtime.abort")]), None, 2),
    ("whole-accept-truncated", "SyncCommitteeMessage `.S` cut inside the Signature segment", "SM", lambda L: L[:140], None, 2),
    ("whole-accept-truncated-epi", "VoluntaryExit `.S` cut after `add $0x48,%rsp` of the accept epilogue", "VE", lambda L: L[:87], None, 2),
    ("whole-accept-callee-other-type", "VoluntaryExit: the ValidatorIndex field calls Epoch.UnmarshalSSZ", "VE",
     lambda L: [l.replace("ValidatorIndex.UnmarshalSSZ", "Epoch.UnmarshalSSZ") for l in L], None, 2),
    # whole-accept rules (the step front end covers these inputs; whole-accept refuses)
    ("whole-accept-head-rdi-not-home", "PendingDeposit: `mov %rdi,0x70(%rsp)` (rdi home slot 0x68)", "PD",
     rv([(13, "mov %rdi,0x68(%rsp)", "mov %rdi,0x70(%rsp)")]), None, 2),
    ("whole-accept-head-spill-twice", "PendingDeposit: `mov %rax,0x50(%rsp)` twice", "PD",
     rv([(12, "mov %rax,0x50(%rsp)", ["mov %rax,0x50(%rsp)", "mov %rax,0x50(%rsp)"])]), None, 2),
    ("whole-accept-head-rcx-spill", "VoluntaryExit: an extra spill `mov %rcx,0x68(%rsp)` (no rcx slot in the kind)", "VE",
     rv([(15, "test %al,(%rax)", ("before", ["mov %rcx,0x68(%rsp)"]))]), None, 2),
    ("whole-accept-head-db", "ValidatorBalance: decoderPrologue spills rbx to 0x48 (dB != F + 24)", "VB",
     rv([(8, "mov %rbx,0x50(%rsp)", "mov %rbx,0x48(%rsp)")]), None, 2),
    ("whole-accept-epi-xor-frame48", "VoluntaryExit: `xor %eax,%eax; xor %ebx,%ebx` before `add $0x48,%rsp` (no xor lemma in frame 0x48)",
     "VE", rv([(87, "add $0x48,%rsp", ("before", ["xor %eax,%eax", "xor %ebx,%ebx"]))]), None, 2),
    ("whole-accept-epi-load-ptr-slot", "SyncCommitteeMessage: epilogue `mov 0x38(%rsp),%rax` (the pointer slot, not a zero slot)", "SM",
     rv([(157, "mov 0x28(%rsp),%rax", "mov 0x38(%rsp),%rax")]), None, 2),
    ("whole-accept-epi-nop", "PendingDeposit: a `nop` between `add $0x40,%rsp` and `pop %rbp` of the accept epilogue", "PD",
     rv([(163, "pop %rbp", ("before", ["nop"]))]), None, 2),
    ("whole-accept-reject-errsize", "SyncCommitteeMessage: size-error block loads ssz.ErrOffset", "SM",
     rv([(163, "mov ssz.ErrSize(%rip),%rax", "mov ssz.ErrOffset(%rip),%rax")]), None, 2),
    ("whole-accept-reject-frame", "VoluntaryExit: size-error block `add $0x40,%rsp` (frame 0x48)", "VE",
     rv([(93, "add $0x48,%rsp", "add $0x40,%rsp")]), None, 2),
    ("whole-accept-store-input", "PendingDeposit Amount: `mov %rsi,0x30(%rsp)` stores the input word into a frame slot", "PD",
     rv([(88, "mov %rsi,0x38(%rdx)", ("before", ["mov %rsi,0x30(%rsp)"]))]), None, 2),
    ("whole-accept-load-outside-layout", "ValidatorBalance Balance: `mov 0x30(%rsp),%rsi` (no stack chunk at 0x30)", "VB",
     rv([(52, "mov %rcx,0x10(%rdx)", ("before", ["mov 0x30(%rsp),%rsi"]))]), None, 2),
    ("whole-accept-interleaved", "real PendingPartialWithdrawal: the Epoch set-up runs inside the Amount field", "PW", None, None, 2),
    ("whole-accept-nested", "real AttestationData: Source / Target are nested containers (step exit 3)", "AD", None, None, 2),
    # statement-level IR mutants
    ("whole-accept-ir-goff", "IR: PowBlock ParentHash Go offset 32 (code 24)", "PB", None, ir_goff("ParentHash", 32), 2),
    ("whole-accept-ir-size", "IR: PowBlock TotalDifficulty of 48 bytes (code 32)", "PB", None, ir_size("TotalDifficulty", 48), 2),
    ("whole-accept-ir-order", "IR: VoluntaryExit Epoch / ValidatorIndex order swapped", "VE", None, ir_swap("Epoch", "ValidatorIndex"), 2),
    ("whole-accept-ir-goff-code", "IR and code: ValidatorBalance Balance at Go offset 24 (code store 0x18; not the running sum 16)", "VB",
     rv([(52, "mov %rcx,0x10(%rdx)", "mov %rcx,0x18(%rdx)")]), ir_goff("Balance", 24), 2),
    ("whole-accept-ir-goff-first", "IR: VoluntaryExit Epoch Go offset 0 (code 8, state word)", "VE", None, ir_goff("Epoch", 0), 2),
    # valid variants: generated, kindcheck PASS
    ("whole-accept-valid-extra-move", "SyncCommitteeMessage: an extra `mov %rdi,%rsi` in the ValidatorIndex set-up", "SM",
     sm_vi(VI[:4] + ["  mov %rdi,%rsi"] + VI[4:]), None, 0),
    ("whole-accept-valid-order", "SyncCommitteeMessage: ValidatorIndex set-up with `mov $0x8,%ecx` first", "SM",
     sm_vi([VI[5]] + VI[:5]), None, 0),
]


def g5_run(work, new, mid, c, S=None, ir=None, extra=()):
    su = work / f"{mid}.g5.json"
    su.unlink(missing_ok=True)
    rc, so, se = run(["python3", "-I", "-B", str(new), "decoder", "--whole-accept", "--S", S or c["S"], "--ir", ir or IR,
                      "--type", c["type"], "--summary", str(su)] + c["args"] + list(extra), KR)
    sm = json.loads(su.read_text()) if su.exists() else {}
    return rc, so, se, sm


def g5_cases(work, new):
    """`--whole-accept` on real types, adversarial inputs, valid variants."""
    res, bad = [], 0
    KC = ["python3", "-I", "-B", str(HERE / "kindcheck.py")]
    irt = (KR / IR).read_text()
    for key in ("PD", "SM", "VE", "PB", "VB", "PW", "AD"):
        c = G5[key]
        r1, r2 = g5_run(work, new, f"whole-accept-new-{key}-1", c), g5_run(work, new, f"whole-accept-new-{key}-2", c)
        want = 2 if key in ("PW", "AD") else 0
        kc = None
        if r1[0] == 0:
            f = work / f"whole-accept-new-{key}.lean"
            f.write_bytes(r1[1])
            kc = subprocess.run(KC + [str(f)], capture_output=True, text=True).returncode
        t = r1[1].decode()
        pre = c["args"][3]
        thm = all(f"\ntheorem {pre}_{x} : " in t and f"\ntheorem {pre}_{x}_kind : " in t
                  for x in ("head", "f1", "epi", "accept", "reject")) if want == 0 else True
        ok = (r1[0] == want and r1[:2] == r2[:2] and (r1[1] == b"") == (want != 0) and thm and kc == (0 if want == 0 else None)
              and r1[3].get("exit") == want and r1[3].get("accept_generated") == (want == 0))
        res.append(dict(id=f"whole-accept-new-{key}", expect=f"exit {want} twice, identical" + (", every whole-accept theorem kinded, kindcheck "
                        "PASS" if want == 0 else ", 0 bytes, accept_generated false"), exit=r1[0], stdout_bytes=len(r1[1]),
                        kindcheck_exit=kc, reason=r1[3].get("reason", "")[:300], ok=bool(ok)))
        bad |= not ok
    for (mid, what, key, eds, irf, want) in G5_MUT:
        c = G5[key]
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
        rc, so, se, sm = g5_run(work, new, mid, c, S, irp)
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


# the whole-accept fail-closed harness (written to <work-dir>; argv: scalgen.py config.json result.json; cwd = fv/kraken)
G5FC_HARNESS = r"""
import contextlib, importlib.util, io, json, pathlib, sys
spec = importlib.util.spec_from_file_location("scalgen_g5fc", sys.argv[1])
sg = importlib.util.module_from_spec(spec)
spec.loader.exec_module(sg)
g5 = sg.g5_module()
ARGV = list(sys.argv)
cfg = json.loads(pathlib.Path(ARGV[2]).read_text())
SU = pathlib.Path(cfg["summary"])


class Boom(Exception):
    pass


def call():
    sys.argv = ["scalgen.py"] + cfg["argv"] + ["--summary", str(SU)]
    SU.unlink(missing_ok=True)
    so, se = io.StringIO(), io.StringIO()
    with contextlib.redirect_stdout(so), contextlib.redirect_stderr(se):
        try:
            sg.main()
            rc = 0
        except SystemExit as e:
            rc = e.code if isinstance(e.code, int) else (0 if e.code is None else 1)
        except BaseException as e:
            rc = "uncaught " + type(e).__name__
    sm = json.loads(SU.read_text()) if SU.exists() else None
    return rc, len(so.getvalue()), sm


def fire(kind, where):
    if kind == "unexpected":
        raise Boom("injected at " + where)
    if kind == "refuse":
        raise g5.G5Refuse("injected at " + where)
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
    res.append(dict(phase=phase, kind=kind, where=where, rc=rc, stdout=nso, sm_exit=(sm or {}).get("exit"),
                    acc=(sm or {}).get("accept_generated")))


rec("control", "none", "", call())
KINDS = ("unexpected", "refuse", "sysexit0")
# phase gen4: the front end and the recomputed walk / epilogue
for kind in KINDS:
    rec("gen4", kind, "p2dec_gen4", patched(sg, "p2dec_gen4", lambda *a, k=kind: fire(k, "p2dec_gen4")))
    rec("gen4", kind, "g4_walk", patched(sg, "g4_walk", lambda *a, k=kind: fire(k, "g4_walk")))
    rec("gen4", kind, "g4_epilogue", patched(sg, "g4_epilogue", lambda *a, k=kind: fire(k, "g4_epilogue")))
o4 = sg.p2dec_gen4
rec("gen4", "returns None", "p2dec_gen4", patched(sg, "p2dec_gen4", lambda *a: None))
rec("gen4", "returns a cut text", "p2dec_gen4", patched(sg, "p2dec_gen4", lambda *a: o4(*a)[:-20]))
ow = sg.g4_walk
rec("gen4", "walk with a stop", "g4_walk", patched(sg, "g4_walk", lambda *a: (lambda r: (r[0], sg.G4Stop(0, "x", "other"), r[2]))(ow(*a))))
rec("gen4", "epilogue returns True", "g4_epilogue", patched(sg, "g4_epilogue", lambda *a: True))
# phase derive: the specifications and every step rendering
for fn in ("g5_derive", "g5_head_spec", "g5_epi_spec", "g5_reject_spec"):
    for kind in KINDS:
        rec("derive", kind, fn, patched(g5, fn, lambda *a, k=kind, fn=fn: fire(k, fn)))
ostep, seq = g5.g5_step, []
setattr(g5, "g5_step", lambda *a: (seq.append(1), ostep(*a))[1])
call()
setattr(g5, "g5_step", ostep)
for kind in KINDS:
    for n in range(len(seq)):
        cnt = [0]

        def inj(*a, n=n, kind=kind, cnt=cnt):
            cnt[0] += 1
            if cnt[0] == n + 1:
                fire(kind, f"g5_step call {n}")
            return ostep(*a)
        rec("derive", kind, f"g5_step call {n}", patched(g5, "g5_step", inj))
# phase render: every theorem renderer (each call), the kind recorder
for meth in ("head", "field", "f_u64", "f_bytes", "f_call", "epi", "accept", "reject", "layout", "binders", "mem"):
    om, seqm = getattr(g5.T, meth), []
    setattr(g5.T, meth, lambda self, *a, om=om, seqm=seqm: (seqm.append(1), om(self, *a))[1])
    call()
    setattr(g5.T, meth, om)
    for kind in KINDS:
        for n in range(len(seqm)):
            cnt = [0]

            def inj(self, *a, n=n, kind=kind, cnt=cnt, om=om, meth=meth):
                cnt[0] += 1
                if cnt[0] == n + 1:
                    fire(kind, f"T.{meth} call {n}")
                return om(self, *a)
            rec("render", kind, f"T.{meth} call {n}", patched(g5.T, meth, inj))
ok_ = g5.T.kind
rec("flags", "a kind line not recorded", "T.kind", patched(g5.T, "kind", lambda self, name, kind, extra: (
    ok_(self, name, kind, extra), self.kinds_emitted.pop() if name.endswith("_f1") else None)[0]))
rec("flags", "a kind line dropped from the text", "T.body", patched(g5.T, "body", (lambda ob: lambda self: ob(self).replace(
    "_epi_kind :", "_epi_kinx :", 1))(g5.T.body)))
oi = sg._p2dec_gen5
rec("flags", "inner returns its text, outer flags not set", "_p2dec_gen5",
    patched(sg, "_p2dec_gen5", lambda args, flags: oi(args, dict(flags))))
rec("flags", "inner sets four of five flags", "_p2dec_gen5", patched(sg, "_p2dec_gen5", lambda args, flags: (
    lambda t: (flags.update({k: True for k in sg.G5_FLAGS[:4]}), t)[1])(oi(args, dict(flags)))))
pathlib.Path(ARGV[3]).write_text(json.dumps(res) + "\n")
"""


G5FC_KEYS = ("PD", "SM", "VE", "PB", "VB")


def g5_fc_cases(work, new, keys=None):
    res, bad = [], 0
    h = work / "g5fc_harness.py"
    h.write_text(G5FC_HARNESS)
    for key in (keys or G5FC_KEYS):
        c = G5[key]
        cfg, out = work / f"whole-accept-fail-closed-{key}.cfg.json", work / f"whole-accept-fail-closed-{key}.result.json"
        cfg.write_text(json.dumps(dict(argv=["decoder", "--whole-accept", "--S", c["S"], "--ir", IR, "--type", c["type"]] + c["args"],
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
                ok = all(r["rc"] == 2 and r["stdout"] == 0 and r["sm_exit"] == 2 and r["acc"] is False for r in rs)
            res.append(dict(id=f"whole-accept-fail-closed-{key}-{ph}-{kind.replace(' ', '_')}", expect="control: exit 0" if ph == "control"
                            else "exit 2, 0 bytes, summary exit 2, accept_generated false", exit=sorted({str(r["rc"]) for r in rs}),
                            stdout_bytes=sum(r["stdout"] for r in rs), injections=len(rs),
                            bad=[r for r in rs if not ok][:3], ok=bool(ok)))
            bad |= not ok
        fl = {r["phase"] for r in R}
        ok = rc == 0 and {"control", "gen4", "derive", "render", "flags"} <= fl and len(R) > 50
        res.append(dict(id=f"whole-accept-fail-closed-{key}-phases", expect="harness exit 0; injections in gen4, derive, render, flags",
                        exit=rc, stdout_bytes=0, injections=len(R), phases=sorted(fl), stderr=se.strip()[-300:], ok=bool(ok)))
        bad |= not ok
    return res, bad


def main(work, out):
    work.mkdir(parents=True, exist_ok=True)
    res, bad = [], 0
    old = work / "scalgen_old.py"
    old.write_bytes(subprocess.run(["git", "cat-file", "-p", OLD_BLOB], cwd=KR, capture_output=True, check=True).stdout)
    new = KR / "gen" / "scal" / "scalgen.py"

    # old generator, historical record
    rc, so, se = run(["python3", "-I", str(old), "p2dec", "--S", S] + OLD_ARGS, KR)  # the frozen generator: its mode name
    rec = [l for l in (KR / RECORD).read_text().split("\n") if l.startswith("scalgen p2dec:")]  # the record line
    ok = rc == 2 and so == b"" and rec and se.strip() == rec[0]
    res.append(dict(id="old-gen", expect="exit 2, 0 bytes, stderr = record", exit=rc, stdout_bytes=len(so),
                    stderr=se.strip(), ok=bool(ok)))
    bad |= not ok

    # new generator, two runs, committed output
    outs = []
    for _ in range(2):
        rc, so, se = run(["python3", "-I", str(new), "decoder", "--S", S] + ARGS, KR)
        outs.append((rc, so, se))
    com = (KR / COMMITTED).read_bytes() if (KR / COMMITTED).exists() else None
    ok = all(r == 0 for r, _, _ in outs) and outs[0][1] == outs[1][1] and outs[0][1] == com
    t = outs[0][1].decode()
    res.append(dict(id="new-gen", expect="exit 0 twice, identical, = committed GenE1Dec.lean", exit=[r for r, _, _ in outs],
                    stdout_bytes=len(outs[0][1]), deterministic=outs[0][1] == outs[1][1], equals_committed=outs[0][1] == com,
                    theorems=[l.split()[1] for l in t.split("\n") if l.startswith("theorem ")], ok=bool(ok)))
    bad |= not ok

    base = (KR / S).read_text().split("\n")
    for (mid, what, line, o, n, want, match) in MUTANTS:
        if mid == "mutant-both":
            lines = mutate(mutate(base, 31, "  mov $0x20,%ecx", "  mov $0x10,%ecx"), 68, "  add $0x28,%rbx", "  add $0x28,%rsi")
        else:
            lines = mutate(base, line, o, n)
        f = work / f"{mid}.S"
        f.write_text("\n".join(lines))
        rc, so, se = run(["python3", "-I", str(new), "decoder", "--S", str(f)] + ARGS, KR)
        got = sorted(l.split()[3].rstrip(":") for l in se.split("\n") if ": MATCH form" in l)
        ok = rc == want and so == b"" and (want == 2 or got == sorted(match))
        res.append(dict(id=mid, what=what, expect=f"exit {want}, 0 bytes" + (f", MATCH {match}" if want == 3 else ""),
                        exit=rc, stdout_bytes=len(so), matched=got, stderr=se.strip().split("\n"), ok=bool(ok)))
        bad |= not ok

    # partial output on request
    f = work / "mutant-addreg.S"
    po = work / "partial.lean"
    if po.exists():
        po.unlink()
    rc, so, se = run(["python3", "-I", str(new), "decoder", "--S", str(f), "--partial-out", str(po)] + ARGS, KR)
    pt = po.read_text() if po.exists() else ""
    ok = (rc == 3 and so == b"" and pt.startswith("/-! PARTIAL OUTPUT") and "NOT generated: BlockHash" in pt.split("\n")[0]
          and "theorem Decode.generated_root_DepositRoot_seg " in pt and "Decode.generated_root_BlockHash_seg" not in pt)
    res.append(dict(id="partial", expect="exit 3, 0 bytes on stdout, --partial-out file marked PARTIAL, DepositRoot only",
                    exit=rc, stdout_bytes=len(so), partial_first_line=pt.split("\n")[0], ok=bool(ok)))
    bad |= not ok

    r2, b2 = gen2_cases(work, new)
    res += r2
    bad |= b2
    r3, b3 = g3_cases(work, new)
    res += r3
    bad |= b3
    r4, b4 = g4_cases(work, new)
    res += r4
    bad |= b4
    r5, b5 = fc_cases(work, new)
    res += r5
    bad |= b5
    r6, b6 = g5_cases(work, new)
    res += r6
    bad |= b6
    r7, b7 = g5_fc_cases(work, new)
    res += r7
    bad |= b7

    out.write_text(json.dumps(dict(cases=res, passed=sum(r["ok"] for r in res), total=len(res)), indent=1) + "\n")
    print(f"p2dec_test: {sum(r['ok'] for r in res)}/{len(res)} as expected")
    for r in res:
        print(("OK  " if r["ok"] else "BAD ") + r["id"], "exit", r["exit"], "stdout", r["stdout_bytes"])
    return 1 if bad else 0


if __name__ == "__main__":
    if len(sys.argv) != 3:
        print(__doc__)
        sys.exit(2)
    sys.exit(main(pathlib.Path(sys.argv[1]), pathlib.Path(sys.argv[2])))
