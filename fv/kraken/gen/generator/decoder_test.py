#!/usr/bin/env python3
"""Generator tests for `generator.py decoder --whole-accept`. Tests that can fail.

usage: decoder_test.py <work-dir> <result.json>      (run from anywhere; one heavy job at a time; Python 3 stdlib)
exit 0 = every case has its expected exit code and output; 1 = a case differs; 2 = usage

Every case runs `gen/generator/generator.py` of the working tree. Mutants are written to <work-dir>, nothing in the repository.
Cases (ids `whole-accept-*`; mutated `.S` / IR copies in <work-dir> only):
 - whole-accept-new-*: `--whole-accept` on the type of every `decoder --whole-accept` row of `gen/generator/types.tsv`.
   An accept row: exit 0 twice, identical, every whole-accept theorem with its kind line, `kindcheck.py` PASS (rule 12:
   kind parameters recomputed from the IR and the `.S`). A refuse row: exit 2 twice, 0 bytes. Examples of refuse rows:
   AttestationData (nested fields).
 - adversarial inputs, each expected exit 2 with 0 bytes on stdout and `accept_generated: false` in the summary (no
   accept theorem): every class of the step rules (stack-store overlap / misaligned store, head variants, size
   immediate, epilogue jump to a missing label, truncated file, callee of another overlay type) and the whole-accept rules
   (spill to a non-home slot, a register spilled twice, an extra `rcx` spill, `dB != F + 24`, an `xor` epilogue in a
   frame other than 0x20, an epilogue load of a non-zero slot, a `nop` inside the accept epilogue, a malformed
   size-error block, a stack store of an input value, a load from a stack slot outside the layout, interleaved
   fields: the Withdrawal set-up changed, the first field store moved or removed); the 4-byte inline copy (copy removed or 64-bit, source offset, write-barrier branch, length, buffer
   register or slot, pointer store) and the 20-byte memmove size; statement-level IR mutants (a wrong Go offset, a wrong size, the field order swapped, a Go offset that
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
sys.path.insert(0, str(HERE))
import types_table  # noqa: E402


def run(argv, cwd):
    p = subprocess.run(argv, cwd=cwd, capture_output=True)
    return p.returncode, p.stdout, p.stderr.decode("utf-8", "replace")


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


def ir_sizes(sizes):
    """The sizes of several fields changed; the sum (the container's fixed size) stays the same."""
    def fn(t):
        for f in t["ir"]["fields"]:
            if f["key"] in sizes:
                f["v"]["size"] = sizes[f["key"]]
                f["v"]["fixed_size"] = sizes[f["key"]]
    return fn


def ir_swap(a, b):
    def fn(t):
        fs = t["ir"]["fields"]
        i, j = [k for k, f in enumerate(fs) if f["key"] in (a, b)]
        fs[i], fs[j] = fs[j], fs[i]
    return fn


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


# ---------------------------------------------------------------------------------------------- whole-accept

def whole_accept_case(row):
    t = row["type"]
    return dict(S=types_table.assembly(row), type=f"{row['package']}.{t}",
                args=["--const", "unmarshalSSZ", "--prefix", "Decode.generated", "--imports", f"Prysm.{t}.Code", "--open",
                      f"Prysm.{t}.Code"] + row["options"], want=0 if row["expect"] == "accept" else 2)


# the `decoder --whole-accept` rows of gen/generator/types.tsv, in table order
WHOLE_ACCEPT_CASES = {r["type"]: whole_accept_case(r) for r in types_table.rows() if r["mode"] == "decoder --whole-accept"}


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
    ("whole-accept-nested", "real AttestationData: Source / Target are nested containers (step exit 3)", "AttestationData", None, None, 2),
    # statement-level IR mutants
    ("whole-accept-ir-goff", "IR: PowBlock ParentHash Go offset 32 (code 24)", "PowBlock", None, ir_goff("ParentHash", 32), 2),
    ("whole-accept-ir-size", "IR: PowBlock TotalDifficulty of 48 bytes (code 32)", "PowBlock", None, ir_size("TotalDifficulty", 48), 2),
    ("whole-accept-ir-order", "IR: VoluntaryExit Epoch / ValidatorIndex order swapped", "VoluntaryExit", None, ir_swap("Epoch", "ValidatorIndex"), 2),
    ("whole-accept-ir-goff-code", "IR and code: ValidatorBalance Balance at Go offset 24 (code store 0x18; not the running sum 16)", "ValidatorBalance",
     rv([(52, "mov %rcx,0x10(%rdx)", "mov %rcx,0x18(%rdx)")]), ir_goff("Balance", 24), 2),
    ("whole-accept-ir-goff-first", "IR: VoluntaryExit Epoch Go offset 0 (code 8, state word)", "VoluntaryExit", None, ir_goff("Epoch", 0), 2),
    # 4-byte fields (inline-copy segment, Fork) and 20-byte fields (WithdrawalRequest)
    ("whole-accept-inline-copy-missing", "Fork PreviousVersion: the 32-bit store `mov %edi,(%rax)` removed", "Fork",
     rv([(32, "mov %edi,(%rax)", None)]), None, 2),
    ("whole-accept-inline-copy-64", "Fork PreviousVersion: a 64-bit copy `mov (%rsi),%rdi; mov %rdi,(%rax)`", "Fork",
     rv([(31, "mov (%rsi),%edi", "mov (%rsi),%rdi"), (32, "mov %edi,(%rax)", "mov %rdi,(%rax)")]), None, 2),
    ("whole-accept-inline-source-offset", "Fork CurrentVersion: `mov 0x8(%rbx),%esi` (IR SSZ offset 4)", "Fork",
     rv([(60, "mov 0x4(%rbx),%esi", "mov 0x8(%rbx),%esi")]), None, 2),
    ("whole-accept-inline-je-to-jne", "Fork PreviousVersion: the write-barrier test `jne` (the copy tail runs on the barrier path)", "Fork",
     rv([(37, "UnmarshalSSZ_b2", "jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Fork.UnmarshalSSZ_b2")]), None, 2),
    ("whole-accept-inline-len-imm", "Fork PreviousVersion: `movq $0x5,0x10(%rdx)` after the copy (size 4)", "Fork",
     rv([(33, "movq $0x4,0x10(%rdx)", "movq $0x5,0x10(%rdx)")]), None, 2),
    ("whole-accept-inline-buffer-register", "Fork PreviousVersion: buffer in rcx (`mov 0x50(%rsp),%rcx; mov (%rcx),%edi`, no lemma case)", "Fork",
     rv([(30, "mov 0x50(%rsp),%rsi", "mov 0x50(%rsp),%rcx"), (31, "mov (%rsi),%edi", "mov (%rcx),%edi")]), None, 2),
    ("whole-accept-inline-pointer-store", "Fork PreviousVersion: pointer store after the barrier at Go offset 16 (IR 8)", "Fork",
     rv([(43, "mov %rax,0x8(%rdx)", "mov %rax,0x10(%rdx)")]), None, 2),
    ("whole-accept-inline-buffer-not-home", "Fork PreviousVersion: buffer reload from 0x48(%rsp) (the receiver slot)", "Fork",
     rv([(30, "mov 0x50(%rsp),%rsi", "mov 0x48(%rsp),%rsi")]), None, 2),
    ("whole-accept-epilogue-four-nops", "Fork: four `nop`s between `pop %rbp` and `retq` of the accept epilogue (at most three)", "Fork",
     rv([(109, "nop", ["nop", "nop", "nop", "nop"])]), None, 2),
    ("whole-accept-ir-size-4", "IR: ForkData CurrentVersion of 32 bytes and GenesisValidatorsRoot of 4 bytes (code 4 and 32)", "ForkData",
     None, ir_sizes({"CurrentVersion": 32, "GenesisValidatorsRoot": 4}), 2),
    ("whole-accept-memmove-size-20", "WithdrawalRequest SourceAddress: `mov $0x13,%ecx` before memmove (size 20)", "WithdrawalRequest",
     rv([(31, "mov $0x14,%ecx", "mov $0x13,%ecx")]), None, 2),
    ("whole-accept-ir-size-20", "IR: WithdrawalRequest SourceAddress of 48 bytes and ValidatorPubkey of 20 bytes (code 20 and 48)",
     "WithdrawalRequest", None, ir_sizes({"SourceAddress": 48, "ValidatorPubkey": 20}), 2),
    # interleaved fields (Withdrawal: the ValidatorIndex set-up `lea 0x8(%rbx),%rdx; add $-0x8,%rdi; lea 0x10(%rax),%rsi` runs
    # before the Index load and store, lines 14-18; one field block for Index and ValidatorIndex)
    ("whole-accept-interleaved-store-removed", "Withdrawal: the Index receiver store `mov %r8,0x8(%rax)` removed", "Withdrawal",
     rv([(18, "mov %r8,0x8(%rax)", None)]), None, 2),
    ("whole-accept-interleaved-store-after-call", "Withdrawal: the Index load and store moved to the continuation of the ValidatorIndex call",
     "Withdrawal", rv([(17, "mov (%rbx),%r8", None), (18, "mov %r8,0x8(%rax)", None),
                       (53, "mov %rbx,0x30(%rsp)", ("before", ["mov (%rbx),%r8", "mov %r8,0x8(%rax)"]))]), None, 2),
    ("whole-accept-interleaved-store-offset", "Withdrawal: the Index store at receiver offset 0x10 (the ValidatorIndex word)", "Withdrawal",
     rv([(18, "mov %r8,0x8(%rax)", "mov %r8,0x10(%rax)")]), None, 2),
    ("whole-accept-interleaved-setup-offset", "Withdrawal: `lea 0x10(%rbx),%rdx` (the ValidatorIndex source at SSZ offset 16, IR 8)", "Withdrawal",
     rv([(14, "lea 0x8(%rbx),%rdx", "lea 0x10(%rbx),%rdx")]), None, 2),
    ("whole-accept-interleaved-setup-receiver", "Withdrawal: `lea 0x18(%rax),%rsi` (the ValidatorIndex target at Go offset 24, IR 16)", "Withdrawal",
     rv([(16, "lea 0x10(%rax),%rsi", "lea 0x18(%rax),%rsi")]), None, 2),
    ("whole-accept-interleaved-setup-clobbered", "Withdrawal: `mov %rdi,%rsi` after the Index store (the receiver address clobbered)", "Withdrawal",
     rv([(19, "mov %rsi,%rax", ("before", ["mov %rdi,%rsi"]))]), None, 2),
    ("whole-accept-interleaved-load-offset", "Withdrawal: the Index load `mov 0x8(%rbx),%r8` (SSZ offset 8, IR 0)", "Withdrawal",
     rv([(17, "mov (%rbx),%r8", "mov 0x8(%rbx),%r8")]), None, 2),
    # valid variants: generated, kindcheck PASS
    ("whole-accept-interleaved-valid-setup-after-store", "Withdrawal: the ValidatorIndex set-up after the Index store (no interleaving)",
     "Withdrawal", rv([(14, "lea 0x8(%rbx),%rdx", None), (15, "add $-0x8,%rdi", None), (16, "lea 0x10(%rax),%rsi", None),
                       (19, "mov %rsi,%rax", ("before", ["lea 0x8(%rbx),%rdx", "add $-0x8,%rdi", "lea 0x10(%rax),%rsi"]))]), None, 0),
    ("whole-accept-interleaved-valid-nop", "Withdrawal: a `nop` between the Index store and the ValidatorIndex set-up moves", "Withdrawal",
     rv([(19, "mov %rsi,%rax", ("before", ["nop"]))]), None, 0),
    ("whole-accept-inline-valid-nop", "Fork PreviousVersion: a `nop` between the 32-bit load and the 32-bit store", "Fork",
     rv([(32, "mov %edi,(%rax)", ("before", ["nop"]))]), None, 0),
    ("whole-accept-epilogue-valid-no-nop", "Fork: the `nop` between `pop %rbp` and `retq` removed", "Fork",
     rv([(109, "nop", None)]), None, 0),
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
    for key, c in WHOLE_ACCEPT_CASES.items():
        r1, r2 = whole_accept_run(work, new, f"whole-accept-new-{key}-1", c), whole_accept_run(work, new, f"whole-accept-new-{key}-2", c)
        want = c["want"]
        kc = None
        if r1[0] == 0:
            f = work / f"whole-accept-new-{key}.lean"
            f.write_bytes(r1[1])
            kc = subprocess.run(KC + [str(f)], capture_output=True, text=True).returncode
        t = r1[1].decode()
        pre = c["args"][3]
        thm = (all(f"\ntheorem {pre}_{x} : " in t and f"\ntheorem {pre}_{x}_kind : " in t
                   for x in ("head", "epilogue", "accept", "reject"))
               and (f"\ntheorem {pre}_field_1 : " in t or f"\ntheorem {pre}_fields_1_" in t)) if want == 0 else True
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
for meth in ("head", "field", "f_u64", "f_bytes", "f_inline", "f_call", "epilogue", "accept", "reject", "layout", "binders", "mem"):
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
    ok_(self, name, kind, extra), self.kinds_emitted.pop() if name.endswith("_field_1") or "_fields_1_" in name else None)[0]))
rec("flags", "a kind line dropped from the text", "T.body", patched(whole_accept_gen.T, "body", (lambda ob: lambda self: ob(self).replace(
    "_epilogue_kind :", "_epilogue_kinx :", 1))(whole_accept_gen.T.body)))
oi = sg._decoder_whole_accept
rec("flags", "inner returns its text, outer flags not set", "_decoder_whole_accept",
    patched(sg, "_decoder_whole_accept", lambda args, flags: oi(args, dict(flags))))
rec("flags", "inner sets four of five flags", "_decoder_whole_accept", patched(sg, "_decoder_whole_accept", lambda args, flags: (
    lambda t: (flags.update({k: True for k in sg.WHOLE_ACCEPT_FLAGS[:4]}), t)[1])(oi(args, dict(flags)))))
pathlib.Path(ARGV[3]).write_text(json.dumps(res) + "\n")
"""


WHOLE_ACCEPT_FAIL_CLOSED_KEYS = ("PendingDeposit", "SyncCommitteeMessage", "VoluntaryExit", "PowBlock", "ValidatorBalance", "Fork", "Withdrawal")


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
