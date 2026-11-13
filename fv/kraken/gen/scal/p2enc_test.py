#!/usr/bin/env python3
"""Generator tests for `scalgen.py encoder --fast-path`. Tests that can fail.

usage: p2enc_test.py <work-dir> <result.json>     (cwd = fv/kraken; one gated job; Python 3 stdlib only)
exit 0 = every case has its expected outcome; 1 = a case differs; 2 = usage

Cases (mutated `.S` / IR copies are written to <work-dir>, nothing in the repository changes):
 - fast-path-real-*: the 16 flat development types as committed in `gen/gen.sh` (fast-path rows): exit 0, two runs
   byte-identical, every theorem with its kind line; equal to the committed `lean/Prysm/<T>/GeneratedEncodeFastPath.lean` when it
   exists.
 - fast-path-adv-*: adversarial `.S` / IR mutants (capacity test altered so that the growslice site is on the walked path,
   length test with a wrong immediate / wrong word, a store to the wrong offset vs the IR, fields out of order, a
   clobbered dst / len register, memmove with swapped source / destination, epilogue frame-test variants, a
   truncated file, an extra store beyond len + size, unknown directives and callees, stack stores outside the frame,
   head variants, IR mutants, ...). Expected: exit 2, 0 bytes on stdout, the `--summary` says generated = false.
 - fast-path-ok-*: valid variants that must stay COVERED (exit 0, every kind line): nops at many places, an extra harmless
   move, a consistent register rename.
 - e6fc-*: fail-closed fault injection. A harness imports the working-tree `scalgen.py`, takes its `gen6enc` module
   (`g6_module()`), monkeypatches one phase and calls `main()`: an unexpected exception, SystemExit(0) and a G6Refuse
   at every phase (IR read, `.S` read, hand layout parse, walk pass 1 / pass 2, every field's first step, boundary,
   liveness, frame test, epilogue, text, meta), plus corrupted results (a kind line dropped, a forbidden token, a
   missing flag). Expected for every injection: exit 2, 0 bytes on stdout. Control: no injection, exit 0.
"""
import json, os, pathlib, re, subprocess, sys

P = "github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1"
E = "prysm/go1.26.10"
IR = "prysm/ir/ir-mainnet.json"
ROWS = [  # type, link dir, const, code module, prefix, extra args, output file
    ("Checkpoint", "link-set", "marshalSSZTo", "Prysm.Checkpoint.Code", "cp", ["--hand-layout=Prysm.Checkpoint.encodeLayout",
     "--hand-layout-src=lean/Prysm/Checkpoint/EncodeFastPathKindInstances.lean", "--same-as=Prysm.Checkpoint.Encode.fast_path",
     "--same-as-via=Prysm.Checkpoint.Encode.fast_path_of_kind"], "Gen6CpEnc"),
    ("BeaconBlockHeader", "link-set", "marshalSSZTo", "Prysm.BeaconBlockHeader.Code", "bh", ["--hand-layout=Prysm.BeaconBlockHeader.encodeLayout",
     "--hand-layout-src=lean/Prysm/BeaconBlockHeader/EncodeFastPathKindInstances.lean", "--same-as=Prysm.BeaconBlockHeader.Encode.fast_path"], "Gen6BhEnc"),
    ("Eth1Data", "link-set", "marshalSSZTo", "Prysm.Eth1Data.Code", "e1", ["--hand-layout=Prysm.Eth1Data.encodeLayout",
     "--hand-layout-src=lean/Prysm/Eth1Data/EncodeFastPathKindInstances.lean", "--same-as=Prysm.Eth1Data.Encode.fast_path"], "Gen6E1Enc"),
] + [(t, "link-set", c, f"Prysm.{t}.EncoderCode", p, [], f"Gen6{p.capitalize()}Enc") for t, c, p in [
    ("BlobIdentifier", "marshalSSZTo", "bi"), ("DepositMessage", "marshalSSZTo", "dm"), ("Deposit_Data", "marshalSSZTo", "dd"),
    ("PendingPartialWithdrawal", "marshalSSZTo", "pw"), ("SyncCommitteeMessage", "marshalSSZTo", "sc"),
    ("PendingConsolidation", "marshalSSZTo", "pc"), ("PendingDeposit", "marshalSSZTo", "pd"), ("PowBlock", "marshalSSZTo", "pb"),
    ("HistoricalSummary", "marshalSSZTo", "hs"), ("SigningData", "marshalSSZTo", "sd"),
    ("SyncAggregatorSelectionData", "marshalSSZTo", "sa"), ("ValidatorBalance", "marshalSSZTo", "vb"),
    ("VoluntaryExit", "marshalSSZTo", "ve")]]
ROW = {r[0]: r for r in ROWS}


def spath(t):
    return f"{E}/{ROW[t][1]}/norm/{P}.{t}.MarshalSSZTo.S"


def argv(t, S=None, ir=IR, extra=None, summary=None):
    _, d, c, mod, p, x, _ = ROW[t]
    a = ["python3", "-I", "-B", "gen/scal/scalgen.py", "encoder", "--fast-path", "--S", S or spath(t), "--const", c,
         "--ir", ir, "--type", f"v1alpha1.{t}", "--prefix", "Encode.generated", "--imports", mod, "--open", f"Prysm.{t}.Code"]
    a += x if extra is None else extra
    if summary:
        a += ["--summary", summary]
    return a


def run(a):
    r = subprocess.run(a, capture_output=True)
    return r.returncode, r.stdout, r.stderr.decode(errors="replace")


def lines_of(t):
    return pathlib.Path(spath(t)).read_text().split("\n")


def mut(t, edits, work, name):
    """edits: list of (old stripped text, [new lines] or None (delete), nth occurrence). Every edit must apply."""
    L = lines_of(t)
    for old, new, nth in edits:
        hits = [i for i, l in enumerate(L) if l.strip() == old]
        if len(hits) <= nth:
            raise SystemExit(f"test setup: `{old}` occurrence {nth} not in {t}")
        i = hits[nth]
        L[i:i + 1] = [] if new is None else ["  " + x if not x.endswith(":") else x for x in new]
    p = work / f"{name}.S"
    if L == lines_of(t):
        raise SystemExit(f"test setup: .S mutant {name} changes nothing")
    p.write_text("\n".join(L))
    return str(p)


def ir_mut(t, fn, work, name):
    d = json.loads(pathlib.Path(IR).read_text())
    hit = 0
    for c in d["configs"]:
        for ty in c.get("types", []):
            if ty.get("name") == t and c["package"].endswith("/v1alpha1"):
                fn(ty)
                hit += 1
    if hit != 1:
        raise SystemExit("test setup: IR type")
    p = work / f"{name}.json"
    if json.dumps(d) == json.dumps(json.loads(pathlib.Path(IR).read_text())):
        raise SystemExit(f"test setup: IR mutant {name} changes nothing")
    p.write_text(json.dumps(d))
    return str(p)


def lbl(t, suffix):
    return f"L_{P}.{t}.MarshalSSZTo_{suffix}"


def adversarial(work):
    """(id, argv, expect 'refuse' | 'covered', what)"""
    C = []
    vb, dm, hs, bh, e1, bi = "ValidatorBalance", "DepositMessage", "HistoricalSummary", "BeaconBlockHeader", "Eth1Data", \
        "BlobIdentifier"

    def adv(i, t, edits, what, expect="refuse", extra=None):
        C.append((f"fast-path-adv-{i}" if expect == "refuse" else f"fast-path-ok-{i}", argv(t, S=mut(t, edits, work, i), extra=extra),
                  expect, what))
    # capacity test altered: the growslice site is on the walked path / the test is not provably passed
    adv("cap-jae-deleted", vb, [(f"jae {lbl(vb, '7b')}", None, 0)], "capacity test branch removed: growslice on the path")
    adv("cap-jae-to-jb", vb, [(f"jae {lbl(vb, '7b')}", [f"jb {lbl(vb, '7b')}"], 0)],
        "capacity test jae -> jb to the merge label: growslice on the fall-through")
    adv("cap-operands-swapped", vb, [("cmp %rdx,%rdi", ["cmp %rdi,%rdx"], 0)], "cmp of capacity and length swapped")
    adv("cap-short", vb, [("lea 0x8(%rcx),%rdx", ["lea 0x7(%rcx),%rdx"], 0)], "capacity test for len + 7 (field needs 8)")
    adv("cap-jae-to-growslice", vb, [(f"jae {lbl(vb, '7b')}", [f"jae {lbl(vb, 'gs')}"], 0),
                                     ("callq runtime.growslice", [f"{lbl(vb, 'gs')}:", "callq runtime.growslice"], 0)],
        "capacity test jumps INTO the growslice site")
    adv("cap-missing-dm", dm, [("cmp %r8,%rdi", None, 0), (f"jae {lbl(dm, '7b')}", None, 0)],
        "byte field without capacity test")
    # length test
    adv("len-imm", dm, [("cmpq $0x30,0x8(%rax)", ["cmpq $0x20,0x8(%rax)"], 0)], "length test with a wrong immediate")
    adv("len-word", dm, [("cmpq $0x30,0x8(%rax)", ["cmpq $0x30,0x10(%rax)"], 0)], "length test on the capacity word")
    adv("len-missing", dm, [("cmpq $0x30,0x8(%rax)", None, 0), (f"jne {lbl(dm, '183')}", None, 0)],
        "byte field without its length test")
    adv("len-je", dm, [(f"jne {lbl(dm, '183')}", [f"je {lbl(dm, '183')}"], 0)], "length test with je")
    # stores against the IR
    adv("store-offset", vb, [("mov %r8,-0x8(%rdx,%rbx,1)", ["mov %r8,-0x10(%rdx,%rbx,1)"], 0)],
        "second uint64 stored at SSZ offset 0 (IR: 8)")
    adv("store-offset-first", vb, [("mov %r8,(%rbx,%rcx,1)", ["mov %r8,0x8(%rbx,%rcx,1)"], 0)],
        "first uint64 stored at SSZ offset 8 (IR: 0)")
    adv("extra-store", vb, [("mov %r8,-0x8(%rdx,%rbx,1)", ["mov %r8,-0x8(%rdx,%rbx,1)", "mov %r8,(%rdx,%rbx,1)"], 0)],
        "an extra store at len + size after the last field")
    adv("store-wrong-value", vb, [("mov 0x10(%rax),%r8", ["mov 0x8(%rax),%r8"], 0)],
        "field 1 slot gets field 0's value")
    def swap(ty):
        g = ty["go_fields"]
        g[1], g[2] = g[2], g[1]
        ty["ir"]["fields"].reverse()
    C.append(("fast-path-adv-fields-out-of-order", argv(vb, ir=ir_mut(vb, swap, work, "vb-swap")), "refuse",
              "IR field order swapped, Go offsets as in the code"))
    adv("code-fields-swapped", vb, [("mov 0x10(%rax),%r8", ["mov 0x8(%rax),%r8"], 0),
                                    ("mov 0x8(%rax),%r8", ["mov 0x10(%rax),%r8"], 0)],
        "code writes Balance first and Index second")
    C.append(("fast-path-adv-ir-goff", argv(vb, ir=ir_mut(vb, lambda ty: ty["go_fields"][2].__setitem__("offset_gc_amd64", 24),
                                                   work, "vb-goff")), "refuse", "IR Go offset off by 8"))
    C.append(("fast-path-adv-ir-size", argv(dm, ir=ir_mut(dm, lambda ty: (
        ty["go_fields"][0].__setitem__("tag", ty["go_fields"][0]["tag"].replace('ssz-size:"48"', 'ssz-size:"32"')),
        ty["ir"]["fields"][0]["v"].update(size=32, fixed_size=32), ty["ir"].update(fixed_size=ty["ir"]["fixed_size"] - 16)),
        work, "dm-size")), "refuse", "IR size 48 -> 32 (code tests 48)"))
    C.append(("fast-path-adv-ir-size-only-tag", argv(dm, ir=ir_mut(dm, lambda ty: ty["go_fields"][0].__setitem__(
        "tag", ty["go_fields"][0]["tag"].replace('ssz-size:"48"', 'ssz-size:"32"')), work, "dm-tag")), "refuse",
        "IR views disagree (tag 32, SSZ IR 48)"))
    C.append(("fast-path-adv-ir-missing-type", argv(vb) [:0] + [x.replace("v1alpha1.ValidatorBalance", "v1alpha1.NoSuchType")
                                                         for x in argv(vb)], "refuse", "type not in the IR"))
    # clobbered registers
    adv("clobber-len", vb, [("mov %r8,(%rbx,%rcx,1)", ["mov $0x0,%ecx", "mov %r8,(%rbx,%rcx,1)"], 0)],
        "len register clobbered before the store")
    adv("clobber-dst", vb, [("mov %r8,(%rbx,%rcx,1)", ["xor %ebx,%ebx", "mov %r8,(%rbx,%rcx,1)"], 0)],
        "dst register clobbered before the store")
    adv("clobber-rcv", dm, [("mov 0x18(%rdx),%rbx", ["mov 0x18(%rcx),%rbx"], 0)], "receiver load through a clobbered register")
    # memmove
    adv("memmove-swapped", dm, [("lea (%rcx,%rbx,1),%rax", ["mov %rdx,%rax"], 0), ("mov %rdx,%rbx", ["lea (%rcx,%rbx,1),%rbx"], 0)],
        "memmove with swapped source / destination")
    adv("memmove-size", dm, [("mov $0x30,%ecx", ["mov $0x20,%ecx"], 0)], "memmove of 32 bytes for a 48-byte field")
    adv("memmove-other-callee", dm, [("callq runtime.memmove", ["callq runtime.memclrNoHeapPointers"], 0)],
        "unknown callee on the path")
    # epilogue / frame test
    adv("ft-jae", hs, [(f"jb {lbl(hs, '12e')}", [f"jae {lbl(hs, '12e')}"], 0)], "frame test with jae")
    adv("ft-imm", hs, [("lea 0x60(%rsp),%rsi", ["lea 0x58(%rsp),%rsi"], 0)], "frame test against F + 8")
    adv("ft-target", hs, [(f"jb {lbl(hs, '12e')}", [f"jb {lbl(hs, '13d')}"], 0)], "frame test branch to the return block")
    adv("ft-sub", hs, [("sub %rsp,%rdx", ["sub %rsi,%rdx"], 0)], "frame test on a value other than ptr - rsp")
    adv("epi-no-xor", vb, [("xor %esi,%esi", None, 0)], "rsi not zeroed at the return")
    adv("epi-rbx", vb, [("mov %rdx,%rbx", ["mov %rcx,%rbx"], 2)], "result length register wrong")
    adv("epi-no-ret", vb, [("retq", ["nop"], 0)], "no retq after pop")
    adv("epi-frame", vb, [("add $0x68,%rsp", ["add $0x60,%rsp"], 0)], "frame release of the wrong size")
    # truncated / malformed files
    tr = lines_of(vb)[:40]
    p = work / "truncated.S"
    p.write_text("\n".join(tr))
    C.append(("fast-path-adv-truncated", argv(vb, S=str(p)), "refuse", "file cut after 40 lines"))
    adv("blank-line", vb, [("mov %rbx,0x80(%rsp)", ["mov %rbx,0x80(%rsp)", ""], 0)], "blank line inside")
    adv("dup-label", vb, [("mov %r8,-0x8(%rdx,%rbx,1)", [f"{lbl(vb, '7b')}:", "mov %r8,-0x8(%rdx,%rbx,1)"], 0)],
        "label defined twice")
    adv("unknown-directive", vb, [("mov %r8,0x48(%rsp)", ["movq %r8,0x48(%rsp)"], 0)], "directive form without a step lemma")
    adv("unknown-label", vb, [(f"jae {lbl(vb, '7b')}", [f"jae {lbl(vb, 'zz')}"], 0)], "jump to a label not in the file")
    adv("backward-jmp", hs, [(f"jmp {lbl(hs, '13d')}", [f"jmp {lbl(hs, '0')}"], 0)], "backward jump on the path")
    # stack stores outside the frame
    adv("store-saved-rbp", vb, [("mov %rbx,0x80(%rsp)", ["mov %rbx,0x68(%rsp)"], 0)], "spill over the saved rbp")
    adv("store-ret-addr", vb, [("mov %rbx,0x80(%rsp)", ["mov %rbx,0x70(%rsp)"], 0)], "spill over the return address")
    adv("store-below-frame", vb, [("mov %r8,0x48(%rsp)", ["mov %r8,-0x8(%rsp)"], 0)], "store below the frame")
    adv("movups-dst", vb, [("movups %xmm15,(%r9)", ["movups %xmm15,(%rbx)"], 0)], "zeroing store through the dst pointer")
    adv("overlap", vb, [("mov %r8,0x48(%rsp)", ["mov %r8,0x4c(%rsp)"], 0)], "8-byte store across two stack regions")
    # head variants
    adv("head-no-push", vb, [("push %rbp", ["nop"], 0)], "prologue without push")
    adv("head-guard", vb, [("cmp 0x10(%r14),%rsp", ["cmp 0x18(%r14),%rsp"], 0)], "stack guard on another word")
    adv("head-frame", vb, [("sub $0x68,%rsp", ["sub %rax,%rsp"], 0)], "frame allocation form")
    # hand layout of another type
    C.append(("fast-path-adv-hand-layout-other", argv(bh, extra=["--hand-layout=Prysm.Eth1Data.encodeLayout",
                                                           "--hand-layout-src=lean/Prysm/Eth1Data/EncodeFastPathKindInstances.lean"]),
              "refuse", "hand layout of Eth1Data for BeaconBlockHeader"))
    C.append(("fast-path-adv-hand-layout-missing", argv(bh, extra=["--hand-layout=Prysm.BeaconBlockHeader.encodeLayoutMissing",
                                                             "--hand-layout-src=lean/Prysm/BeaconBlockHeader/EncodeFastPathKindInstances.lean"]),
              "refuse", "hand layout not in the file"))
    # valid variants: must stay covered
    adv("nops", vb, [("lea 0x8(%rcx),%rdx", ["nop", "lea 0x8(%rcx),%rdx", "nop"], 0), ("cmp %rdx,%rdi", ["cmp %rdx,%rdi", "nop"], 0),
                     ("mov 0x48(%rsp),%r8", ["nop", "nop", "mov 0x48(%rsp),%r8"], 0), ("pop %rbp", ["nop", "pop %rbp"], 0)],
        "nops at start, middle (inside a cmp / jae window), doubled, before pop", "covered")
    adv("nops-call", dm, [("callq runtime.memmove", ["nop", "nop", "callq runtime.memmove"], 0)],
        "two nops before a memmove", "covered")
    adv("extra-move", vb, [("mov 0x10(%rax),%r8", ["mov %rax,%r10", "mov 0x10(%rax),%r8"], 0)], "an extra harmless move",
        "covered")
    adv("rename", vb, [("mov 0x10(%rax),%r8", ["mov 0x10(%rax),%r9"], 0), ("mov %r8,-0x8(%rdx,%rbx,1)",
                                                                           ["mov %r9,-0x8(%rdx,%rbx,1)"], 0)],
        "field 1 value through r9 instead of r8", "covered")
    return C


KINDS = ("encHeadKindAnyFrame", "encFieldKindAnyFrame", "encEpilogueKindAnyFrame", "encFastPathKindAnyFrame")


def kinds_ok(out, p, nf):
    t = out.decode()
    want = ["Encode.generated_head"] + [f"Encode.generated_f{i}" for i in range(nf)] + ["Encode.generated_epi", "Encode.generated_fast"]
    return all(t.count(f"\ntheorem {w}_kind : ∀ (h : Host), type_of% (@{w} h)\n") == 1 for w in want)


def nfields(t):
    d = json.loads(pathlib.Path(IR).read_text())
    for c in d["configs"]:
        for ty in c.get("types", []):
            if ty.get("name") == t and c["package"].endswith("/v1alpha1"):
                return sum(f["exported"] for f in ty["go_fields"])


FC_HARNESS = r'''
import importlib.util, io, json, sys, contextlib
spec = importlib.util.spec_from_file_location("scalgen_g6fc", sys.argv[1])
sg = importlib.util.module_from_spec(spec)
spec.loader.exec_module(sg)
cfg = json.loads(open(sys.argv[2]).read())
OUT = sys.argv[3]
G6 = sg.g6_module()
R = []

class Boom(Exception):
    pass

def raiser(kind, where):
    if kind == "exception":
        raise Boom("injected at " + where)
    if kind == "systemexit0":
        raise SystemExit(0)
    raise G6.G6Refuse("injected at " + where)

def main_once():
    out = io.StringIO()
    code = 0
    with contextlib.redirect_stdout(out):
        try:
            sys.argv = ["scalgen.py"] + cfg["argv"]
            sg.main()
        except SystemExit as e:
            code = e.code if isinstance(e.code, int) else (0 if e.code is None else 1)
        except BaseException as e:
            code = 99
    return code, len(out.getvalue())

PH_FUNCS = [("read_ir", G6, "read_ir"), ("read_S", G6, "read_S"), ("parse_layout", G6, "parse_layout"),
            ("walk", G6.Gen6, "walk"), ("run", G6.Gen6, "run"), ("touch", G6.Gen6, "touch"),
            ("boundary", G6.Gen6, "boundary"), ("live_after", G6.Gen6, "live_after"), ("frametest", G6.Gen6, "frametest"),
            ("epi", G6.Gen6, "epi"), ("text", G6.Gen6, "text"), ("meta", G6.Gen6, "meta"), ("ins", G6.Gen6, "ins"),
            ("layout_fields", G6.Gen6, "layout_fields")]
code, n = main_once()
R.append(dict(phase="control", kind="none", exit=code, stdout=n, ok=(code == 0 and n > 0)))
for ph, obj, name in PH_FUNCS:
    orig = getattr(obj, name)
    for kind in ("exception", "systemexit0", "refuse"):
        called = []
        def patched(*a, _k=kind, _ph=ph, **kw):
            called.append(1)
            raiser(_k, _ph)
        setattr(obj, name, patched)
        try:
            code, n = main_once()
        finally:
            setattr(obj, name, orig)
        # a phase this type does not reach (no hand layout / no frame test) must leave the run unchanged (exit 0)
        R.append(dict(phase=ph, kind=kind, exit=code, stdout=n, reached=bool(called),
                      ok=(code == 2 and n == 0) if called else (code == 0 and n > 0)))
# every field: the first step after boundary j (pass 2), for every j
orig_step = G6.Gen6.step
for j in range(cfg["nfields"] + 1):
    for kind in ("exception", "systemexit0", "refuse"):
        def pstep(self, i, _j=j, _k=kind):
            if self.emit and self.done == _j:
                raiser(_k, f"step of field {_j}")
            return orig_step(self, i)
        G6.Gen6.step = pstep
        try:
            code, n = main_once()
        finally:
            G6.Gen6.step = orig_step
        R.append(dict(phase=f"field{j}", kind=kind, exit=code, stdout=n, ok=(code == 2 and n == 0)))
# corrupted results (no exception): a kind line dropped, a forbidden token, a flag not set
orig_text = G6.Gen6.text
def drop_kind(self):
    b, k = orig_text(self)
    return b, k[:-1]
def sorry_text(self):
    b, k = orig_text(self)
    return b.replace("  intro h; rfl", "  sorry", 1), k
def kind_text_missing(self):
    b, k = orig_text(self)
    return b.replace("_epi_kind :", "_epi_kinx :", 1), k
for nm, fn in (("drop_kind_list", drop_kind), ("sorry_token", sorry_text), ("kind_line_renamed", kind_text_missing)):
    G6.Gen6.text = fn
    try:
        code, n = main_once()
    finally:
        G6.Gen6.text = orig_text
    R.append(dict(phase="text-result", kind=nm, exit=code, stdout=n, ok=(code == 2 and n == 0)))
orig_inner = sg._p2enc_gen6
for flag in sg.G6_FLAGS:
    def inner(args, flags, _f=flag):
        t = orig_inner(args, flags)
        flags[_f] = False
        return t
    sg._p2enc_gen6 = inner
    try:
        code, n = main_once()
    finally:
        sg._p2enc_gen6 = orig_inner
    R.append(dict(phase="flags", kind=f"unset {flag}", exit=code, stdout=n, ok=(code == 2 and n == 0)))
def inner_none(args, flags):
    orig_inner(args, flags)
    return None
sg._p2enc_gen6 = inner_none
try:
    code, n = main_once()
finally:
    sg._p2enc_gen6 = orig_inner
R.append(dict(phase="flags", kind="text None", exit=code, stdout=n, ok=(code == 2 and n == 0)))
open(OUT, "w").write(json.dumps(R))
'''


def main():
    if len(sys.argv) != 3:
        print(__doc__)
        return 2
    work, out = pathlib.Path(sys.argv[1]), pathlib.Path(sys.argv[2])
    work.mkdir(parents=True, exist_ok=True)
    res = []
    # real types
    for t, d, c, mod, p, x, f in ROWS:
        r1, r2 = run(argv(t)), run(argv(t))
        nf = nfields(t)
        com = pathlib.Path(f"lean/Prysm/{t}/GeneratedEncodeFastPath.lean")
        same = (r1[1] == com.read_bytes()) if com.exists() else None
        ok = r1[0] == 0 and r1[1] == r2[1] and kinds_ok(r1[1], p, nf) and same is not False
        res.append(dict(id=f"fast-path-real-{p}", expect="exit 0, deterministic, all kinds" + (", = committed" if same else ""),
                        exit=r1[0], stdout=len(r1[1]), committed_equal=same, ok=ok, stderr=r1[2][-200:]))
    # adversarial + valid variants
    for cid, a, exp, what in adversarial(work):
        sm = work / f"{cid}.summary.json"
        code, so, se = run(a + ["--summary", str(sm)])
        try:
            S = json.loads(sm.read_text())
        except Exception:
            S = {}
        if exp == "refuse":
            ok = code == 2 and len(so) == 0 and S.get("generated") is False and S.get("exit") == 2
        else:
            t = [r for r in ROWS if f"--const" in a and r[2] == a[a.index("--const") + 1]][0]
            ok = code == 0 and kinds_ok(so, t[4], nfields(t[0])) and S.get("generated") is True
        res.append(dict(id=cid, expect=exp, what=what, exit=code, stdout=len(so), ok=ok,
                        reason=S.get("reason", "")[:240] or se.strip()[-240:]))
    # fault injection
    h = work / "g6fc_harness.py"
    h.write_text(FC_HARNESS)
    reached = set()
    for t in ("ValidatorBalance", "DepositMessage", "HistoricalSummary", "Checkpoint"):
        cfg = work / f"g6fc-{t}.cfg.json"
        ro = work / f"g6fc-{t}.result.json"
        cfg.write_text(json.dumps(dict(argv=argv(t)[4:], nfields=nfields(t))))
        r = subprocess.run(["python3", "-I", "-B", str(h), "gen/scal/scalgen.py", str(cfg), str(ro)], capture_output=True)
        try:
            R = json.loads(ro.read_text())
        except Exception:
            R = []
        for x in R:
            res.append(dict(id=f"e6fc-{ROW[t][4]}-{x['phase']}-{x['kind']}", expect="control: exit 0" if x["phase"] == "control"
                            else "exit 2, 0 bytes", exit=x["exit"], stdout=x["stdout"], ok=x["ok"]))
        reached.update(x["phase"] for x in R if x.get("reached", True))
        res.append(dict(id=f"e6fc-{ROW[t][4]}-harness", expect="harness exit 0 and >= 55 injections",
                        exit=r.returncode, stdout=0, ok=r.returncode == 0 and len(R) >= 55,
                        stderr=r.stderr.decode(errors="replace")[-300:]))
    phases = {"read_ir", "read_S", "parse_layout", "walk", "run", "touch", "boundary", "live_after", "frametest", "epi",
              "text", "meta", "ins", "layout_fields", "field0", "field1", "field2", "text-result", "flags"}
    res.append(dict(id="e6fc-every-phase-reached", expect="every injected phase reached in some type",
                    exit=0, stdout=0, ok=phases <= reached, missing=sorted(phases - reached)))
    n_ok = sum(r["ok"] for r in res)
    summary = dict(total=len(res), ok=n_ok, adversarial=sum(r["id"].startswith("fast-path-adv-") for r in res),
                   valid_variants=sum(r["id"].startswith("fast-path-ok-") for r in res),
                   fc=sum(r["id"].startswith("e6fc-") for r in res), cases=res)
    out.write_text(json.dumps(summary, indent=1) + "\n")
    for r in res:
        if not r["ok"]:
            print("FAIL", r["id"], r.get("exit"), r.get("reason", r.get("stderr", ""))[:200])
    print(f"p2enc_test: {n_ok}/{len(res)} ok (adversarial {summary['adversarial']}, valid variants "
          f"{summary['valid_variants']}, fault injections {summary['fc']})")
    return 0 if n_ok == len(res) else 1


if __name__ == "__main__":
    sys.exit(main())
