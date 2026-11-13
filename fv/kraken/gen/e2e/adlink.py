#!/usr/bin/env python3
"""Call graph, inlining record and link tables of the real v1alpha1.AttestationData SSZ
functions and their primitives callees on the Go 1.26.10 ELF.

Usage (Python 3 standard library only; python3 -I -B; the steps after `filter` are gated):
  adlink.py callgraph <objdump> <out.json> <m2.log>  call targets with contract class + inlining lines
  adlink.py filter <outdir> <objdump> <elf> <nm>     <outdir>/target.objdump of FUNCS (+ ELF/nm links)
  adlink.py data <outdir> <cp-linkdir>               after `conv.py <outdir>/target.objdump
                                                     <outdir>/p1bin-amd64.nm <outdir>/norm --norm`:
                                                     write <outdir>/data/*.data (link/data.py's code)
Then `link/check.py <outdir>` (a)-(f). Committed copy: prysm/go1.26.10/link-set. The Checkpoint
link tables (prysm/go1.26.10/link-set) are not changed; the items that both sets use (uint8 type word,
ssz.ErrSize, ssz.ErrBytesLength, errorString type) are asserted equal to the Checkpoint set's operands
and not written again. Every data item is located from an operand of the converted code.
"""
import importlib.util
import json
import pathlib
import re
import sys

HERE = pathlib.Path(__file__).resolve().parent
LINK = HERE.parent.parent / "link"
sys.path.insert(0, str(HERE))
import e2elink  # noqa: E402

PRIM = "github.com/OffchainLabs/prysm/v7/consensus-types/primitives"
V1A1 = "github.com/OffchainLabs/prysm/v7/proto/prysm/v1alpha1"
AD_M = ("SizeSSZ", "MarshalSSZTo", "UnmarshalSSZ")
PM = ("UnmarshalSSZ", "MarshalSSZTo", "MarshalSSZ", "SizeSSZ")
FUNCS = [f"{V1A1}.(*AttestationData).{m}" for m in AD_M] + \
        [f"{PRIM}.(*Slot).{m}" for m in PM] + [f"{PRIM}.(*CommitteeIndex).{m}" for m in PM]
SCOPE = {FUNCS[0]: "in (A4 size)", FUNCS[1]: "in (A4 encoder)", FUNCS[2]: "in (A3 decoder)",
         FUNCS[3]: "in (callee, function spec Prysm.Slot.Decode.accept_function_spec, A2)", FUNCS[7]: "in (callee, function spec Prysm.CommitteeIndex.Decode.accept_function_spec, A2)"}
for i in (4, 5, 6, 8, 9, 10):
    SCOPE[FUNCS[i]] = "record only (inlined into AttestationData.MarshalSSZTo or unused; out-of-line body unused)"
CP_U = f"{V1A1}.(*Checkpoint).UnmarshalSSZ"
CP_M = f"{V1A1}.(*Checkpoint).MarshalSSZTo"
CLASS = {
    "runtime.morestack_noctxt.abi0": ("c", "stack-guard premise g.stackguard0 < rsp: the jbe is proved not taken"),
    "runtime.makeslice": ("b", "MakesliceC (esz 1, uint8 type word, cnt 32)"),
    "runtime.memmove": ("b", "MemmoveC (n = 32)"),
    "runtime.growslice": ("b", "GrowsliceC (esz 1); main theorem: capacity sufficient, not called"),
    "runtime.convT64": ("b", "ConvT64C (Slot/CommitteeIndex length reject only; not on the accept specs)"),
    "runtime.gcWriteBarrier2": ("c", "writeBarrier = 0 premise: the cmpl/jne is proved to skip the call"),
    "runtime.newobject": ("b", "NewobjectC (Checkpoint type word, 72 bytes): decoder Source/Target, encoder nil "
                               "Source/Target; after fmt.errorf: the nil-result branch, excluded by rax != 0"),
    "fmt.errorf": ("b", "FmtErrorfWC (field wraps 'Slot: %w', 'CommitteeIndex: %w', 'Source: %w', 'Target: %w'); "
                        "decoder: unreachable_mc under the callee specs; encoder Source/Target: reachable when "
                        "a child Root has len != 32"),
    f"{PRIM}.(*Slot).UnmarshalSSZ": ("a", "function spec Prysm.Slot.Decode.accept_function_spec, proved from machine code"),
    f"{PRIM}.(*CommitteeIndex).UnmarshalSSZ": ("a", "function spec Prysm.CommitteeIndex.Decode.accept_function_spec, proved from machine code"),
    CP_U: ("a", "function spec Prysm.Checkpoint.Decode.accept_function_spec = Prysm.Checkpoint.Decode.accept (its runtime contracts stay hypotheses)"),
    CP_M: ("a", "function spec Prysm.Checkpoint.Encode.fast_path_function_spec = Prysm.Checkpoint.Encode.fast_path (its runtime contracts stay hypotheses)"),
}
INL = {
    "cannot_inline_Slot_UnmarshalSSZ": r"slot\.go:\d+:\d+: cannot inline \(\*Slot\)\.UnmarshalSSZ",
    "can_inline_Slot_MarshalSSZTo": r"slot\.go:\d+:\d+: can inline \(\*Slot\)\.MarshalSSZTo",
    "cannot_inline_CommitteeIndex_UnmarshalSSZ": r"committee_index\.go:\d+:\d+: cannot inline \(\*CommitteeIndex\)\.UnmarshalSSZ",
    "can_inline_CommitteeIndex_MarshalSSZTo": r"committee_index\.go:\d+:\d+: can inline \(\*CommitteeIndex\)\.MarshalSSZTo",
    "ad_marshal_inlines_Slot_MarshalSSZTo": r"phase0\.ssz\.go:2[34]\d:\d+: inlining call to primitives\.\(\*Slot\)\.MarshalSSZTo",
    "ad_marshal_inlines_CommitteeIndex_MarshalSSZTo": r"phase0\.ssz\.go:2[34]\d:\d+: inlining call to primitives\.\(\*CommitteeIndex\)\.MarshalSSZTo",
    "ad_unmarshal_inlines_any_primitives": r"phase0\.ssz\.go:(2[89]\d|30\d|31[01]):\d+: inlining call to primitives\.",
}


def callgraph(objdump, out, mlog):
    want, cur = set(FUNCS), None
    res = {f: {"addr": None, "instructions": 0, "calls": [], "scope": SCOPE[f]} for f in FUNCS}
    for line in open(objdump):
        if line.startswith("TEXT "):
            name = line.split()[1].removesuffix("(SB)")
            cur = name if name in want else None
            continue
        if cur is None or not line.strip():
            continue
        mm = re.match(r"\s*\S+:\d+\s+0x([0-9a-f]+)\s", line)
        if not mm:
            continue
        addr = int(mm[1], 16)
        r = res[cur]
        if r["addr"] is None:
            r["addr"] = addr
        r["instructions"] += 1
        m = re.search(r"CALL (\S+)\(SB\)", line)
        if m:
            c = CLASS.get(m[1])
            r["calls"].append({"site": hex(addr), "target": m[1], "class": c[0] if c else "UNCLASSIFIED",
                               "how": c[1] if c else ""})
    text = open(mlog, errors="replace").read().splitlines()
    inl = {k: sorted({l.strip() for l in text if re.search(p, l)}) for k, p in INL.items()}
    counts = {f: {} for f in FUNCS}
    for f in FUNCS:
        for c in res[f]["calls"]:
            counts[f][c["target"]] = counts[f].get(c["target"], 0) + 1
    enc = res[FUNCS[1]]["calls"]
    asm = {"AttestationData.MarshalSSZTo calls a Slot/CommitteeIndex method": any(
        "Slot" in c["target"] or "CommitteeIndex" in c["target"] for c in enc)}
    unc = [(f, c["target"]) for f in FUNCS for c in res[f]["calls"] if c["class"] == "UNCLASSIFIED"
           and SCOPE[f].startswith("in")]
    missing = [f for f in FUNCS if res[f]["addr"] is None]
    for f in FUNCS:
        res[f]["addr"] = hex(res[f]["addr"]) if res[f]["addr"] is not None else None
    doc = {"functions": res, "call_counts": counts, "inlining_m2": inl, "asm_inlining": asm,
           "unclassified_in_scope": unc, "missing": missing}
    json.dump(doc, open(out, "w"), indent=1)
    for f in FUNCS:
        print(f"{f.split('/')[-1]:58} {res[f]['instructions']:4} instr  {counts[f]}")
    print("inlining", {k: len(v) for k, v in inl.items()}, "asm", asm, "unclassified", unc, "missing", missing)
    return 1 if (missing or unc) else 0


def filt(outdir, objdump, elf, nm):
    e2elink.callgraph.FUNCS = FUNCS
    return e2elink.filt(outdir, objdump, elf, nm)


def back_lea(lines, i, reg="rax"):
    """Operand (label, off) of the nearest `lea X(%rip),%reg` before line i (nops skipped)."""
    pat = r"lea ([A-Za-z0-9_.]+)(?:\+(\d+))?\(%rip\),%" + reg
    for j in range(i - 1, max(i - 4, -1), -1):
        m = re.fullmatch(pat, lines[j])
        if m:
            return (m[1], int(m[2]) if m[2] else 0)
        if not lines[j].startswith("nop"):
            break
    raise AssertionError(("no lea before", i, lines[i]))


def items(outdir, cpdir):
    spec = importlib.util.spec_from_file_location("data", LINK / "data.py")
    data = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(data)
    AD = "github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttestationData"
    du, dm = e2elink.ins(outdir, f"{AD}.UnmarshalSSZ"), e2elink.ins(outdir, f"{AD}.MarshalSSZTo")
    cu, cm = e2elink.ins(cpdir, f"{e2elink.CP}.UnmarshalSSZ"), e2elink.ins(cpdir, f"{e2elink.CP}.MarshalSSZTo")
    lea = r"lea ([A-Za-z0-9_.]+)(?:\+(\d+))?\(%rip\),%{}"
    # shared with the Checkpoint set: asserted equal, not written again
    u8 = e2elink.operand([cu[cu.index("callq runtime.makeslice") - 3]], lea.format("rax"))
    assert back_lea(du, du.index("callq runtime.makeslice") - 2) == u8 or \
        e2elink.operand([du[du.index("callq runtime.makeslice") - 3]], lea.format("rax")) == u8
    assert e2elink.operand(dm, lea.format("rsi")) == u8
    assert e2elink.operand(du, r"mov ([A-Za-z0-9_.]+)\(%rip\),%rax()") == \
        e2elink.operand(cu, r"mov ([A-Za-z0-9_.]+)\(%rip\),%rax()")
    assert e2elink.operand(dm, r"mov ([A-Za-z0-9_.]+)\(%rip\),%rdi()") == \
        e2elink.operand(cm, r"mov ([A-Za-z0-9_.]+)\(%rip\),%rdi()")
    estype = back_lea(cu, cu.index("callq runtime.newobject"))
    # newobject sites: the errorString ones (after fmt.errorf) and the Checkpoint ones
    def nobj(lines):
        return [back_lea(lines, i) for i, l in enumerate(lines) if l == "callq runtime.newobject"]
    dn, mn = nobj(du), nobj(dm)
    cpt = {o for o in dn + mn if o != estype}
    assert len(cpt) == 1 and dn.count(estype) == 4 and mn.count(estype) == 2, (dn, mn, estype)
    cpt = cpt.pop()
    assert dn.count(cpt) == 2 and mn.count(cpt) == 2, (dn, mn)
    # the four field wraps of the decoder (order Slot, CommitteeIndex, Source, Target), the encoder's two
    def fmts(lines):
        out = []
        for i, l in enumerate(lines):
            if l == "callq fmt.errorf":
                k = next(j for j in range(i - 1, i - 8, -1) if re.fullmatch(r"mov \$0x[0-9a-f]+,%ebx", lines[j]))
                out.append((back_lea(lines, k + 1) if False else
                            e2elink.operand([lines[k - 1]], lea.format("rax")),
                            int(re.fullmatch(r"mov \$0x([0-9a-f]+),%ebx", lines[k])[1], 16)))
        return out
    df, mf = fmts(du), fmts(dm)
    assert [n for _, n in df] == [8, 18, 10, 10] and mf == df[2:], (df, mf)
    T = data.ABI_TYPE_WORDS
    its = [
        ("typeCheckpoint", cpt[0], cpt[1], 48, T),
        (None, df[0][0][0], df[0][0][1], df[0][1], []),
        (None, df[1][0][0], df[1][0][1], df[1][1], []),
        (None, df[2][0][0], df[2][0][1], df[2][1], []),
        (None, df[3][0][0], df[3][0][1], df[3][1], []),
    ]
    return data, its


def write_data(outdir, cpdir):
    data, its = items(outdir, cpdir)
    for it in its:
        print("item", it[:4])
    data.ITEMS = its
    data.main(pathlib.Path(outdir))
    return 0


if __name__ == "__main__":
    c = sys.argv[1]
    if c == "callgraph":
        sys.exit(callgraph(*sys.argv[2:5]))
    if c == "filter":
        sys.exit(filt(*sys.argv[2:6]))
    if c == "data":
        sys.exit(write_data(*sys.argv[2:4]))
    sys.exit(f"unknown command {c}")
