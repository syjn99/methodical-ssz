#!/usr/bin/env python3
"""H5 hold-out: call graph and link tables of the real v1alpha1.SyncCommitteeMessage and v1alpha1.PendingConsolidation
UnmarshalSSZ on the Go 1.26.10 ELF (the same ELF as prysm/go1.26.10/e2e/link; written after the
H5 hold-out was opened at 2026-11-11T11:25:14Z; the text of `h4link.py` with the function set and the data items changed).

Usage (Python 3 standard library only; python3 -I -B; the steps after `filter` are gated):
  h5link.py callgraph <objdump> <out.json>          call targets with contract class
  h5link.py filter <outdir> <objdump> <elf> <nm>    <outdir>/target.objdump of FUNCS (+ ELF/nm links)
  h5link.py data <outdir> <cp-linkdir> <ad-linkdir> after `conv.py <outdir>/target.objdump
                                                    <outdir>/p1bin-amd64.nm <outdir>/norm --norm`:
                                                    write <outdir>/data/*.data (link/data.py's code)
Then `link/check.py <outdir>` (a)-(f). Committed copy: prysm/go1.26.10/e2e/h5/link.
Encoders, SizeSSZ and HashTreeRoot are not in the set (out of H5 scope).
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
import adlink  # noqa: E402

PRIM = "github.com/OffchainLabs/prysm/v7/consensus-types/primitives"
V1A1 = "github.com/OffchainLabs/prysm/v7/proto/prysm/v1alpha1"
FUNCS = [f"{V1A1}.(*SyncCommitteeMessage).UnmarshalSSZ", f"{V1A1}.(*PendingConsolidation).UnmarshalSSZ"]
SCOPE = {FUNCS[0]: "in (H5 decoder)", FUNCS[1]: "in (H5 decoder)"}
CLASS = dict(adlink.CLASS)
CLASS.update({
    f"{PRIM}.(*ValidatorIndex).UnmarshalSSZ": ("a", "function spec E2eScal.ViUAccC, proved from machine code (H1)"),
    f"{PRIM}.(*Slot).UnmarshalSSZ": ("a", "function spec SlUAccC, proved from machine code (E2eAd)"),
    "fmt.errorf": ("b", "FmtErrorfWC (field wraps of the callee errors); decoder: unreachable under the callee specs"),
    "runtime.newobject": ("b", "NewobjectC errorString (after fmt.errorf: nil-result branch, excluded by rax != 0)"),
})


def callgraph(objdump, out):
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
    counts = {f: {} for f in FUNCS}
    for f in FUNCS:
        for c in res[f]["calls"]:
            counts[f][c["target"]] = counts[f].get(c["target"], 0) + 1
    unc = [(f, c["target"]) for f in FUNCS for c in res[f]["calls"] if c["class"] == "UNCLASSIFIED"
           and SCOPE[f].startswith("in")]
    missing = [f for f in FUNCS if res[f]["addr"] is None]
    for f in FUNCS:
        res[f]["addr"] = hex(res[f]["addr"]) if res[f]["addr"] is not None else None
    asm = {}
    doc = {"functions": res, "call_counts": counts, "asm_inlining": asm, "unclassified_in_scope": unc,
           "missing": missing}
    json.dump(doc, open(out, "w"), indent=1)
    for f in FUNCS:
        print(f"{f.split('/')[-1]:58} {res[f]['instructions']:4} instr  {counts[f]}")
    print("asm", asm, "unclassified", unc, "missing", missing)
    return 1 if (missing or unc) else 0


def filt(outdir, objdump, elf, nm):
    e2elink.callgraph.FUNCS = FUNCS
    return e2elink.filt(outdir, objdump, elf, nm)


def items(outdir, cpdir, addir):
    """SyncCommitteeMessage has two makeslice calls (BlockRoot 32, Signature 96) and calls the Slot and
    ValidatorIndex decoders, wrapping their errors with fmt.errorf ("Slot: %w", "ValidatorIndex: %w").
    PendingConsolidation has no makeslice; it calls the ValidatorIndex decoder twice and wraps the errors
    ("SourceIndex: %w", "TargetIndex: %w"; `bhlink.py` idiom). The shared operands (uint8 type word,
    ssz.ErrSize, writeBarrier, errorString type) are asserted equal to the Checkpoint / AttestationData sets'
    operands. Data files: the address-only error global of each decoder (smErrSize, pcErrSize; length 0) and
    the four format strings."""
    spec = importlib.util.spec_from_file_location("data", LINK / "data.py")
    data = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(data)
    V = "github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1"
    su = e2elink.ins(outdir, f"{V}.SyncCommitteeMessage.UnmarshalSSZ")
    pu = e2elink.ins(outdir, f"{V}.PendingConsolidation.UnmarshalSSZ")
    cu = e2elink.ins(cpdir, f"{e2elink.CP}.UnmarshalSSZ")
    au = e2elink.ins(addir, f"{V}.AttestationData.UnmarshalSSZ")
    lea = r"lea ([A-Za-z0-9_.]+)(?:\+(\d+))?\(%rip\),%{}"
    u8 = e2elink.operand([cu[cu.index("callq runtime.makeslice") - 3]], lea.format("rax"))
    wb = r"cmpl \$0x0,([A-Za-z0-9_.]+)(?:\+(\d+))?\(%rip\)"
    esz = e2elink.operand(cu, r"mov ([A-Za-z0-9_.]+)\(%rip\),%rax()")
    back = adlink.back_lea
    estype = back(cu, cu.index("callq runtime.newobject"))
    its = []

    def fmts(lines):
        out = []
        for i, l in enumerate(lines):
            if l == "callq fmt.errorf":
                k = next(j for j in range(i - 1, i - 8, -1) if re.fullmatch(r"mov \$0x[0-9a-f]+,%ebx", lines[j]))
                out.append((e2elink.operand([lines[k - 1]], lea.format("rax")),
                            int(re.fullmatch(r"mov \$0x([0-9a-f]+),%ebx", lines[k])[1], 16)))
        return out
    # SyncCommitteeMessage
    mks = [i for i, l in enumerate(su) if l == "callq runtime.makeslice"]
    assert len(mks) == 2, mks
    for i in mks:
        assert any(e2elink.operand([su[j]], lea.format("rax")) == u8 for j in range(i - 5, i)
                   if re.fullmatch(lea.format("rax"), su[j])), ("u8 word", i)
    assert not any(l == "callq runtime.growslice" for l in su)
    assert e2elink.operand(su, r"mov ([A-Za-z0-9_.]+)\(%rip\),%rax()") == esz
    assert e2elink.operand(su, wb) == e2elink.operand(au, wb)
    sn = [back(su, i) for i, l in enumerate(su) if l == "callq runtime.newobject"]
    assert sn == [estype, estype], (sn, estype)
    its.append(("smErrSize", esz[0], 0, 0, []))
    sf = fmts(su)
    assert [n for _, n in sf] == [8, 18], sf  # "Slot: %w", "ValidatorIndex: %w"
    its.append(("smFmtSlot", sf[0][0][0], sf[0][0][1], sf[0][1], []))
    its.append(("smFmtVi", sf[1][0][0], sf[1][0][1], sf[1][1], []))
    # PendingConsolidation
    assert not any(l in ("callq runtime.makeslice", "callq runtime.growslice") for l in pu)
    assert e2elink.operand(pu, r"mov ([A-Za-z0-9_.]+)\(%rip\),%rax()") == esz
    pn = [back(pu, i) for i, l in enumerate(pu) if l == "callq runtime.newobject"]
    assert pn == [estype, estype], (pn, estype)
    its.append(("pcErrSize", esz[0], 0, 0, []))
    pf = fmts(pu)
    assert [n for _, n in pf] == [15, 15], pf  # "SourceIndex: %w", "TargetIndex: %w"
    its.append(("pcFmtSource", pf[0][0][0], pf[0][0][1], pf[0][1], []))
    its.append(("pcFmtTarget", pf[1][0][0], pf[1][0][1], pf[1][1], []))
    return data, its


def write_data(outdir, cpdir, addir):
    data, its = items(outdir, cpdir, addir)
    for it in its:
        print("item", it[:4])
    data.ITEMS = its
    data.main(pathlib.Path(outdir))
    return 0


if __name__ == "__main__":
    c = sys.argv[1]
    if c == "callgraph":
        sys.exit(callgraph(*sys.argv[2:4]))
    if c == "filter":
        sys.exit(filt(*sys.argv[2:6]))
    if c == "data":
        sys.exit(write_data(*sys.argv[2:5]))
    sys.exit(f"unknown command {c}")
