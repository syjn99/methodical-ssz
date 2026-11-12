#!/usr/bin/env python3
"""Eth1Data hold-out: call graph and link tables of the real v1alpha1.Eth1Data UnmarshalSSZ and MarshalSSZTo
on the Go 1.26.10 ELF (the same ELF as prysm/go1.26.10/e2e/link; written after the Eth1Data (H2)
hold-out was opened at 2026-11-11T01:59:11Z; the text of `bhlink.py` with the function set changed).

Usage (Python 3 standard library only; python3 -I -B; the steps after `filter` are gated):
  e1link.py callgraph <objdump> <out.json>          call targets with contract class
  e1link.py filter <outdir> <objdump> <elf> <nm>    <outdir>/target.objdump of FUNCS (+ ELF/nm links)
  e1link.py data <outdir> <cp-linkdir> <ad-linkdir> after `conv.py <outdir>/target.objdump
                                                    <outdir>/p1bin-amd64.nm <outdir>/norm --norm`:
                                                    write <outdir>/data/*.data (link/data.py's code)
Then `link/check.py <outdir>` (a)-(f). Committed copy: prysm/go1.26.10/e2e/e1/link.
SizeSSZ is not in the set (excluded from the hold-out claim). Shared items are asserted equal to
the Checkpoint / AttestationData sets' operands (see `items`).
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
FUNCS = [f"{V1A1}.(*Eth1Data).MarshalSSZTo", f"{V1A1}.(*Eth1Data).UnmarshalSSZ"]
SCOPE = {FUNCS[0]: "in (H2 encoder fast path)", FUNCS[1]: "in (H2 decoder)"}
CLASS = dict(adlink.CLASS)


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
    """Eth1Data has no fmt.errorf and no newobject call. The shared operands (uint8 type word of makeslice
    and growslice, ssz.ErrSize, ssz.ErrBytesLength, writeBarrier) are asserted equal to the Checkpoint /
    AttestationData sets' operands. check.py (f) needs one data file at least: the set writes the two
    address-only error globals that its own code names (e1ErrSize, e1ErrBytesLength; length 0)."""
    spec = importlib.util.spec_from_file_location("data", LINK / "data.py")
    data = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(data)
    E1 = "github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Eth1Data"
    du, dm = e2elink.ins(outdir, f"{E1}.UnmarshalSSZ"), e2elink.ins(outdir, f"{E1}.MarshalSSZTo")
    cu, cm = e2elink.ins(cpdir, f"{e2elink.CP}.UnmarshalSSZ"), e2elink.ins(cpdir, f"{e2elink.CP}.MarshalSSZTo")
    au = e2elink.ins(addir, "github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttestationData.UnmarshalSSZ")
    lea = r"lea ([A-Za-z0-9_.]+)(?:\+(\d+))?\(%rip\),%{}"
    u8 = e2elink.operand([cu[cu.index("callq runtime.makeslice") - 3]], lea.format("rax"))
    mks = [i for i, l in enumerate(du) if l == "callq runtime.makeslice"]
    assert len(mks) == 2, mks
    for i in mks:
        assert any(e2elink.operand([du[j]], lea.format("rax")) == u8 for j in range(i - 4, i)
                   if re.fullmatch(lea.format("rax"), du[j])), ("u8 word", i)
    gs = [i for i, l in enumerate(dm) if l == "callq runtime.growslice"]
    assert len(gs) == 3, gs
    for i in gs:
        assert any(e2elink.operand([dm[j]], lea.format("rsi")) == u8 for j in range(i - 3, i)
                   if re.fullmatch(lea.format("rsi"), dm[j])), ("growslice type word", i)
    assert not any(l in ("callq fmt.errorf", "callq runtime.newobject") for l in du + dm)
    esz = e2elink.operand(du, r"mov ([A-Za-z0-9_.]+)\(%rip\),%rax()")
    assert esz == e2elink.operand(cu, r"mov ([A-Za-z0-9_.]+)\(%rip\),%rax()"), esz
    ebl = e2elink.operand(dm, r"mov ([A-Za-z0-9_.]+)\(%rip\),%rdi()")
    assert ebl == e2elink.operand(cm, r"mov ([A-Za-z0-9_.]+)\(%rip\),%rdi()"), ebl
    wb = r"cmpl \$0x0,([A-Za-z0-9_.]+)(?:\+(\d+))?\(%rip\)"
    assert e2elink.operand(du, wb) == e2elink.operand(au, wb)
    its = [("e1ErrSize", esz[0], 0, 0, []), ("e1ErrBytesLength", ebl[0], 0, 0, [])]
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
