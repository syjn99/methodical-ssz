#!/usr/bin/env python3
"""H3 hold-out: call graph and link tables of the real v1alpha1.BlobIdentifier and v1alpha1.DepositMessage
UnmarshalSSZ on the Go 1.26.10 ELF (the same ELF as prysm/go1.26.10/link-set; written after the
H3 hold-out was opened at 2026-11-11T04:26:30Z; the text of `e1link.py` with the function set and the data items changed).

Usage (Python 3 standard library only; python3 -I -B; the steps after `filter` are gated):
  h3link.py callgraph <objdump> <out.json>          call targets with contract class
  h3link.py filter <outdir> <objdump> <elf> <nm>    <outdir>/target.objdump of FUNCS (+ ELF/nm links)
  h3link.py data <outdir> <cp-linkdir> <ad-linkdir> after `conv.py <outdir>/target.objdump
                                                    <outdir>/p1bin-amd64.nm <outdir>/norm --norm`:
                                                    write <outdir>/data/*.data (link/data.py's code)
Then `link/check.py <outdir>` (a)-(f). Committed copy: prysm/go1.26.10/link-set.
Encoders, SizeSSZ and HashTreeRoot are not in the set (out of H3 scope).
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
FUNCS = [f"{V1A1}.(*BlobIdentifier).UnmarshalSSZ", f"{V1A1}.(*DepositMessage).UnmarshalSSZ"]
SCOPE = {FUNCS[0]: "in (H3 decoder)", FUNCS[1]: "in (H3 decoder)"}
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
    """The two decoders have no fmt.errorf, newobject or growslice call. The shared operands (uint8 type
    word of makeslice, ssz.ErrSize, writeBarrier) are asserted equal to the Checkpoint / AttestationData
    sets' operands. check.py (f) needs one data file at least: the set writes the address-only error global
    that each decoder names (biErrSize, dmErrSize; length 0)."""
    spec = importlib.util.spec_from_file_location("data", LINK / "data.py")
    data = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(data)
    V = "github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1"
    bu = e2elink.ins(outdir, f"{V}.BlobIdentifier.UnmarshalSSZ")
    du = e2elink.ins(outdir, f"{V}.DepositMessage.UnmarshalSSZ")
    cu = e2elink.ins(cpdir, f"{e2elink.CP}.UnmarshalSSZ")
    au = e2elink.ins(addir, f"{V}.AttestationData.UnmarshalSSZ")
    lea = r"lea ([A-Za-z0-9_.]+)(?:\+(\d+))?\(%rip\),%{}"
    u8 = e2elink.operand([cu[cu.index("callq runtime.makeslice") - 3]], lea.format("rax"))
    wb = r"cmpl \$0x0,([A-Za-z0-9_.]+)(?:\+(\d+))?\(%rip\)"
    esz = e2elink.operand(cu, r"mov ([A-Za-z0-9_.]+)\(%rip\),%rax()")
    its = []
    for fn, n, tag in ((bu, 1, "bi"), (du, 2, "dm")):
        mks = [i for i, l in enumerate(fn) if l == "callq runtime.makeslice"]
        assert len(mks) == n, (tag, mks)
        for i in mks:
            assert any(e2elink.operand([fn[j]], lea.format("rax")) == u8 for j in range(i - 4, i)
                       if re.fullmatch(lea.format("rax"), fn[j])), ("u8 word", tag, i)
        assert not any(l in ("callq fmt.errorf", "callq runtime.newobject", "callq runtime.growslice")
                       for l in fn), tag
        assert e2elink.operand(fn, r"mov ([A-Za-z0-9_.]+)\(%rip\),%rax()") == esz, tag
        assert e2elink.operand(fn, wb) == e2elink.operand(au, wb), tag
        its.append((f"{tag}ErrSize", esz[0], 0, 0, []))
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
