#!/usr/bin/env python3
"""Call graph and link tables of the real MarshalSSZTo of the thirteen flat
development types that had no encoder link table (v1alpha1 BlobIdentifier, DepositMessage, Deposit_Data,
PendingPartialWithdrawal, SyncCommitteeMessage, PendingConsolidation, PendingDeposit, PowBlock,
HistoricalSummary, SigningData, SyncAggregatorSelectionData, ValidatorBalance, VoluntaryExit) on the Go 1.26.10
ELF (the same ELF as prysm/go1.26.10/e2e/link; the text of `h6link.py` with the function set and the data items changed).
Checkpoint, BeaconBlockHeader and Eth1Data have their encoder tables in e2e/link, e2e/bh/link and e2e/e1/link.
No primitives MarshalSSZTo is called by these functions (the call graph lists every call target), so no callee
encoder is in the set.

Usage (Python 3 standard library only; python3 -I -B; the steps after `filter` are gated):
  enc2link.py callgraph <objdump> <out.json>          call targets with contract class
  enc2link.py filter <outdir> <objdump> <elf> <nm>    <outdir>/target.objdump of FUNCS (+ ELF/nm links)
  enc2link.py data <outdir> <cp-linkdir> <e1-linkdir> after `conv.py <outdir>/target.objdump
                                                      <outdir>/p1bin-amd64.nm <outdir>/norm --norm`:
                                                      write <outdir>/data/*.data (link/data.py's code)
Then `link/check.py <outdir>` (a)-(f). Committed copy: prysm/go1.26.10/e2e/enc2/link.
Decoders, SizeSSZ, MarshalSSZ and HashTreeRoot are not in the set.
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

V1A1 = "github.com/OffchainLabs/prysm/v7/proto/prysm/v1alpha1"
TYPES = [("BlobIdentifier", "bi"), ("DepositMessage", "dm"), ("Deposit_Data", "dd"),
         ("PendingPartialWithdrawal", "pw"), ("SyncCommitteeMessage", "sc"), ("PendingConsolidation", "pc"),
         ("PendingDeposit", "pd"), ("PowBlock", "pb"), ("HistoricalSummary", "hs"), ("SigningData", "sd"),
         ("SyncAggregatorSelectionData", "sa"), ("ValidatorBalance", "vb"), ("VoluntaryExit", "ve")]
FUNCS = [f"{V1A1}.(*{t}).MarshalSSZTo" for t, _ in TYPES]
SCOPE = {f: "in (ENC2 encoder)" for f in FUNCS}
CLASS = dict(adlink.CLASS)
CLASS.update({
    "runtime.moveSliceNoCapNoScan": ("d", "no contract in the tree; recorded only (the survey gives its branch); "
                                          "no claim of unit E2-P uses it"),
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
    asm = {"an encoder calls a MarshalSSZTo": any("MarshalSSZTo" in c["target"] for f in FUNCS
                                                  for c in res[f]["calls"])}
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


def items(outdir, cpdir, e1dir):
    """Per encoder: the address-only error global `<p>ErrBytesLength` (length 0) when its code loads it
    (`mov X(%rip),%rdi`). Every growslice is asserted to take the uint8 type word of the Checkpoint set in %rsi
    (the literal of `e2elink.items`); ssz.ErrBytesLength is asserted equal to the Checkpoint and Eth1Data
    encoders' operand; no makeslice, newobject or fmt.errorf."""
    spec = importlib.util.spec_from_file_location("data", LINK / "data.py")
    data = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(data)
    V = "github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1"
    cu = e2elink.ins(cpdir, f"{e2elink.CP}.UnmarshalSSZ")
    cm = e2elink.ins(cpdir, f"{e2elink.CP}.MarshalSSZTo")
    em = e2elink.ins(e1dir, f"{V}.Eth1Data.MarshalSSZTo")
    lea = r"lea ([A-Za-z0-9_.]+)(?:\+(\d+))?\(%rip\),%{}"
    u8 = e2elink.operand([cu[cu.index("callq runtime.makeslice") - 3]], lea.format("rax"))
    assert u8 == ("type__", 387072), u8
    ebp = r"mov ([A-Za-z0-9_.]+)\(%rip\),%rdi()"
    ebl = e2elink.operand(cm, ebp)
    assert ebl == e2elink.operand(em, ebp), ebl
    its = []
    for t, p in TYPES:
        m = e2elink.ins(outdir, f"{V}.{t}.MarshalSSZTo")
        gs = [i for i, l in enumerate(m) if l == "callq runtime.growslice"]
        for i in gs:
            assert any(e2elink.operand([m[j]], lea.format("rsi")) == u8 for j in range(i - 4, i)
                       if re.fullmatch(lea.format("rsi"), m[j])), ("growslice type word", t, i)
        assert not any(l in ("callq runtime.makeslice", "callq runtime.newobject", "callq fmt.errorf")
                       for l in m), t
        has_ebl = any(re.fullmatch(ebp, l) for l in m)
        if has_ebl:
            assert e2elink.operand(m, ebp) == ebl, t
            its.append((f"{p}ErrBytesLength", ebl[0], 0, 0, []))
        print("type", t, "growslice", len(gs), "ErrBytesLength", has_ebl)
    return data, its


def write_data(outdir, cpdir, e1dir):
    data, its = items(outdir, cpdir, e1dir)
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
