#!/usr/bin/env python3
"""Flat-type hold-out (H7): call graph and link tables of the real UnmarshalSSZ and MarshalSSZTo of the 24 flat fixed-size
types outside the development population (fv/kraken/prysm/proof-inventory.md at the FLAT24 freeze) on the Go 1.26.10
ELF (the same ELF as prysm/go1.26.10/e2e/link; written after the H7 hold-out was opened at 2026-11-12T05:59:42Z;
the text of `h6link.py` + `enc2link.py` with the function set changed and the data items made per function).

Usage (Python 3 standard library only; python3 -I -B; every step runs gated):
  f24link.py callgraph <objdump> <out.json>          call targets with contract class
  f24link.py filter <outdir> <objdump> <elf> <nm>    <outdir>/target.objdump of FUNCS (+ ELF/nm links)
  f24link.py data <outdir> <cp-linkdir> <ad-linkdir> <e1-linkdir>
                                                     after `conv.py <outdir>/target.objdump
                                                     <outdir>/p1bin-amd64.nm <outdir>/norm --norm`:
                                                     write <outdir>/data/*.data (link/data.py's code)
Then `link/check.py <outdir>` (a)-(f). Committed copy: prysm/go1.26.10/e2e/f24/link.
SizeSSZ, MarshalSSZ and HashTreeRoot are not in the set.
A call target without a contract in the tree is recorded with class "d" (no claim of this unit uses it).
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
PKG = {"v1": "github.com/OffchainLabs/prysm/v7/proto/engine/v1",
       "v1alpha1": "github.com/OffchainLabs/prysm/v7/proto/prysm/v1alpha1"}
SPKG = {k: v.replace("/", "_").replace("github.com_", "github.com_") for k, v in PKG.items()}
TYPES = [("v1", "BuilderDepositRequest", "bdr"), ("v1", "BuilderExitRequest", "ber"),
         ("v1", "ConsolidationRequest", "cnr"), ("v1", "DepositRequest", "dpr"), ("v1", "Withdrawal", "wdl"),
         ("v1", "WithdrawalRequest", "wdr"), ("v1alpha1", "BLSToExecutionChange", "btc"),
         ("v1alpha1", "BeaconBlocksByRangeRequest", "bbr"), ("v1alpha1", "BlobSidecarsByRangeRequest", "bsr"),
         ("v1alpha1", "Builder", "bld"), ("v1alpha1", "BuilderPendingWithdrawal", "bpw"),
         ("v1alpha1", "BuilderPreferences", "bpf"), ("v1alpha1", "ENRForkID", "efi"),
         ("v1alpha1", "ExecutionPayloadEnvelopesByRangeRequest", "epr"), ("v1alpha1", "Fork", "frk"),
         ("v1alpha1", "ForkData", "fkd"), ("v1alpha1", "PartialDataColumnGroupID", "pdc"),
         ("v1alpha1", "PayloadAttestationData", "pad"), ("v1alpha1", "ProposerPreferences", "ppf"),
         ("v1alpha1", "Status", "sts"), ("v1alpha1", "StatusV2", "st2"), ("v1alpha1", "Validator", "vld"),
         ("v1alpha1", "ValidatorIdentity", "vid"), ("v1alpha1", "ValidatorRegistrationV1", "vr1")]
DEC = [f"{PKG[k]}.(*{t}).UnmarshalSSZ" for k, t, _ in TYPES]
ENC = [f"{PKG[k]}.(*{t}).MarshalSSZTo" for k, t, _ in TYPES]
FUNCS = DEC + ENC
SCOPE = {f: "in (FLAT24 decoder)" for f in DEC} | {f: "in (FLAT24 encoder)" for f in ENC}
CLASS = dict(adlink.CLASS)
CLASS.update({
    f"{PRIM}.(*ValidatorIndex).UnmarshalSSZ": ("a", "function spec E2eScal.ViUAccC, proved from machine code (H1)"),
    f"{PRIM}.(*Slot).UnmarshalSSZ": ("a", "function spec Prysm.Slot.Decode.accept_function_spec, proved from machine code (E2eAd)"),
    f"{PRIM}.(*Epoch).UnmarshalSSZ": ("a", "function spec Prysm.Epoch.Decode.accept_function_spec, proved from machine code (E2e)"),
    "fmt.errorf": ("b", "FmtErrorfWC (field wraps of the callee errors); decoder: unreachable under the callee specs"),
    "runtime.newobject": ("b", "NewobjectC errorString (after fmt.errorf: nil-result branch, excluded by rax != 0)"),
    "runtime.moveSliceNoCapNoScan": ("d", "no contract in the tree; recorded only"),
})


def sname(k, t, m):
    return f"{SPKG[k]}.{t}.{m}"


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
            r["calls"].append({"site": hex(addr), "target": m[1], "class": c[0] if c else "d",
                               "how": c[1] if c else "no contract in the tree; recorded only (FLAT24 link)"})
    counts = {f: {} for f in FUNCS}
    for f in FUNCS:
        for c in res[f]["calls"]:
            counts[f][c["target"]] = counts[f].get(c["target"], 0) + 1
    new = sorted({c["target"] for f in FUNCS for c in res[f]["calls"] if c["target"] not in CLASS})
    missing = [f for f in FUNCS if res[f]["addr"] is None]
    for f in FUNCS:
        res[f]["addr"] = hex(res[f]["addr"]) if res[f]["addr"] is not None else None
    asm = {"an encoder calls a MarshalSSZTo": any("MarshalSSZTo" in c["target"] for f in ENC
                                                  for c in res[f]["calls"])}
    doc = {"functions": res, "call_counts": counts, "asm_inlining": asm,
           "targets_without_contract_class": new, "missing": missing}
    json.dump(doc, open(out, "w"), indent=1)
    for f in FUNCS:
        print(f"{f.split('/')[-1]:62} {res[f]['instructions']:4} instr  {counts[f]}")
    print("asm", asm, "targets without contract class", new, "missing", missing)
    return 1 if missing else 0


def filt(outdir, objdump, elf, nm):
    e2elink.callgraph.FUNCS = FUNCS
    return e2elink.filt(outdir, objdump, elf, nm)


def items(outdir, cpdir, addir, e1dir):
    """Per decoder: every address-only error global loaded into rax (`<p>ErrSize` for ssz.ErrSize, else
    `<p>Err<Name>`, length 0) and the format
    strings of its fmt.errorf wraps (`<p>Fmt<k>`, in code order). Per encoder: the address-only
    `<p>ErrBytesLength` when its code loads it. Every makeslice / growslice is checked for the uint8 type word of
    the Checkpoint set (`type__+387072`) and the result is printed per function (no assertion: a type whose
    literal differs is a fact for Part 1, not a link failure). ssz.ErrSize / ssz.ErrBytesLength / writeBarrier /
    errorString are asserted equal to the Checkpoint / AttestationData / Eth1Data operands where present."""
    spec = importlib.util.spec_from_file_location("data", LINK / "data.py")
    data = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(data)
    V = "github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1"
    cu = e2elink.ins(cpdir, f"{e2elink.CP}.UnmarshalSSZ")
    cm = e2elink.ins(cpdir, f"{e2elink.CP}.MarshalSSZTo")
    au = e2elink.ins(addir, f"{V}.AttestationData.UnmarshalSSZ")
    em = e2elink.ins(e1dir, f"{V}.Eth1Data.MarshalSSZTo")
    lea = r"lea ([A-Za-z0-9_.]+)(?:\+(\d+))?\(%rip\),%{}"
    u8 = e2elink.operand([cu[cu.index("callq runtime.makeslice") - 3]], lea.format("rax"))
    assert u8 == ("type__", 387072), u8
    wb = r"cmpl \$0x0,([A-Za-z0-9_.]+)(?:\+(\d+))?\(%rip\)"
    eszp = r"mov ([A-Za-z0-9_.]+)\(%rip\),%rax()"
    esz = e2elink.operand(cu, eszp)
    back = adlink.back_lea
    estype = back(cu, cu.index("callq runtime.newobject"))
    ebp = r"mov ([A-Za-z0-9_.]+)\(%rip\),%rdi()"
    ebl = e2elink.operand(cm, ebp)
    assert ebl == e2elink.operand(em, ebp), ebl
    its = []

    def fmts(lines):
        out = []
        for i, l in enumerate(lines):
            if l == "callq fmt.errorf":
                k = next(j for j in range(i - 1, i - 8, -1) if re.fullmatch(r"mov \$0x[0-9a-f]+,%ebx", lines[j]))
                out.append((e2elink.operand([lines[k - 1]], lea.format("rax")),
                            int(re.fullmatch(r"mov \$0x([0-9a-f]+),%ebx", lines[k])[1], 16)))
        return out

    def u8word(lines, i, reg, back_n):
        return any(e2elink.operand([lines[j]], lea.format(reg)) == u8 for j in range(i - back_n, i)
                   if re.fullmatch(lea.format(reg), lines[j]))
    for k, t, p in TYPES:
        u = e2elink.ins(outdir, sname(k, t, "UnmarshalSSZ"))
        mks = [i for i, l in enumerate(u) if l == "callq runtime.makeslice"]
        mk_u8 = [u8word(u, i, "rax", 5) for i in mks]
        assert not any(l == "callq runtime.growslice" for l in u), t
        gl = sorted({re.fullmatch(eszp, l)[1] for l in u if re.fullmatch(eszp, l)})
        for g in gl:
            if g == esz[0]:
                its.append((f"{p}ErrSize", esz[0], 0, 0, []))
            else:
                its.append((f"{p}Err{g.split('.')[-1]}", g, 0, 0, []))
        if mks:
            assert e2elink.operand(u, wb) == e2elink.operand(au, wb), t
        nn = [back(u, i) for i, l in enumerate(u) if l == "callq runtime.newobject"]
        assert all(x == estype for x in nn), (t, nn, estype)
        for j, ((sym, off), n) in enumerate(fmts(u)):
            its.append((f"{p}Fmt{j}", sym, off, n, []))
        print("dec", t, "makeslice", len(mks), "u8 literal", mk_u8, "newobject", len(nn), "fmt", len(fmts(u)),
              "error globals", gl)
        m = e2elink.ins(outdir, sname(k, t, "MarshalSSZTo"))
        gs = [i for i, l in enumerate(m) if l == "callq runtime.growslice"]
        gs_u8 = [u8word(m, i, "rsi", 4) for i in gs]
        assert not any(l in ("callq runtime.makeslice", "callq runtime.newobject", "callq fmt.errorf")
                       for l in m), t
        has_ebl = any(re.fullmatch(ebp, l) for l in m)
        if has_ebl:
            assert e2elink.operand(m, ebp) == ebl, t
            its.append((f"{p}ErrBytesLength", ebl[0], 0, 0, []))
        print("enc", t, "growslice", len(gs), "u8 literal", gs_u8, "ErrBytesLength", has_ebl)
    return data, its


def write_data(outdir, cpdir, addir, e1dir):
    data, its = items(outdir, cpdir, addir, e1dir)
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
        sys.exit(write_data(*sys.argv[2:6]))
    sys.exit(f"unknown command {c}")
