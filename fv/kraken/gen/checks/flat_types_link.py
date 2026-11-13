#!/usr/bin/env python3
"""Call graph and link tables of the real UnmarshalSSZ and MarshalSSZTo of the 24 flat fixed-size
types outside the development population (fv/kraken/prysm/proof-inventory.md at the freeze of the 24 flat types) on the Go 1.26.10
ELF (the same ELF as prysm/go1.26.10/link-set; written after the hold-out of the 24 flat types had been run;
the text of `seven_flat_decoders_link.py` + `flat_encoders_link.py` with the function set changed and the data items made per function).

Usage (Python 3 standard library only; python3 -I -B; every step runs gated):
  flat_types_link.py callgraph <objdump> <out.json>          call targets with contract class
  flat_types_link.py filter <outdir> <objdump> <elf> <nm>    <outdir>/target.objdump of FUNCS (+ ELF/nm links)
  flat_types_link.py data <outdir> <checkpoint-link-dir> <attestation-data-link-dir> <eth1-data-link-dir>
                                                     after `convert_objdump.py <outdir>/target.objdump
                                                     <outdir>/p1bin-amd64.nm <outdir>/norm --norm`:
                                                     write <outdir>/data/*.data (link/data.py's code)
Then `link/check.py <outdir>` (a)-(f). Committed copy: prysm/go1.26.10/link-set.
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
import checkpoint_and_epoch_link  # noqa: E402
import attestation_data_link  # noqa: E402

PRIM = "github.com/OffchainLabs/prysm/v7/consensus-types/primitives"
PKG = {"v1": "github.com/OffchainLabs/prysm/v7/proto/engine/v1",
       "v1alpha1": "github.com/OffchainLabs/prysm/v7/proto/prysm/v1alpha1"}
SPKG = {k: v.replace("/", "_").replace("github.com_", "github.com_") for k, v in PKG.items()}
TYPES = [("v1", "BuilderDepositRequest"), ("v1", "BuilderExitRequest"),
         ("v1", "ConsolidationRequest"), ("v1", "DepositRequest"), ("v1", "Withdrawal"),
         ("v1", "WithdrawalRequest"), ("v1alpha1", "BLSToExecutionChange"),
         ("v1alpha1", "BeaconBlocksByRangeRequest"), ("v1alpha1", "BlobSidecarsByRangeRequest"),
         ("v1alpha1", "Builder"), ("v1alpha1", "BuilderPendingWithdrawal"),
         ("v1alpha1", "BuilderPreferences"), ("v1alpha1", "ENRForkID"),
         ("v1alpha1", "ExecutionPayloadEnvelopesByRangeRequest"), ("v1alpha1", "Fork"),
         ("v1alpha1", "ForkData"), ("v1alpha1", "PartialDataColumnGroupID"),
         ("v1alpha1", "PayloadAttestationData"), ("v1alpha1", "ProposerPreferences"),
         ("v1alpha1", "Status"), ("v1alpha1", "StatusV2"), ("v1alpha1", "Validator"),
         ("v1alpha1", "ValidatorIdentity"), ("v1alpha1", "ValidatorRegistrationV1")]
DEC = [f"{PKG[k]}.(*{t}).UnmarshalSSZ" for k, t in TYPES]
ENC = [f"{PKG[k]}.(*{t}).MarshalSSZTo" for k, t in TYPES]
FUNCS = DEC + ENC
SCOPE = {f: "in (24 flat types, decoder)" for f in DEC} | {f: "in (24 flat types, encoder)" for f in ENC}
CLASS = dict(attestation_data_link.CLASS)
CLASS.update({
    f"{PRIM}.(*ValidatorIndex).UnmarshalSSZ": ("a", "function spec Prysm.ValidatorIndex.Decode.accept_function_spec, proved from machine code (BeaconBlockHeader hold-out)"),
    f"{PRIM}.(*Slot).UnmarshalSSZ": ("a", "function spec Prysm.Slot.Decode.accept_function_spec, proved from machine code (Prysm/Slot/)"),
    f"{PRIM}.(*Epoch).UnmarshalSSZ": ("a", "function spec Prysm.Epoch.Decode.accept_function_spec, proved from machine code (Prysm/Epoch/)"),
    "fmt.errorf": ("b", "FmtErrorfWrapContract (field wraps of the callee errors); decoder: unreachable under the callee specs"),
    "runtime.newobject": ("b", "NewobjectContract errorString (after fmt.errorf: nil-result branch, excluded by rax != 0)"),
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
                               "how": c[1] if c else "no contract in the tree; recorded only (link of the 24 flat types)"})
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
    checkpoint_and_epoch_link.callgraph.FUNCS = FUNCS
    return checkpoint_and_epoch_link.filt(outdir, objdump, elf, nm)


def items(outdir, checkpoint_dir, attestation_data_dir, eth1_data_dir):
    """Per decoder: every address-only error global loaded into rax (`sszErrSize` for ssz.ErrSize, else the id
    of its symbol by `link/data.py` `item_id`, length 0) and the format
    strings of its fmt.errorf wraps (`format<Field>`, in code order). Per encoder: the address-only
    `sszErrBytesLength` when its code loads it. Every makeslice / growslice is checked for the uint8 type word of
    the Checkpoint set (`type__+387072`) and the result is printed per function (no assertion: a type whose
    literal differs is a fact for Part 1, not a link failure). ssz.ErrSize / ssz.ErrBytesLength / writeBarrier /
    errorString are asserted equal to the Checkpoint / AttestationData / Eth1Data operands where present."""
    spec = importlib.util.spec_from_file_location("data", LINK / "data.py")
    data = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(data)
    V = "github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1"
    cu = checkpoint_and_epoch_link.ins(checkpoint_dir, f"{checkpoint_and_epoch_link.CHECKPOINT_SYMBOL}.UnmarshalSSZ")
    cm = checkpoint_and_epoch_link.ins(checkpoint_dir, f"{checkpoint_and_epoch_link.CHECKPOINT_SYMBOL}.MarshalSSZTo")
    au = checkpoint_and_epoch_link.ins(attestation_data_dir, f"{V}.AttestationData.UnmarshalSSZ")
    em = checkpoint_and_epoch_link.ins(eth1_data_dir, f"{V}.Eth1Data.MarshalSSZTo")
    lea = r"lea ([A-Za-z0-9_.]+)(?:\+(\d+))?\(%rip\),%{}"
    u8 = checkpoint_and_epoch_link.operand([cu[cu.index("callq runtime.makeslice") - 3]], lea.format("rax"))
    assert u8 == ("type__", 387072), u8
    wb = r"cmpl \$0x0,([A-Za-z0-9_.]+)(?:\+(\d+))?\(%rip\)"
    eszp = r"mov ([A-Za-z0-9_.]+)\(%rip\),%rax()"
    esz = checkpoint_and_epoch_link.operand(cu, eszp)
    back = attestation_data_link.back_lea
    estype = back(cu, cu.index("callq runtime.newobject"))
    ebp = r"mov ([A-Za-z0-9_.]+)\(%rip\),%rdi()"
    ebl = checkpoint_and_epoch_link.operand(cm, ebp)
    assert ebl == checkpoint_and_epoch_link.operand(em, ebp), ebl
    its = []

    def fmts(lines):
        out = []
        for i, l in enumerate(lines):
            if l == "callq fmt.errorf":
                k = next(j for j in range(i - 1, i - 8, -1) if re.fullmatch(r"mov \$0x[0-9a-f]+,%ebx", lines[j]))
                out.append((checkpoint_and_epoch_link.operand([lines[k - 1]], lea.format("rax")),
                            int(re.fullmatch(r"mov \$0x([0-9a-f]+),%ebx", lines[k])[1], 16)))
        return out

    def u8word(lines, i, reg, back_n):
        return any(checkpoint_and_epoch_link.operand([lines[j]], lea.format(reg)) == u8 for j in range(i - back_n, i)
                   if re.fullmatch(lea.format(reg), lines[j]))
    for k, t in TYPES:
        u = checkpoint_and_epoch_link.ins(outdir, sname(k, t, "UnmarshalSSZ"))
        mks = [i for i, l in enumerate(u) if l == "callq runtime.makeslice"]
        mk_u8 = [u8word(u, i, "rax", 5) for i in mks]
        assert not any(l == "callq runtime.growslice" for l in u), t
        gl = sorted({re.fullmatch(eszp, l)[1] for l in u if re.fullmatch(eszp, l)})
        for g in gl:
            if g == esz[0]:
                its.append((None, esz[0], 0, 0, []))
            else:
                its.append((None, g, 0, 0, []))
        if mks:
            assert checkpoint_and_epoch_link.operand(u, wb) == checkpoint_and_epoch_link.operand(au, wb), t
        nn = [back(u, i) for i, l in enumerate(u) if l == "callq runtime.newobject"]
        assert all(x == estype for x in nn), (t, nn, estype)
        for j, ((sym, off), n) in enumerate(fmts(u)):
            its.append((None, sym, off, n, []))
        print("dec", t, "makeslice", len(mks), "u8 literal", mk_u8, "newobject", len(nn), "fmt", len(fmts(u)),
              "error globals", gl)
        m = checkpoint_and_epoch_link.ins(outdir, sname(k, t, "MarshalSSZTo"))
        gs = [i for i, l in enumerate(m) if l == "callq runtime.growslice"]
        gs_u8 = [u8word(m, i, "rsi", 4) for i in gs]
        assert not any(l in ("callq runtime.makeslice", "callq runtime.newobject", "callq fmt.errorf")
                       for l in m), t
        has_ebl = any(re.fullmatch(ebp, l) for l in m)
        if has_ebl:
            assert checkpoint_and_epoch_link.operand(m, ebp) == ebl, t
            its.append((None, ebl[0], 0, 0, []))
        print("enc", t, "growslice", len(gs), "u8 literal", gs_u8, "ErrBytesLength", has_ebl)
    return data, its


def write_data(outdir, checkpoint_dir, attestation_data_dir, eth1_data_dir):
    data, its = items(outdir, checkpoint_dir, attestation_data_dir, eth1_data_dir)
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
