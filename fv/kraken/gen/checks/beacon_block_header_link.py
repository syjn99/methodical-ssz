#!/usr/bin/env python3
"""Call graph and link tables of the real v1alpha1.BeaconBlockHeader SSZ functions and the
primitives.ValidatorIndex methods on the Go 1.26.10 ELF (the same ELF as prysm/go1.26.10/link-set; BeaconBlockHeader
and ValidatorIndex are hold-out types; the text of `attestation_data_link.py` with the function set changed).

Usage (Python 3 standard library only; python3 -I -B; the steps after `filter` are gated):
  beacon_block_header_link.py callgraph <objdump> <out.json>          call targets with contract class
  beacon_block_header_link.py filter <outdir> <objdump> <elf> <nm>    <outdir>/target.objdump of FUNCS (+ ELF/nm links)
  beacon_block_header_link.py data <outdir> <checkpoint-link-dir> <attestation-data-link-dir> after `convert_objdump.py <outdir>/target.objdump
                                                    <outdir>/p1bin-amd64.nm <outdir>/norm --norm`:
                                                    write <outdir>/data/*.data (link/data.py's code)
Then `link/check.py <outdir>` (a)-(f). Committed copy: prysm/go1.26.10/link-set.
SizeSSZ is not in the set (excluded from the hold-out claim). The Slot callee is `Prysm.Slot.Code.unmarshalSSZ`
(its code is in prysm/go1.26.10/link-set); the shared items (uint8 type word, ssz.ErrSize, the
errorString type, writeBarrier) are asserted equal to the Checkpoint / AttestationData sets' operands.
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
V1A1 = "github.com/OffchainLabs/prysm/v7/proto/prysm/v1alpha1"
FUNCS = [f"{V1A1}.(*BeaconBlockHeader).MarshalSSZTo", f"{V1A1}.(*BeaconBlockHeader).UnmarshalSSZ",
         f"{PRIM}.(*ValidatorIndex).UnmarshalSSZ", f"{PRIM}.(*ValidatorIndex).MarshalSSZTo"]
SCOPE = {FUNCS[0]: "in (hold-out encoder fast path)", FUNCS[1]: "in (hold-out decoder)", FUNCS[2]: "in (hold-out uint64 callee)",
         FUNCS[3]: "record only (inlined into BeaconBlockHeader.MarshalSSZTo or unused)"}
CLASS = dict(attestation_data_link.CLASS)
CLASS.update({
    f"{PRIM}.(*ValidatorIndex).UnmarshalSSZ": ("a", "function spec Prysm.ValidatorIndex.Decode.accept_function_spec, proved from machine code (the uint64 decoder proof)"),
    "fmt.errorf": ("b", "FmtErrorfWrapContract (field wraps 'Slot: %w', 'ProposerIndex: %w'); decoder: unreachable under "
                        "the callee specs; ValidatorIndex length reject (not in the hold-out)"),
    "runtime.newobject": ("b", "NewobjectContract errorString (after fmt.errorf: nil-result branch, excluded by rax != 0)"),
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
    asm = {"BeaconBlockHeader.MarshalSSZTo calls a Slot/ValidatorIndex method": any(
        "Slot" in c["target"] or "ValidatorIndex" in c["target"] for c in res[FUNCS[0]]["calls"])}
    doc = {"functions": res, "call_counts": counts, "asm_inlining": asm, "unclassified_in_scope": unc,
           "missing": missing}
    json.dump(doc, open(out, "w"), indent=1)
    for f in FUNCS:
        print(f"{f.split('/')[-1]:58} {res[f]['instructions']:4} instr  {counts[f]}")
    print("asm", asm, "unclassified", unc, "missing", missing)
    return 1 if (missing or unc) else 0


def filt(outdir, objdump, elf, nm):
    checkpoint_and_epoch_link.callgraph.FUNCS = FUNCS
    return checkpoint_and_epoch_link.filt(outdir, objdump, elf, nm)


def items(outdir, checkpoint_dir, attestation_data_dir):
    spec = importlib.util.spec_from_file_location("data", LINK / "data.py")
    data = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(data)
    BEACON_BLOCK_HEADER = "github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockHeader"
    du, dm = checkpoint_and_epoch_link.ins(outdir, f"{BEACON_BLOCK_HEADER}.UnmarshalSSZ"), checkpoint_and_epoch_link.ins(outdir, f"{BEACON_BLOCK_HEADER}.MarshalSSZTo")
    cu, cm = checkpoint_and_epoch_link.ins(checkpoint_dir, f"{checkpoint_and_epoch_link.CHECKPOINT_SYMBOL}.UnmarshalSSZ"), checkpoint_and_epoch_link.ins(checkpoint_dir, f"{checkpoint_and_epoch_link.CHECKPOINT_SYMBOL}.MarshalSSZTo")
    au = checkpoint_and_epoch_link.ins(attestation_data_dir, "github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttestationData.UnmarshalSSZ")
    lea = r"lea ([A-Za-z0-9_.]+)(?:\+(\d+))?\(%rip\),%{}"
    back = attestation_data_link.back_lea
    # shared with the Checkpoint set: asserted equal, not written again
    u8 = checkpoint_and_epoch_link.operand([cu[cu.index("callq runtime.makeslice") - 3]], lea.format("rax"))
    mks = [i for i, l in enumerate(du) if l == "callq runtime.makeslice"]
    assert len(mks) == 3
    for i in mks:
        assert any(checkpoint_and_epoch_link.operand([du[j]], lea.format("rax")) == u8 for j in range(i - 4, i)
                   if re.fullmatch(lea.format("rax"), du[j])), ("u8 word", i)
    assert checkpoint_and_epoch_link.operand(dm, lea.format("rsi")) == u8
    # ssz.ErrSize (decoder) and ssz.ErrBytesLength (encoder) operands = the Checkpoint set's
    assert checkpoint_and_epoch_link.operand(du, r"mov ([A-Za-z0-9_.]+)\(%rip\),%rax()") == \
        checkpoint_and_epoch_link.operand(cu, r"mov ([A-Za-z0-9_.]+)\(%rip\),%rax()")
    assert checkpoint_and_epoch_link.operand(dm, r"mov ([A-Za-z0-9_.]+)\(%rip\),%rdi()") == \
        checkpoint_and_epoch_link.operand(cm, r"mov ([A-Za-z0-9_.]+)\(%rip\),%rdi()")
    # writeBarrier flag operand = the AttestationData decoder's
    wb = r"cmpl \$0x0,([A-Za-z0-9_.]+)(?:\+(\d+))?\(%rip\)"
    assert checkpoint_and_epoch_link.operand(du, wb) == checkpoint_and_epoch_link.operand(au, wb)
    estype = back(cu, cu.index("callq runtime.newobject"))
    dn = [back(du, i) for i, l in enumerate(du) if l == "callq runtime.newobject"]
    assert dn == [estype, estype], (dn, estype)

    def fmts(lines):
        out = []
        for i, l in enumerate(lines):
            if l == "callq fmt.errorf":
                k = next(j for j in range(i - 1, i - 8, -1) if re.fullmatch(r"mov \$0x[0-9a-f]+,%ebx", lines[j]))
                out.append((checkpoint_and_epoch_link.operand([lines[k - 1]], lea.format("rax")),
                            int(re.fullmatch(r"mov \$0x([0-9a-f]+),%ebx", lines[k])[1], 16)))
        return out
    df = fmts(du)
    assert [n for _, n in df] == [8, 17], df  # "Slot: %w", "ProposerIndex: %w"
    its = [
        (None, df[0][0][0], df[0][0][1], df[0][1], []),
        (None, df[1][0][0], df[1][0][1], df[1][1], []),
    ]
    return data, its


def write_data(outdir, checkpoint_dir, attestation_data_dir):
    data, its = items(outdir, checkpoint_dir, attestation_data_dir)
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
