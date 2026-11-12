#!/usr/bin/env python3
"""Call graph and link set of the real v1alpha1.DataColumnsByRootIdentifier.MarshalSSZTo on the
Go 1.26.10 ELF (sha256 c6403c02...911e), the first variable-length encoder hand proof (selected: one variable-length field, a uint64 list, and no call to
another generated method).
A new file in the pattern of `lvlink.py`. Existing scripts are not changed.

Usage (Python 3 standard library only; python3 -I -B; the steps after `filter` are gated):
  enclink.py callgraph <objdump> <out.json>      call targets of the candidates with contract class
  enclink.py filter <outdir> <objdump> <elf> <nm> <outdir>/target.objdump of the target (+ ELF/nm links)
  enclink.py data <outdir> <cp-linkdir> <t3-linkdir>
                                                 after `conv.py <outdir>/target.objdump
                                                 <outdir>/p1bin-amd64.nm <outdir>/norm --norm`:
                                                 write <outdir>/data/*.data (link/data.py's code)
Then `link/check.py <outdir>` (a)-(f). Committed copy: prysm/go1.26.10/e2e/lv/link-enc.

Data items are located from the converted code. The Lean statements use the existing names
`E2e.Data.e2eU8Type_addr`, `E2e.Data.e2eErrBytesLength_addr` and `E2eList.Data.lvErrListTooBig_addr`;
`data` asserts that the operands of this .S are those items (same label and offset) and writes the
items again under the `enc` prefix so that check (f) binds them to the ELF in this directory.
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
import lvlink  # noqa: E402

V1A1 = "github.com/OffchainLabs/prysm/v7/proto/prysm/v1alpha1"
TARGET = f"{V1A1}.(*DataColumnsByRootIdentifier).MarshalSSZTo"
# candidates read for the selection (DataColumnSidecarsByRangeRequest: reserve, same form; IndexedAttestation:
# excluded, it calls AttestationData.MarshalSSZTo); only TARGET is linked
CANDS = [TARGET, f"{V1A1}.(*DataColumnSidecarsByRangeRequest).MarshalSSZTo",
         f"{V1A1}.(*IndexedAttestation).MarshalSSZTo"]
CLASS = dict(lvlink.CLASS)
CLASS.update({
    "runtime.growslice": ("b", "GrowsliceC Heap e2eU8Type_addr 1 S (esz 1; num 32, 4, 8)"),
    "runtime.memmove": ("b", "MemmoveC S (n = 32)"),
    "runtime.morestack_noctxt.abi0": ("c", "premise guard < rsp - 8"),
    f"{V1A1}.(*AttestationData).MarshalSSZTo": ("FORBIDDEN", "forbidden target (task brief)"),
})


def callgraph(objdump, out):
    lvlink.FUNCS[:] = CANDS
    lvlink.SCOPE.clear()
    lvlink.SCOPE.update({CANDS[0]: "in (ENC target)", CANDS[1]: "candidate (not selected)",
                         CANDS[2]: "excluded (calls AttestationData.MarshalSSZTo)"})
    lvlink.CLASS.clear()
    lvlink.CLASS.update(CLASS)
    return lvlink.callgraph(objdump, out)


def filt(outdir, objdump, elf, nm):
    e2elink.callgraph.FUNCS = [TARGET]
    return e2elink.filt(outdir, objdump, elf, nm)


def write_data(outdir, cpdir, t3dir):
    spec = importlib.util.spec_from_file_location("data", LINK / "data.py")
    data = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(data)
    V = "github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1"
    m = e2elink.ins(outdir, f"{V}.DataColumnsByRootIdentifier.MarshalSSZTo")
    cm = e2elink.ins(cpdir, f"{e2elink.CP}.MarshalSSZTo")
    lea = r"lea ([A-Za-z0-9_.]+)(?:\+(\d+))?\(%rip\),%rsi"
    gs = [i for i, l in enumerate(m) if l == "callq runtime.growslice"]
    assert len(gs) == 3, gs
    u8 = e2elink.operand(m, lea)  # one operand for all three sites (operand() asserts uniqueness)
    assert u8 == e2elink.operand(cm, lea), u8
    assert sum(l == "callq runtime.memmove" for l in m) == 1
    calls = sorted({l for l in m if l.startswith("callq ")})
    assert calls == ["callq runtime.growslice", "callq runtime.memmove", "callq runtime.morestack_noctxt.abi0"], calls
    errbl = e2elink.operand(m, r"mov (ssz\.ErrBytesLength)\(%rip\),%rdi()")
    assert errbl == e2elink.operand(cm, r"mov ([A-Za-z0-9_.]+)\(%rip\),%rdi()"), errbl
    errtb = e2elink.operand(m, r"mov (ssz\.ErrListTooBig)\(%rip\),%rdi()")
    t3 = (pathlib.Path(t3dir) / "data" / "lvErrListTooBig.data").read_text()
    assert f"\nat {errtb[0]} 0\n" in t3, t3
    its = [("encU8Type", u8[0], u8[1], 48, data.ABI_TYPE_WORDS),
           ("encErrBytesLength", errbl[0], 0, 0, []),
           ("encErrListTooBig", errtb[0], 0, 0, [])]
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
