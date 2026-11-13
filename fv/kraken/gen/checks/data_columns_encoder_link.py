#!/usr/bin/env python3
"""Call graph and link set of the real v1alpha1.DataColumnsByRootIdentifier.MarshalSSZTo on the
Go 1.26.10 ELF (sha256 c6403c02...911e), the first variable-length encoder hand proof (selected: one variable-length field, a uint64 list, and no call to
another generated method).
A new file in the pattern of `lists_and_vectors_link.py`. Existing scripts are not changed.

Usage (Python 3 standard library only; python3 -I -B; the steps after `filter` are gated):
  data_columns_encoder_link.py callgraph <objdump> <out.json>      call targets of the candidates with contract class
  data_columns_encoder_link.py filter <outdir> <objdump> <elf> <nm> <outdir>/target.objdump of the target (+ ELF/nm links)
  data_columns_encoder_link.py data <outdir> <checkpoint-link-dir> <indexed-attestation-link-dir>
                                                 after `convert_objdump.py <outdir>/target.objdump
                                                 <outdir>/p1bin-amd64.nm <outdir>/norm --norm`:
                                                 write <outdir>/data/*.data (link/data.py's code)
Then `link/check.py <outdir>` (a)-(f). Committed copy: prysm/go1.26.10/link-set.

Data items are located from the converted code. The Lean statements use the existing names
`ElfData.PrysmTarget.typeUint8_addr`, `ElfData.PrysmTarget.sszErrBytesLength_addr` and `ElfData.PrysmTarget.sszErrListTooBig_addr`;
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
import checkpoint_and_epoch_link  # noqa: E402
import lists_and_vectors_link  # noqa: E402

V1A1 = "github.com/OffchainLabs/prysm/v7/proto/prysm/v1alpha1"
TARGET = f"{V1A1}.(*DataColumnsByRootIdentifier).MarshalSSZTo"
# candidates read for the selection (DataColumnSidecarsByRangeRequest: reserve, same form; IndexedAttestation:
# excluded, it calls AttestationData.MarshalSSZTo); only TARGET is linked
CANDS = [TARGET, f"{V1A1}.(*DataColumnSidecarsByRangeRequest).MarshalSSZTo",
         f"{V1A1}.(*IndexedAttestation).MarshalSSZTo"]
CLASS = dict(lists_and_vectors_link.CLASS)
CLASS.update({
    "runtime.growslice": ("b", "GrowsliceContract Heap typeUint8_addr 1 S (esz 1; num 32, 4, 8)"),
    "runtime.memmove": ("b", "MemmoveContract S (n = 32)"),
    "runtime.morestack_noctxt.abi0": ("c", "premise guard < rsp - 8"),
    f"{V1A1}.(*AttestationData).MarshalSSZTo": ("FORBIDDEN", "forbidden target (task brief)"),
})


def callgraph(objdump, out):
    lists_and_vectors_link.FUNCS[:] = CANDS
    lists_and_vectors_link.SCOPE.clear()
    lists_and_vectors_link.SCOPE.update({CANDS[0]: "in (ENC target)", CANDS[1]: "candidate (not selected)",
                         CANDS[2]: "excluded (calls AttestationData.MarshalSSZTo)"})
    lists_and_vectors_link.CLASS.clear()
    lists_and_vectors_link.CLASS.update(CLASS)
    return lists_and_vectors_link.callgraph(objdump, out)


def filt(outdir, objdump, elf, nm):
    checkpoint_and_epoch_link.callgraph.FUNCS = [TARGET]
    return checkpoint_and_epoch_link.filt(outdir, objdump, elf, nm)


def write_data(outdir, checkpoint_dir, indexed_attestation_dir):
    spec = importlib.util.spec_from_file_location("data", LINK / "data.py")
    data = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(data)
    V = "github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1"
    m = checkpoint_and_epoch_link.ins(outdir, f"{V}.DataColumnsByRootIdentifier.MarshalSSZTo")
    cm = checkpoint_and_epoch_link.ins(checkpoint_dir, f"{checkpoint_and_epoch_link.CHECKPOINT_SYMBOL}.MarshalSSZTo")
    lea = r"lea ([A-Za-z0-9_.]+)(?:\+(\d+))?\(%rip\),%rsi"
    gs = [i for i, l in enumerate(m) if l == "callq runtime.growslice"]
    assert len(gs) == 3, gs
    u8 = checkpoint_and_epoch_link.operand(m, lea)  # one operand for all three sites (operand() asserts uniqueness)
    assert u8 == checkpoint_and_epoch_link.operand(cm, lea), u8
    assert sum(l == "callq runtime.memmove" for l in m) == 1
    calls = sorted({l for l in m if l.startswith("callq ")})
    assert calls == ["callq runtime.growslice", "callq runtime.memmove", "callq runtime.morestack_noctxt.abi0"], calls
    errbl = checkpoint_and_epoch_link.operand(m, r"mov (ssz\.ErrBytesLength)\(%rip\),%rdi()")
    assert errbl == checkpoint_and_epoch_link.operand(cm, r"mov ([A-Za-z0-9_.]+)\(%rip\),%rdi()"), errbl
    errtb = checkpoint_and_epoch_link.operand(m, r"mov (ssz\.ErrListTooBig)\(%rip\),%rdi()")
    with_indexed_attestation = (pathlib.Path(indexed_attestation_dir) / "data" / "sszErrListTooBig.data").read_text()
    assert f"\nat {errtb[0]} 0\n" in with_indexed_attestation, with_indexed_attestation
    its = [("typeUint8", u8[0], u8[1], 48, data.ABI_TYPE_WORDS),
           (None, errbl[0], 0, 0, []),
           (None, errtb[0], 0, 0, [])]
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
