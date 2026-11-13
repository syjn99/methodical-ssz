#!/usr/bin/env python3
"""Call graph and link set of the real v1alpha1.HistoricalBatch UnmarshalSSZ on the Go 1.26.10 ELF
(the same ELF as prysm/go1.26.10/link-set, sha256 c6403c02...911e). A new file. It reuses `lists_and_vectors_link.py`, `checkpoint_and_epoch_link.py`
and `attestation_data_link.py` by import; none of them is changed.

Usage (Python 3 standard library only; python3 -I -B; the steps after `filter` are gated):
  historical_batch_link.py callgraph <objdump> <out.json>          call targets with contract class
  historical_batch_link.py filter <outdir> <objdump> <elf> <nm>    <outdir>/target.objdump of HistoricalBatch (+ ELF/nm links)
  historical_batch_link.py data <outdir> <cp-linkdir> <lv-linkdir> after `conv.py <outdir>/target.objdump
                                                    <outdir>/p1bin-amd64.nm <outdir>/norm --norm`:
                                                    write <outdir>/data/*.data (link/data.py's code)
Then `link/check.py <outdir>` (a)-(f). Committed copy: prysm/go1.26.10/link-set.

Every operand that the HistoricalBatch proofs read equals an item of an existing link set: the uint8 type word and
ssz.ErrSize (Checkpoint set, `Prysm.ElfData.PrysmTarget`) and the `[]uint8` element type word of the `[][]byte` backing array
(SyncCommittee, `ElfData.PrysmTarget.typeUint8Slice`). The script asserts these equalities. It writes the one
data file `typeUint8Slice.data` again, so that check (f) compares it with the ELF in this link set too.
"""
import json
import pathlib
import re
import sys

HERE = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import checkpoint_and_epoch_link  # noqa: E402
import lists_and_vectors_link  # noqa: E402

V1A1 = "github.com/OffchainLabs/prysm/v7/proto/prysm/v1alpha1"
FUNCS = [f"{V1A1}.(*HistoricalBatch).UnmarshalSSZ"]
V = "github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1"


def callgraph(objdump, out):
    lists_and_vectors_link.FUNCS[:] = FUNCS
    lists_and_vectors_link.SCOPE.clear()
    lists_and_vectors_link.SCOPE[FUNCS[0]] = "in (HB decoder)"
    return lists_and_vectors_link.callgraph(objdump, out)


def filt(outdir, objdump, elf, nm):
    checkpoint_and_epoch_link.callgraph.FUNCS = FUNCS
    return checkpoint_and_epoch_link.filt(outdir, objdump, elf, nm)


def write_data(outdir, cpdir, lvdir):
    import importlib.util
    spec = importlib.util.spec_from_file_location("data", lists_and_vectors_link.LINK / "data.py")
    data = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(data)
    hb = checkpoint_and_epoch_link.ins(outdir, f"{V}.HistoricalBatch.UnmarshalSSZ")
    sc = checkpoint_and_epoch_link.ins(lvdir, f"{V}.SyncCommittee.UnmarshalSSZ")
    cu = checkpoint_and_epoch_link.ins(cpdir, f"{checkpoint_and_epoch_link.CP}.UnmarshalSSZ")
    lea = r"lea ([A-Za-z0-9_.]+)(?:\+(\d+))?\(%rip\),%rax"
    u8 = checkpoint_and_epoch_link.operand([cu[cu.index("callq runtime.makeslice") - 3]], lea)
    esz = checkpoint_and_epoch_link.operand(cu, r"mov ([A-Za-z0-9_.]+)\(%rip\),%rax()")
    wb = r"cmpl \$0x0,([A-Za-z0-9_.]+)(?:\+(\d+))?\(%rip\)"

    def mk_types(lines):
        out = []
        for i, l in enumerate(lines):
            if l == "callq runtime.makeslice":
                ts = [checkpoint_and_epoch_link.operand([lines[j]], lea) for j in range(i - 5, i) if re.fullmatch(lea, lines[j])]
                assert len(ts) == 1, ("makeslice type word", i, ts)
                out.append(ts[0])
        return out
    sct = mk_types(sc)
    st = mk_types(hb)
    # BlockRoots backing array, 8192 x uint8 elements, StateRoots backing array, 8192 x uint8 elements
    assert st == [sct[0], u8, sct[0], u8], (st, sct)
    assert sum(l == "callq runtime.memmove" for l in hb) == 2
    assert sum(l == "callq runtime.panicBounds" for l in hb) == 4
    for n in ("fmt.errorf", "runtime.newobject", "runtime.growslice", "runtime.convT64"):
        assert f"callq {n}" not in hb, n
    assert checkpoint_and_epoch_link.operand(hb, r"mov ([A-Za-z0-9_.]+)\(%rip\),%rax()") == esz
    assert checkpoint_and_epoch_link.operand(hb, wb) == checkpoint_and_epoch_link.operand(sc, wb)
    its = [("typeUint8Slice", st[0][0], st[0][1], 48, data.ABI_TYPE_WORDS)]
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
