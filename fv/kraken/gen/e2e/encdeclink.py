#!/usr/bin/env python3
"""Link set of the real v1alpha1.DataColumnsByRootIdentifier.UnmarshalSSZ (Go 1.26.10 ELF
c6403c02...911e). A new file in the pattern of `lvlink.py` / `enclink.py`; existing scripts are not changed.

Usage (Python 3 standard library only; python3 -I -B; the steps after `filter` are gated):
  encdeclink.py filter <outdir> <objdump> <elf> <nm>
  encdeclink.py data <outdir> <cp-linkdir> <t3-linkdir>    after conv.py --norm: write <outdir>/data/*.data
Then `link/check.py <outdir>` (a)-(f). Committed copy: prysm/go1.26.10/link-set.

Data items are located from the converted code. Items equal to an item of the Checkpoint set (`e2elink.py`) or of
the IndexedAttestation set (`lvlink.py --t3`) are asserted equal (same label and offset) and written again under the `dcd`
prefix so that check (f) binds them to the ELF in this directory; the Lean statements read the `dcd` names through
their own reader.
"""
import importlib.util
import pathlib
import re
import sys

HERE = pathlib.Path(__file__).resolve().parent
LINK = HERE.parent.parent / "link"
sys.path.insert(0, str(HERE))
import e2elink  # noqa: E402

V1A1 = "github.com/OffchainLabs/prysm/v7/proto/prysm/v1alpha1"
TARGET = f"{V1A1}.(*DataColumnsByRootIdentifier).UnmarshalSSZ"
V = "github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1"


def filt(outdir, objdump, elf, nm):
    e2elink.callgraph.FUNCS = [TARGET]
    return e2elink.filt(outdir, objdump, elf, nm)


def write_data(outdir, cpdir, t3dir):
    spec = importlib.util.spec_from_file_location("data", LINK / "data.py")
    data = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(data)
    m = e2elink.ins(outdir, f"{V}.DataColumnsByRootIdentifier.UnmarshalSSZ")
    cu = e2elink.ins(cpdir, f"{e2elink.CP}.UnmarshalSSZ")
    eu = e2elink.ins(cpdir, f"{e2elink.EP}.UnmarshalSSZ")
    lea = r"lea ([A-Za-z0-9_.]+)(?:\+(\d+))?\(%rip\),%{}"
    calls = sorted({l for l in m if l.startswith("callq ")})
    assert calls == ["callq fmt.errorf", "callq runtime.convT64", "callq runtime.gcWriteBarrier2",
                     "callq runtime.makeslice", "callq runtime.memmove", "callq runtime.morestack_noctxt.abi0",
                     "callq runtime.newobject", "callq runtime.panicBounds"], calls
    # makeslice type words: uint8 (BlockRoot, cap 32) then uint64 (Columns)
    mk = [i for i, l in enumerate(m) if l == "callq runtime.makeslice"]
    tys = [e2elink.operand([m[j]], lea.format("rax")) for i in mk for j in range(i - 5, i)
           if re.fullmatch(lea.format("rax"), m[j])]
    u8 = e2elink.operand([cu[cu.index("callq runtime.makeslice") - 3]], lea.format("rax"))
    t3 = pathlib.Path(t3dir) / "data"
    assert tys[0] == u8 and len(tys) == 2, tys
    assert f"\nat {tys[1][0]} {tys[1][1]}\n" in (t3 / "lvU64Type.data").read_text(), tys
    # convT64 type word = type:int of the Epoch decoder
    inttype = [e2elink.operand([l], lea.format("rdx")) for l in eu if re.fullmatch(lea.format("rdx"), l)][0]
    cv = [i for i, l in enumerate(m) if l == "callq runtime.convT64"]
    assert len(cv) == 2
    for i in cv:
        assert e2elink.operand([m[i + 1]], lea.format("rcx")) == inttype, ("type:int", i)
    itab = e2elink.operand(cu, r"lea (go_itab[A-Za-z0-9_.]+)(?:\+(\d+))?\(%rip\),%rax")
    assert e2elink.operand(m, r"lea (go_itab[A-Za-z0-9_.]+)(?:\+(\d+))?\(%rip\),%rax") == itab
    # the two formats: lea go_string... ,%rax; mov $len,%ebx; ... callq fmt.errorf (code order: too big, misaligned)
    fm = []
    for i, l in enumerate(m):
        if l == "callq fmt.errorf":
            k = next(j for j in range(i - 1, i - 8, -1) if re.fullmatch(r"mov \$0x[0-9a-f]+,%ebx", m[j]))
            fm.append((e2elink.operand([m[k - 1]], lea.format("rax")),
                       int(re.fullmatch(r"mov \$0x([0-9a-f]+),%ebx", m[k])[1], 16)))
    assert [n for _, n in fm] == [0x3f, 0x4a], fm
    errs = {}
    for g in ("ErrSize", "ErrInvalidVariableOffset", "ErrIncorrectListSize", "ErrListTooBig"):
        assert any(re.fullmatch(rf"mov ssz\.{g}\(%rip\),%r[a-z]+", l) for l in m), g
        errs[g] = f"ssz.{g}"
    T = data.ABI_TYPE_WORDS
    its = [("dcdU8Type", tys[0][0], tys[0][1], 48, T), ("dcdU64Type", tys[1][0], tys[1][1], 48, T),
           ("dcdIntType", inttype[0], inttype[1], 48, T),
           ("dcdFmtTooBig", fm[0][0][0], fm[0][0][1], fm[0][1], []),
           ("dcdFmtMis", fm[1][0][0], fm[1][0][1], fm[1][1], [])]
    its += [(f"dcd{g}", lab, 0, 0, []) for g, lab in errs.items()]
    for it in its:
        print("item", it[:4])
    data.ITEMS = its
    data.main(pathlib.Path(outdir))
    return 0


if __name__ == "__main__":
    c = sys.argv[1]
    if c == "filter":
        sys.exit(filt(*sys.argv[2:6]))
    if c == "data":
        sys.exit(write_data(*sys.argv[2:5]))
    sys.exit(f"unknown command {c}")
