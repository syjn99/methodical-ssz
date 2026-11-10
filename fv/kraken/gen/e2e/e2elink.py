#!/usr/bin/env python3
"""prysm-e2e E1.2: link tables of the Checkpoint / Epoch SSZ functions in the Go 1.26.10 namespace.

Usage (Python 3 standard library only; run with python3 -I -B; the steps after `filter` are gated):
  e2elink.py filter <outdir> <objdump> <elf> <nm>   write <outdir>/target.objdump (the 7 functions of
                                                    callgraph.py) and link the ELF and nm into <outdir>
  e2elink.py data <outdir>                          after `conv.py <outdir>/target.objdump
                                                    <outdir>/p1bin-amd64.nm <outdir>/norm --norm`:
                                                    write <outdir>/data/*.data with link/data.py's code
Then `link/check.py <outdir>` (a)-(f). The committed copy is fv/kraken/prysm/go1.26.10/e2e/link
(norm/, data/, target.objdump, RESULT). link/conv.py, link/data.py and link/check.py are not changed.

Every data item is located from the converted code (the operand that the proofs read), not written by
hand: the label and offset come from the `lea`/`mov` operand of the .S, the length from the code
(`mov $n,%ebx` before the call) or from the item's Go type (abi.Type 48 bytes, itab 32 bytes).
"""
import importlib.util
import os
import pathlib
import re
import sys

HERE = pathlib.Path(__file__).resolve().parent
LINK = HERE.parent.parent / "link"
sys.path.insert(0, str(HERE))
import callgraph  # noqa: E402

CP = "github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Checkpoint"
EP = "github.com_OffchainLabs_prysm_v7_consensus_types_primitives.Epoch"


def filt(outdir, objdump, elf, nm):
    out = pathlib.Path(outdir)
    out.mkdir(parents=True, exist_ok=True)
    want, keep, cur, seen = set(callgraph.FUNCS), [], False, set()
    for line in open(objdump):
        if line.startswith("TEXT "):
            name = line.split()[1].removesuffix("(SB)")
            cur = name in want
            if cur:
                seen.add(name)
        if cur:
            keep.append(line)
    (out / "target.objdump").write_text("".join(keep))
    for src, dst in ((elf, "p1bin-amd64"), (nm, "p1bin-amd64.nm")):
        p = out / dst
        if not p.is_symlink() and not p.exists():
            os.symlink(src, p)
    missing = sorted(want - seen)
    print(f"functions {len(seen)} missing {missing}")
    return 1 if missing else 0


def ins(outdir, fn):
    return [l.strip() for l in (pathlib.Path(outdir) / "norm" / f"{fn}.S").read_text().split("\n")]


def operand(lines, pat):
    """(label, offset) of the unique instruction matching pat (groups: label, offset or None)."""
    ms = [re.fullmatch(pat, l) for l in lines]
    ms = [m for m in ms if m]
    assert len(ms) >= 1, pat
    labs = {(m[1], int(m[2]) if m[2] else 0) for m in ms}
    assert len(labs) == 1, (pat, labs)
    return labs.pop()


def items(outdir):
    spec = importlib.util.spec_from_file_location("data", LINK / "data.py")
    data = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(data)
    cu, cm, eu = ins(outdir, f"{CP}.UnmarshalSSZ"), ins(outdir, f"{CP}.MarshalSSZTo"), ins(outdir, f"{EP}.UnmarshalSSZ")
    lea = r"lea ([A-Za-z0-9_.]+)(?:\+(\d+))?\(%rip\),%{}"
    # uint8 element type of makeslice (decoder) and growslice (encoder): one word in both
    mk = cu.index("callq runtime.makeslice")
    u8 = operand([cu[mk - 3]], lea.format("rax"))
    gs = operand(cm, lea.format("rsi"))
    assert u8 == gs, (u8, gs)
    # "Epoch: %w": lea go_string... then mov $len,%ebx before fmt.errorf (decoder)
    fe = cu.index("callq fmt.errorf")
    cpfmt = operand([cu[fe - 5]], lea.format("rax"))
    cpfmt_n = int(re.fullmatch(r"mov \$0x([0-9a-f]+),%ebx", cu[fe - 4])[1], 16)
    nobj = cu.index("callq runtime.newobject")
    estype = operand([cu[nobj - 1]], lea.format("rax"))
    itab = operand(cu, r"lea (go_itab[A-Za-z0-9_.]+)(?:\+(\d+))?\(%rip\),%rax")
    errsize = operand(cu, r"mov ([A-Za-z0-9_.]+)\(%rip\),%rax()")
    errbl = operand(cm, r"mov ([A-Za-z0-9_.]+)\(%rip\),%rdi()")
    # Epoch reject: args [type:int, &8, type:int, box]; format lea + mov $0x28,%ebx before fmt.errorf
    ef = eu.index("callq fmt.errorf")
    epfmt = operand([eu[ef - 5]], lea.format("rax"))
    epfmt_n = int(re.fullmatch(r"mov \$0x([0-9a-f]+),%ebx", eu[ef - 4])[1], 16)
    ldx = [operand([l], lea.format("rdx")) for l in eu if re.fullmatch(lea.format("rdx"), l)]
    lcx = [operand([l], lea.format("rcx")) for l in eu if re.fullmatch(lea.format("rcx"), l)]
    inttype, eight = ldx[0], ldx[1]
    assert lcx[0] == inttype, (lcx, inttype)
    T = data.ABI_TYPE_WORDS
    its = [
        ("e2eU8Type", u8[0], u8[1], 48, T),
        ("e2eCpFmtW", cpfmt[0], cpfmt[1], cpfmt_n, []),
        ("e2eErrStrType", estype[0], estype[1], 48, T),
        ("e2eErrorStringItab", itab[0], itab[1], 32, [0, 8, 24]),
        ("e2eErrSize", errsize[0], 0, 0, []),
        ("e2eErrBytesLength", errbl[0], 0, 0, []),
        ("e2eEpFmt", epfmt[0], epfmt[1], epfmt_n, []),
        ("e2eIntType", inttype[0], inttype[1], 48, T),
        ("e2eEight", eight[0], eight[1], 8, []),
        ("e2eStaticuint64s", "runtime.staticuint64s", 0, 2048, []),
    ]
    return data, its


def write_data(outdir):
    data, its = items(outdir)
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
        sys.exit(write_data(sys.argv[2]))
    sys.exit(f"unknown command {c}")
