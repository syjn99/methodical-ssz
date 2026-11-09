#!/usr/bin/env python3
"""ELF data include: write the bytes that the proofs read as data files.

Usage: data.py <outdir>      (outdir = fv/kraken/link/out, after build.sh)

For every item of ITEMS, reads `length` bytes of p1bin-amd64 at the item's
label + offset and writes <outdir>/data/<id>.data (format in TOOLS.md):

    at <label> <off>          the item's address (label = conv.py's clean name)
    bytes <hh> <hh> ...       raw bytes (at most 16 per line)
    word <label> <off>        an 8-byte little-endian pointer = label + off

The 8-byte slots listed in `words` are pointers in Go's data (itab and type
descriptor fields); they are written as `word` with the nearest symbol at or
below the pointer value, so the Lean term is `label + off` in every Host.
`fv/kraken/lean/Fk/Include.lean` (`data_include`) reads these files;
`link/check.py` compares them with the ELF again. Item table: the address and
length are what the code uses (`lea go_string._+526(%rip)`, `mov $0x5,%ebx`);
the bytes are what the ELF has there.
"""
import importlib.util
import pathlib
import re
import struct
import sys

HERE = pathlib.Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location("conv", HERE / "conv.py")
conv = importlib.util.module_from_spec(spec)
spec.loader.exec_module(conv)

ABI_TYPE_WORDS = [24, 32]  # abi.Type: Equal func, GCData
# (id, label, offset, length, pointer slots)
ITEMS = [
    ("blFmtB", "go_string._", 526, 5, []),
    ("bvFmtJ", "go_string._", 511, 5, []),
    ("vbvFmt", "go_string._", 27706, 35, []),
    ("lcFmtZero", "go_string._", 39370, 53, []),
    ("lcFmtShort", "go_string._", 42000, 63, []),
    ("lcFmtOrder", "go_string._", 42579, 67, []),
    ("vblMsgE", "go_string._", 33605, 42, []),
    ("vblMsgZ", "go_string._", 13272, 21, []),
    ("vblMsgB", "go_string._", 5743, 13, []),
    ("luFmtTooBig", "go_string._", 40290, 56, []),
    ("luFmtMis", "go_string._", 42646, 68, []),
    # itab: inter, Type, Hash (+4 pad), Fun[0]
    ("errorStringItab", "go_itab._errors.errorString_error", 0, 32, [0, 8, 24]),
    # abi.PtrType of *errors.errorString: abi.Type (48) + Elem
    ("errorStringPtrType", "type__", 68096, 56, ABI_TYPE_WORDS + [48]),
    ("intType", "type__", 49184, 48, ABI_TYPE_WORDS),
    ("uint64Type", "type__", 49120, 48, ABI_TYPE_WORDS),
    ("staticuint64s", "runtime.staticuint64s", 0, 2048, []),
    # error globals: address only (their values are set by the runtime's init)
    ("ErrSize", "ssz.ErrSize", 0, 0, []),
    ("ErrInvalidSerialization", "ssz.ErrInvalidSerialization", 0, 0, []),
    ("ErrInvalidVariableOffset", "ssz.ErrInvalidVariableOffset", 0, 0, []),
    ("ErrListTooBig", "ssz.ErrListTooBig", 0, 0, []),
    ("ErrBytesLength", "ssz.ErrBytesLength", 0, 0, []),
    ("ErrIncorrectListSize", "ssz.ErrIncorrectListSize", 0, 0, []),
]


def read_elf(path):
    """(file bytes, PROGBITS sections [(addr, off, size)])."""
    b = pathlib.Path(path).read_bytes()
    assert b[:6] == b"\x7fELF\x02\x01", "not an ELF64 LSB file"
    shoff, = struct.unpack_from("<Q", b, 0x28)
    shentsize, shnum = struct.unpack_from("<HH", b, 0x3A)
    secs = []
    for i in range(shnum):
        _, typ, _, addr, off, size = struct.unpack_from("<IIQQQQ", b, shoff + i * shentsize)
        if typ == 1:
            secs.append((addr, off, size))
    return b, secs


def elf_bytes(b, secs, addr, n):
    for a, o, s in secs:
        if a <= addr and addr + n <= a + s:
            return b[o + addr - a:o + addr - a + n]
    raise SystemExit(f"no file bytes at {addr:#x}+{n}")


def clean(name):
    """conv.clean without its collision table (check.py's `rev` uses the same map)."""
    o = name.replace(conv.MOD + "fv/kraken/", "").replace(conv.MOD, "")
    return re.sub(r"[^A-Za-z0-9_.]", "_", re.sub(r"\(\*(\w+)\)", r"\1", o))


def symbols(nm):
    """clean name -> {(address, size, original name)}."""
    by = {}
    for a, sz, name in nm:
        by.setdefault(clean(name), set()).add((a, sz, name))
    return by


def main(outdir):
    outdir = pathlib.Path(outdir)
    b, secs = read_elf(outdir / "p1bin-amd64")
    nm = conv.read_nm(outdir / "p1bin-amd64.nm")
    by = symbols(nm)
    used = set(re.findall(r"[A-Za-z0-9_.]+", (outdir / "norm" / "all.S").read_text()))

    def addr(label):
        s = by.get(label, set())
        assert len({a for a, _, _ in s}) == 1, f"label {label}: {sorted(s)}"
        return next(iter(s))[0]

    def near(v):
        """(label, off) for a pointer value: the symbol with the greatest address
        <= v; among several there, a label that the converted code uses (all.S),
        then one of nonzero size that contains v, then the first clean name.
        The label must name one address."""
        best = max(a for a, _, _ in nm if a <= v)
        cands = sorted((clean(n) not in used, sz == 0 or not (a <= v < a + sz), clean(n))
                       for a, sz, n in nm if a == best)
        lab = cands[0][2]
        assert addr(lab) == best
        return lab, v - best

    d = outdir / "data"
    d.mkdir(exist_ok=True)
    for old in d.glob("*.data"):
        old.unlink()
    for ident, label, off, n, words in ITEMS:
        a = addr(label) + off
        bs = elf_bytes(b, secs, a, n) if n else b""
        lines = [f"# {ident}: link/data.py, p1bin-amd64 bytes [{a:#x}, {a + n:#x})"]
        if label == "go_string._":
            lines.append(f"# text {bs.decode()!r}")
        lines.append(f"at {label} {off}")
        i, raw = 0, []

        def flush():
            for k in range(0, len(raw), 16):
                lines.append("bytes " + " ".join(f"{x:02x}" for x in raw[k:k + 16]))
            raw.clear()
        while i < n:
            if i in words:
                flush()
                v, = struct.unpack_from("<Q", bs, i)
                lab, o = near(v)
                lines.append(f"word {lab} {o}")
                i += 8
            else:
                raw.append(bs[i])
                i += 1
        flush()
        (d / f"{ident}.data").write_text("\n".join(lines) + "\n")
        print(f"{ident}: {label}+{off} = {a:#x}, {n} bytes, {len(words)} words")


if __name__ == "__main__":
    main(sys.argv[1])
