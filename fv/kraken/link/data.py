#!/usr/bin/env python3
"""ELF data include: write the bytes that the proofs read as data files.

This module has no command line. gen/checks/link_set.py sets ITEMS from the item table
prysm/go1.26.10/link-set.tsv and calls main(<link set>).

For every item of ITEMS, main reads `length` bytes of target-amd64 at the item's
label + offset and writes <link set>/data/<id>.data (format in link/README.md section 5):

    at <label> <off>          the item's address (label = convert_objdump.py's clean name)
    bytes <hh> <hh> ...       raw bytes (at most 16 per line)
    word <label> <off>        an 8-byte little-endian pointer = label + off

The 8-byte slots listed in `words` are pointers in Go's data (itab and type
descriptor fields); they are written as `word` with the nearest symbol at or
below the pointer value, so the Lean term is `label + off` in every Host.
`fv/kraken/lean/Machine/Include.lean` (`data_include`) reads these files;
`link/check.py` compares them with the ELF again. Item table: the address and
length are what the code uses (`lea go_string._+526(%rip)`, `mov $0x5,%ebx`);
the bytes are what the ELF has there.
"""
import importlib.util
import pathlib
import re
import struct

HERE = pathlib.Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location("conv", HERE / "convert_objdump.py")
conv = importlib.util.module_from_spec(spec)
spec.loader.exec_module(conv)

# (id, label, offset, length, pointer slots); gen/checks/link_set.py sets the items
ITEMS = []


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
    b, secs = read_elf(outdir / "target-amd64")
    nm = conv.read_nm(outdir / "target-amd64.nm")
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
        lines = [f"# {ident}: link/data.py, target-amd64 bytes [{a:#x}, {a + n:#x})", f"at {label} {off}"]
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

