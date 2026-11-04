#!/usr/bin/env python3
"""Convert `go tool objdump -gnu` output into labeled AT&T assembly for Kraken.

Usage: conv.py <objdump> <nm> <outdir> [--norm]

<objdump> is `go tool objdump -gnu -s <regexp> <elf>` output. <nm> is
`go tool nm -size -sort address <elf>` output. One `<fn>.S` file is written
per function, plus `all.S` (all functions in address order).

The converter changes only what Kraken cannot take from objdump directly:
- absolute jump and call targets become labels: `L_<fn>_<hexoff>` inside the
  function, the symbol name outside it;
- `disp(%rip)` becomes `sym+off(%rip)` for the symbol that holds the target;
- symbol names are shortened (module path dropped) and characters outside
  `[A-Za-z0-9_.]` become `_` (Kraken identifier token).
With --norm it also rewrites padding forms (`nopl (%rax)`, `data16 nop`) to
`nop` (listed in REPORT/K1, a gap in the Kraken parser, not a semantic change:
Kraken layouts are abstract, so the byte length of a nop is not used).
"""
import re
import sys

MOD = "github.com/OffchainLabs/methodical-ssz/"


def clean(name):
    name = name.replace(MOD + "fv/kraken/", "").replace(MOD, "")
    name = re.sub(r"\(\*(\w+)\)", r"\1", name)  # (*Scalars) -> Scalars
    return re.sub(r"[^A-Za-z0-9_.]", "_", name)


def read_nm(path):
    syms = []
    for line in open(path):
        p = line.split()
        if len(p) >= 4:
            syms.append((int(p[0], 16), int(p[1]), p[3]))
    return syms


def sym_at(syms, addr):
    """Symbol whose [start, start+size) holds addr, as (name, offset)."""
    best, near = None, None
    for start, size, name in syms:
        if start == addr:
            return name, 0
        if start <= addr < start + max(size, 1):
            best = (name, addr - start)
        if start <= addr:
            near = (name, addr - start)
    # ponytail: Go nm lists type descriptors as one size-0 group (`type:*`), so
    # an address inside it is named by the nearest preceding symbol + offset.
    if best is None and near is None:
        raise SystemExit(f"no symbol at {addr:#x}")
    return best or near


def read_objdump(path):
    fns, cur = [], None
    for line in open(path):
        if line.startswith("TEXT "):
            cur = {"name": line.split()[1].removesuffix("(SB)"), "ins": []}
            fns.append(cur)
            continue
        m = re.match(r"\s+\S+\s+0x([0-9a-f]+)\s+([0-9a-f]+)\s+.*?// (.*)$", line)
        if m and cur is not None:
            att = re.sub(r"\s+", " ", m.group(3)).strip()
            cur["ins"].append((int(m.group(1), 16), len(m.group(2)) // 2, att))
    return fns


BRANCH = re.compile(r"^(j[a-z]+|callq?|jmpq?) 0x([0-9a-f]+)$")
RIP = re.compile(r"(-?0x[0-9a-f]+|-?\d+)\(%rip\)")
NORM = {"nopl (%rax)": "nop", "data16 nop": "nop", "nopw 0x0(%rax,%rax,1)": "nop"}


def convert(fn, syms, norm):
    name = clean(fn["name"])
    lo = fn["ins"][0][0]
    hi = fn["ins"][-1][0] + fn["ins"][-1][1]
    lab = lambda a: f"L_{name}_{a - lo:x}"
    targets, body = set(), []
    for addr, ln, att in fn["ins"]:
        m = BRANCH.match(att)
        if m:
            t = int(m.group(2), 16)
            if lo <= t < hi:
                targets.add(t)
                att = f"{m.group(1)} {lab(t)}"
            else:
                s, off = sym_at(syms, t)
                if off:
                    raise SystemExit(f"branch into the middle of {s}")
                att = f"{m.group(1)} {clean(s)}"
        else:
            r = RIP.search(att)
            if r:
                t = addr + ln + int(r.group(1), 0)
                s, off = sym_at(syms, t)
                ref = clean(s) + (f"+{off}" if off else "")
                att = att[: r.start()] + f"{ref}(%rip)" + att[r.end():]
        if norm:
            att = NORM.get(att, att)
        body.append((addr, att))
    out = [f"{name}:"]
    for addr, att in body:
        if addr in targets:
            out.append(f"{lab(addr)}:")
        out.append(f"  {att}")
    return name, "\n".join(out) + "\n"


def main():
    objdump, nm, outdir = sys.argv[1:4]
    norm = "--norm" in sys.argv
    syms = read_nm(nm)
    allS = []
    for fn in read_objdump(objdump):
        name, text = convert(fn, syms, norm)
        open(f"{outdir}/{name}.S", "w").write(text)
        allS.append(text)
    open(f"{outdir}/all.S", "w").write("".join(allS))


def selftest():
    syms = [(0x100, 0x20, "pkg.f"), (0x200, 16, "ssz.ErrSize")]
    fn = {"name": "pkg.f", "ins": [(0x100, 2, "jae 0x104"), (0x102, 2, "mov 0xfc(%rip),%rax"),
                                   (0x104, 1, "retq")]}
    _, text = convert(fn, syms, False)
    assert "jae L_pkg.f_4" in text and "L_pkg.f_4:\n  retq" in text, text
    assert "mov ssz.ErrSize(%rip),%rax" in text, text


if __name__ == "__main__":
    selftest()
    main()
