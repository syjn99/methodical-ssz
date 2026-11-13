#!/usr/bin/env python3
"""Convert `go tool objdump -gnu` output into labeled AT&T assembly for Kraken.

Usage: convert_objdump.py <objdump> <nm> <outdir> [--norm]

<objdump> is `go tool objdump -gnu -s <regexp> <elf>` output. <nm> is
`go tool nm -size -sort address <elf>` output. One `<fn>.S` file is written
per function, plus `all.S` (all functions in address order).

The converter changes only what Kraken cannot take from objdump directly:
- absolute jump and call targets become labels: `L_<fn>_<hexoff>` inside the
  function, the symbol name outside it;
- `disp(%rip)` becomes `sym+off(%rip)` for the symbol that holds the target;
- symbol names are shortened (module path dropped) and characters outside
  `[A-Za-z0-9_.]` become `_` (Kraken identifier token).
With --norm it also rewrites padding forms (table NORM) to `nop` (a gap in the
Kraken parser, not a semantic change: Kraken layouts are abstract, so the byte
length of a nop is not used; check.py compares the original bytes), and drops
the zero index `,%riz,1)` of a SIB operand (RIZ; same address).

The converter fails (exit status 1) on: an instruction line without the GNU
form (`// ...`), an address gap between instructions, a branch into the middle
of an instruction, and two symbol names that sanitize to the same name.
"""
import re
import sys

MOD = "github.com/OffchainLabs/methodical-ssz/"


CLEANED = {}


def clean(name):
    """Shorten and sanitize a symbol name; fail if two names map to one."""
    out = name.replace(MOD + "fv/kraken/", "").replace(MOD, "")
    out = re.sub(r"\(\*(\w+)\)", r"\1", out)  # (*Scalars) -> Scalars
    out = re.sub(r"[^A-Za-z0-9_.]", "_", out)
    if CLEANED.setdefault(out, name) != name:
        raise SystemExit(f"name collision: {name!r} and {CLEANED[out]!r} both become {out!r}")
    return out


def read_nm(path):
    syms = []
    for line in open(path):
        p = line.split()
        if len(p) >= 4:
            syms.append((int(p[0], 16), int(p[1]), p[3]))
    # Sort so that ties at one address (e.g. `runtime.types` and `type:*`) do
    # not depend on the order go nm prints them in.
    return sorted(syms)


def sym_at(syms, addr):
    """Symbol whose [start, start+size) holds addr, as (name, offset)."""
    best, near, exact = None, None, None
    for start, size, name in syms:
        if start == addr:
            exact = (name, 0)  # last of the sorted ties: stable across nm orders
        if start <= addr < start + max(size, 1):
            best = (name, addr - start)
        if start <= addr:
            near = (name, addr - start)
    # ponytail: Go nm lists type descriptors as one size-0 group (`type:*`), so
    # an address inside it is named by the nearest preceding symbol + offset.
    if exact:
        return exact
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
        if not line.strip():
            continue
        m = re.match(r"\s+\S+\s+0x([0-9a-f]+)\s+([0-9a-f]+)\s+.*?// (.*)$", line)
        if not m or cur is None:
            raise SystemExit(f"unrecognized objdump line (no GNU form?): {line.rstrip()!r}")
        att = re.sub(r"\s+", " ", m.group(3)).strip()
        a, n = int(m.group(1), 16), len(m.group(2)) // 2
        if cur["ins"] and cur["ins"][-1][0] + cur["ins"][-1][1] != a:
            raise SystemExit(f"address gap before {a:#x} in {cur['name']}")
        cur["ins"].append((a, n, att))
    return fns


BRANCH = re.compile(r"^(j[a-z]+|callq?|jmpq?) 0x([0-9a-f]+)$")
RIP = re.compile(r"(-?0x[0-9a-f]+|-?\d+)\(%rip\)")
NORM = {"nopl (%rax)": "nop", "data16 nop": "nop", "nopw 0x0(%rax,%rax,1)": "nop",
        "nopw (%rax,%rax,1)": "nop", "nopl 0x0(%rax)": "nop", "nopl 0x0(%rax,%rax,1)": "nop", "nopl (%rax,%rax,1)": "nop",
        "nopw %cs:0x0(%rax,%rax,1)": "nop", "data16 nopw %cs:0x0(%rax,%rax,1)": "nop", "xchg %ax,%ax": "nop"}
# `%riz` (Go 1.26.10): GNU objdump prints a SIB byte without an index register as index
# `%riz` (for example `0x10(%r12,%riz,1)`: base r12 needs a SIB byte). The index is zero, so the
# address is `0x10(%r12)`. Kraken's parser has no `riz` register. Same address, same bytes (check.py (d)).
RIZ = re.compile(r",%riz,1\)")
# User-approved fix: `go tool objdump -gnu` prints a negative 32-bit memory displacement as an
# unsigned 8-digit hex number (`lea 0xffffff1c(%rdi),%rdx` for -228). x86-64 sign-extends disp32, but Kraken's parser
# reads the token as +4294967068 and clang rejects it. Under --norm such a displacement (exactly 8 hex digits, top bit
# set, directly followed by `(%`, not an immediate `$0x...`, not `%rip`) is written in its signed form `-0xe4(%rdi)`.
# Same address, same bytes: check.py (d) reassembles the line and compares it with the ELF.
DISP32 = re.compile(r"(?<![\w$\-])0x([89a-f][0-9a-f]{7})(?=\(%(?!rip))")


def signed_disp32(att):
    return DISP32.sub(lambda m: f"-0x{(1 << 32) - int(m.group(1), 16):x}", att)


def convert(fn, syms, norm):
    name = clean(fn["name"])
    lo = fn["ins"][0][0]
    hi = fn["ins"][-1][0] + fn["ins"][-1][1]
    lab = lambda a: f"L_{name}_{a - lo:x}"
    starts = {a for a, _, _ in fn["ins"]}
    targets, body = set(), []
    for addr, ln, att in fn["ins"]:
        m = BRANCH.match(att)
        if m:
            t = int(m.group(2), 16)
            if lo <= t < hi:
                if t not in starts:
                    raise SystemExit(f"branch into the middle of an instruction: {t:#x} in {name}")
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
            att = RIZ.sub(")", att)
            att = signed_disp32(att)
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
    for bad in ({"name": "pkg.g", "ins": [(0x100, 2, "jmp 0x101"), (0x102, 1, "retq")]},):
        try:
            convert(bad, syms, False)
            raise AssertionError("mid-instruction branch accepted")
        except SystemExit:
            pass
    riz = {"name": "pkg.r", "ins": [(0x100, 6, "mov 0x10(%r12,%riz,1),%r12"), (0x106, 1, "retq")]}
    assert "  mov 0x10(%r12),%r12\n" in convert(riz, syms, True)[1]
    assert "%riz" in convert(riz, syms, False)[1]
    d32 = {"name": "pkg.d", "ins": [(0x100, 7, "lea 0xffffff1c(%rdi),%rdx"), (0x107, 7, "mov $0xffffff1c,%rax"),
                                    (0x10e, 6, "mov 0x7fffffff(%rax),%rcx"), (0x114, 8, "mov %rbx,0x80000000(%rsi,%rcx,8)"),
                                    (0x11c, 1, "retq")]}
    t = convert(d32, syms, True)[1]
    assert "  lea -0xe4(%rdi),%rdx\n" in t, t
    assert "  mov $0xffffff1c,%rax\n" in t, t
    assert "  mov 0x7fffffff(%rax),%rcx\n" in t, t
    assert "  mov %rbx,-0x80000000(%rsi,%rcx,8)\n" in t, t
    assert "  lea 0xffffff1c(%rdi),%rdx\n" in convert(d32, syms, False)[1]
    clean("pkg.h[uint8]")
    try:
        clean("pkg.h_uint8_")
        raise AssertionError("name collision accepted")
    except SystemExit:
        pass
    CLEANED.clear()


if __name__ == "__main__":
    selftest()
    main()
