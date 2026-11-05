#!/usr/bin/env python3
"""Go value invariants of the witness states (re-proof fix X4).

The main theorems may allow machine states that are not Go values (astra
reprove finding 4: WitBlR had a slice header with len 257, cap 0). This
script reads every Fk/Wit*.lean, rebuilds the byte layout of `block` from
0x10000 and the registers of the start state, and checks the Go values of
the call: the argument slice in (rbx, rcx, rdi) or (rax, rbx, rcx), the slice
fields of the receiver at rax, and the pointer fields (Nested.S, Nested.L,
AttestationData.Source/Target, ListC items). For a slice header (p, len, cap):
len <= cap < 2^63, and if cap > 0 the data p .. p + cap*esz is in the block.
A non-nil pointer and its object are in the block.

Usage (from fv/kraken/lean): python3 tools/wit/goval.py [Fk/WitX.lean ...]
Exit status 1 if a known value violates an invariant. Symbolic values (a
parameter such as `b` or `e8`) are reported, not checked.
"""
import pathlib
import re
import sys

BASE = 0x10000
# Lengths of named byte lists used in blocks.
NAMED = {"bl2049": 257, "bl2048": 257, "blFmtB": 5, "bvFmtJ": 5, "vbvFmt": 35,
         "lcFmtZero": 53, "lcFmtShort": 63}
# Receiver layouts: field offset -> ("slice", esz, elem) or ("ptr", struct).
TYPES = {
    "ListU64": {0: ("slice", 8, None)},
    "FixedVec": {32: ("slice", 8, None)},
    "BitVec": {0: ("slice", 1, None)},
    "BitL": {0: ("slice", 1, None)},
    "ListC": {0: ("slice", 8, "ListU64")},
    "Nested": {8: ("ptr", "Scalars"), 16: ("ptr", "ListU64")},
    "PrysmCheckpoint": {8: ("slice", 1, None)},
    "PrysmAttestationData": {16: ("slice", 1, None), 40: ("ptr", "PrysmCheckpoint"), 48: ("ptr", "PrysmCheckpoint")},
    "Scalars": {},
}
SIZE = {"ListU64": 24, "FixedVec": 56, "BitVec": 24, "BitL": 24, "ListC": 24, "Nested": 24,
        "PrysmCheckpoint": 32, "PrysmAttestationData": 56, "Scalars": 16}


def split_top(s, sep):
    out, depth, cur, i = [], 0, "", 0
    while i < len(s):
        c = s[i]
        if c in "([⟨":
            depth += 1
        elif c in ")]⟩":
            depth -= 1
        if depth == 0 and s.startswith(sep, i):
            out.append(cur.strip()); cur = ""; i += len(sep); continue
        cur += c; i += 1
    out.append(cur.strip())
    return out


def strip_parens(s):
    s = s.strip()
    while s.startswith("(") and s.endswith(")"):
        depth = 0
        for i, c in enumerate(s):
            depth += c == "("
            depth -= c == ")"
            if depth == 0 and i < len(s) - 1:
                return s
        s = s[1:-1].strip()
    return s


def flatten(e):
    e = strip_parens(e)
    parts = split_top(e, "++")
    if len(parts) == 1:
        return [e]
    return [x for p in parts for x in flatten(p)]


def num(t):
    t = t.strip()
    m = re.fullmatch(r"\(?\s*(0x[0-9a-fA-F]+|\d+)\s*(?::\s*(?:BitVec 64|UInt64|Int64))?\s*\)?(?:\.toBitVec)?", t)
    if m:
        return int(m[1], 0)
    m = re.fullmatch(r"\(?(0x[0-9a-fA-F]+|\d+)#64\)?", t)
    if m:
        return int(m[1], 0)
    m = re.fullmatch(r"\(?BitVec\.ofNat 64 (0x[0-9a-fA-F]+|\d+)\)?", t)
    if m:
        return int(m[1], 0)
    m = re.fullmatch(r"\(?UInt64\.toBitVec (0x[0-9a-fA-F]+|\d+)\)?", t)
    if m:
        return int(m[1], 0)
    return None


def piece(e, lens):
    """(length, bytes or None) of one block atom."""
    e = strip_parens(e)
    m = re.fullmatch(r"(?:z|List\.replicate) (\d+)(?: 0)?", e)
    if m:
        return int(m[1]), bytes(int(m[1]))
    m = re.fullmatch(r"Int\.toBytes 8 \(?(-?\d+)(?: : Int)?\)?", e)
    if m:
        return 8, (int(m[1]) % 2 ** 64).to_bytes(8, "little")
    m = re.fullmatch(r"Int\.toBytes 8 (.*)\.toInt", e)
    if m:
        v = num(m[1])
        return 8, (v % 2 ** 64).to_bytes(8, "little") if v is not None else None
    m = re.fullmatch(r"\[([^\]]*)\]", e)
    if m:
        items = [x.strip() for x in m[1].split(",") if x.strip()]
        vals = [num(x) for x in items]
        return len(items), bytes(vals) if all(v is not None for v in vals) else None
    if e in NAMED:
        return NAMED[e], None
    if e in lens:
        return lens[e], None
    m = re.fullmatch(r"List\.replicate (\d+) .*", e)
    if m:
        return int(m[1]), None
    return None, None


def regs_of(txt):
    m = re.search(r"⟨⟨(.*?)⟩,\s*zmms", txt, re.S)
    if not m:
        return None
    r = split_top(m[1].replace("\n", " "), ",")
    return [num(x) for x in r] if len(r) == 16 else None


class Mem:
    def __init__(self, txt):
        m = re.search(r"^def block[^\n]*:= *\n?(.*?)\n\n", txt, re.S | re.M)
        lens = {k: int(v) for k, v in re.findall(r"\(\w+ : (\w+)\.length = (\d+)\)", txt)}
        self.bytes, self.end, self.note, self.partial = {}, BASE, "", ""
        if not m:
            self.note = "no block"; return
        a = BASE
        for p in flatten(" ".join(m[1].split())):
            n, b = piece(p, lens)
            if n is None:  # the layout is known only below a (a symbolic length)
                self.partial = f"layout known below {a:#x} (`{p}` has a symbolic length)"; break
            if b is not None:
                for i, x in enumerate(b):
                    self.bytes[a + i] = x
            a += n
        self.end = a

    def word(self, a):
        bs = [self.bytes.get(a + i) for i in range(8)]
        return None if None in bs else int.from_bytes(bytes(bs), "little")

    def inblock(self, a, n):
        return BASE <= a and a + n <= self.end


def check_slice(mem, name, p, l, c, esz, out):
    if None in (p, l, c) or (mem.partial and c and p + c * esz > mem.end and p >= mem.end):
        out.append((name, (p, l, c), "symbolic"))
        return True
    ok = l <= c < 2 ** 63 and (c == 0 or mem.inblock(p, c * esz))
    why = "ok" if ok else ("len > cap" if l > c else "cap >= 2^63" if c >= 2 ** 63 else "data outside the block")
    out.append((name, (hex(p), l, c), why))
    return ok


def check_obj(mem, ty, a, name, out, depth=0):
    ok = True
    if not mem.inblock(a, SIZE[ty]):
        out.append((name, hex(a), f"{ty} object outside the block"))
        return False
    for off, f in TYPES[ty].items():
        if f[0] == "slice":
            p, l, c = mem.word(a + off), mem.word(a + off + 8), mem.word(a + off + 16)
            ok &= check_slice(mem, f"{name}.{off}", p, l, c, f[1], out)
            if f[2] and None not in (p, l) and depth < 2:
                for i in range(l):
                    q = mem.word(p + 8 * i)
                    if q:
                        ok &= check_obj(mem, f[2], q, f"{name}[{i}]", out, depth + 1)
        else:
            q = mem.word(a + off)
            if q is None:
                out.append((f"{name}.{off}", None, "symbolic"))
            elif q:
                ok &= check_obj(mem, f[1], q, f"{name}.{off}", out, depth + 1)
            else:
                out.append((f"{name}.{off}", 0, "nil"))
    return ok


def check(path):
    txt = pathlib.Path(path).read_text()
    out = []
    m = re.search(r"def P : Program := dataLabels \+\+ (\w+)", txt)
    regs = regs_of(txt)
    mem = Mem(txt)
    if not m or regs is None or mem.note:
        return True, [("-", None, f"not checked: {mem.note or 'no target or registers'}")]
    tgt = m[1]
    ok = True
    if mem.partial:
        out.append(("-", None, "partial: " + mem.partial))
    rax, rbx, rcx, rdi = regs[0], regs[1], regs[2], regs[5]
    if tgt == "ValidateBitvector":
        ok &= check_slice(mem, "buf", rax, rbx, rcx, 1, out)
        return ok, out
    mm = re.fullmatch(r"(\w+?)(UnmarshalSSZ|MarshalSSZTo|SizeSSZ)", tgt)
    ty, meth = mm[1], mm[2]
    if meth != "SizeSSZ":
        ok &= check_slice(mem, "buf" if meth == "UnmarshalSSZ" else "dst", rbx, rcx, rdi, 1, out)
    if rax is None:
        out.append(("recv", None, "symbolic"))
    elif rax == 0:
        out.append(("recv", 0, "nil"))  # a nil receiver is a Go value; the path must not use it
    else:
        ok &= check_obj(mem, ty, rax, "recv", out)
    return ok, out


def main(paths):
    paths = paths or sorted(str(p) for p in pathlib.Path("Fk").glob("Wit*.lean"))
    bad = 0
    for p in paths:
        ok, out = check(p)
        bad += not ok
        for name, val, why in out:
            print(f"{'OK ' if why in ('ok', 'nil') else 'BAD' if why not in ('symbolic',) and not why.startswith(('not checked', 'partial')) else '-- '} "
                  f"{pathlib.Path(p).stem:10} {name:14} {str(val):30} {why}")
    print(f"{len(paths)} witness files, {bad} with a violation")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
