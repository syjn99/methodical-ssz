#!/usr/bin/env python3
"""Go value invariants of the witness states (re-proof fix X4, fix 2 X3).

The main theorems may allow machine states that are not Go values (astra
reprove finding 4; astra reprove-fix finding 3: the Scalars object is 24
bytes in Go, 16 bytes in SSZ). This script reads every Fk/Wit*.lean, rebuilds
the byte layout of `block` from 0x10000, the registers of the start state
and the chunks of `s_mem`, and checks the Go values of the call against the
amd64 layout in layout.json (written by layout.go from unsafe.Sizeof,
unsafe.Alignof, unsafe.Offsetof with the gc amd64 sizes; no table by hand):

- slice header (p, len, cap): len <= cap < 2^63; if cap > 0 the data
  p .. p + cap*esz is in the block and p is aligned to the element;
- object (receiver, pointer field, list element): in the block, address
  aligned to the type's alignment, whole Go size (padding included);
- bool field: the byte is 0 or 1;
- interface type word: for a witness whose premise places the errorString
  itab's type word (itab+8, read into the `%w` argument), the word is a
  non-nil, 8-aligned pointer to the 56-byte `*errors.errorString` descriptor
  (abi.PtrType) in the block, and the descriptor's raw bytes are the ELF's
  (fix 3 X3): Size_ 8, Kind_ 22 (Pointer); the bytes of named included items
  (`Fk.Data.*`) are read from link/out/data/<name>.data;
- error global (fix 3 X3): for a witness whose premise places the two words
  of an `ssz.Err*` global, the global is initialized as Go's `errors.New`
  leaves it: word 0 is the errorString itab, word 1 a non-nil, 8-aligned
  pointer to a 16-byte errorString in the block whose message (pointer, length)
  is in the block;
- overlap: the Go objects (objects, slice data up to cap, type descriptor)
  are pairwise disjoint, and every `s_mem` chunk lies inside one Go object or
  outside all of them (a chunk across an object boundary fails).

Usage (from fv/kraken/lean): python3 tools/wit/goval.py [Fk/WitX.lean ...]
Exit status 1 if a known value violates an invariant. Symbolic values (a
parameter such as `b` or `e8`) are reported as "not checked", not passed.
"""
import json
import pathlib
import re
import sys

BASE = 0x10000
# Lengths of named byte lists used in blocks.
NAMED = {"errorStringPtrType": 56, "bl2049": 257, "bl2048": 257, "blFmtB": 5, "bvFmtJ": 5, "vbvFmt": 35,
         "lcFmtZero": 53, "lcFmtShort": 63, "vblMsgE": 42, "vblMsgZ": 21, "vblMsgB": 13,
         "luFmtTooBig": 56, "luFmtMis": 68, "lcFmtOrder": 67}
LAYOUT = json.loads((pathlib.Path(__file__).parent / "layout.json").read_text())
assert (LAYOUT["goos"], LAYOUT["goarch"]) == ("linux", "amd64")
TY = LAYOUT["types"]
TYPEDESC = 56  # sizeof(abi.PtrType) = abi.Type (48) + Elem, Go 1.26.3 amd64
DATA = pathlib.Path(__file__).resolve().parents[3] / "link" / "out" / "data"


def data_bytes(name):
    """Raw bytes of an included item (link/out/data/<name>.data); None at `word`
    positions (pointer words depend on the host's labels)."""
    p = DATA / f"{name}.data"
    if not p.exists():
        return None
    out = []
    for line in p.read_text().splitlines():
        w = line.split()
        if w and w[0] == "bytes":
            out += [int(x, 16) for x in w[1:]]
        elif w and w[0] == "word":
            out += [None] * 8
    return out


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
        return NAMED[e], data_bytes(e)
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
        lens.update({k: int(v) for k, v in re.findall(r"theorem \w+ : \((.+?)\)\.length = (\d+) :=", txt)})
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
                    if x is not None:
                        self.bytes[a + i] = x
            a += n
        self.end = a

    def word(self, a):
        bs = [self.bytes.get(a + i) for i in range(8)]
        return None if None in bs else int.from_bytes(bytes(bs), "little")

    def inblock(self, a, n):
        return BASE <= a and a + n <= self.end


REG = ["rax", "rbx", "rcx", "rdx", "rsi", "rdi", "rsp", "rbp", "r8", "r9", "r10", "r11", "r12", "r13", "r14", "r15"]


def labels_of(txt):
    out = {}
    m = re.search(r"def dataLabels : Program :=\s*\[(.*?)\]", txt, re.S)
    if m:  # the data labels of a witness host sit at 0x10000 + index
        for i, name in enumerate(re.findall(r'\.label "([^"]+)"', m[1])):
            out[name] = 0x10000 + i
    for name, v in re.findall(r'theorem label_\w+\'? : label "([^"]+)" = ([^:\n]+?) :=', txt):
        v = v.strip()
        m = re.fullmatch(r"0x10000 \+ Int64\.ofNat (\d+)", v)
        out[name] = 0x10000 + int(m[1]) if m else int(v, 0)
    return out


def addr_of(e, regs, labs):
    """Value of an address expression of s_mem, or None."""
    e = re.sub(r"s\.regs\.(\w+)\.toBitVec", lambda m: str(regs[REG.index(m[1])]) if regs[REG.index(m[1])] is not None else "None", e)
    e = re.sub(r'\(label "([^"]+)"\)\.toBitVec|label "([^"]+)"', lambda m: str(labs.get(m[1] or m[2], "None")), e)
    e = re.sub(r"BitVec\.ofNat 64 (\w+)", r"\1", e)
    e = re.sub(r"\((0x[0-9a-fA-F]+|\d+) : BitVec 64\)", r"\1", e)
    e = re.sub(r"(0x[0-9a-fA-F]+|\d+)#64", r"\1", e)
    e = e.replace(".toBitVec", "")
    if "None" in e or not re.fullmatch(r"[\s()+\-0-9a-fx]*", e):
        return None
    return eval(e) % 2 ** 64


def chunks_of(txt, regs, labs, lens):
    """(lo, hi, text) of every `Eq (X.At addr)` chunk of s_mem with a known
    length and address; and the number of chunks not read."""
    m = re.search(r"theorem s_mem.*?=⋆(.*?):= by", txt, re.S)
    if not m:
        return [], 0
    out, unread = [], 0
    for c in split_top(" ".join(m[1].split()), "⋆"):
        mm = re.fullmatch(r"Eq \((.*)\.At (.*)\)", c)
        if not mm:
            continue  # heap predicates, frame `fun _ => True`
        x, a = mm[1], mm[2]
        mt = re.fullmatch(r"\(?(\w+)\.(take|drop) (\d+)\)?", x)
        n = None
        if mt and mt[1] in lens:
            n = int(mt[3]) if mt[2] == "take" else lens[mt[1]] - int(mt[3])
        elif x.strip() in ("(([] : List UInt8))", "([] : List UInt8)"):
            n = 0
        else:
            n, _ = piece(x, lens)
        lo = addr_of(a, regs, labs)
        if n is None or lo is None:
            unread += 1
            continue
        if n:
            out.append((lo, lo + n, c[:60]))
    return out, unread


class Objs:
    """The Go objects of a witness: (lo, hi, name)."""
    def __init__(self):
        self.l = []

    def add(self, lo, hi, name):
        if hi > lo:
            self.l.append((lo, hi, name))


def check_slice(mem, objs, name, p, l, c, esz, out):
    if None in (p, l, c) or (mem.partial and c and p + c * esz > mem.end and p >= mem.end):
        out.append((name, (p, l, c), "not checked: symbolic"))
        return True
    ok = l <= c < 2 ** 63 and (c == 0 or mem.inblock(p, c * esz)) and (c == 0 or p % min(esz, 8) == 0)
    why = "ok" if ok else ("len > cap" if l > c else "cap >= 2^63" if c >= 2 ** 63 else
                           "data outside the block" if not mem.inblock(p, c * esz) else "data not aligned")
    out.append((name, (hex(p), l, c), why))
    objs.add(p, p + c * esz, name + ".data")
    return ok


def check_obj(mem, objs, ty, a, name, out, depth=0):
    t = TY[ty]
    if not mem.inblock(a, t["size"]):
        out.append((name, hex(a), f"{ty} object [{a:#x}, {a + t['size']:#x}) outside the block"))
        return False
    ok = a % t["align"] == 0
    out.append((name, hex(a), f"ok: {ty} size {t['size']} align {t['align']}" if ok else f"{ty} at {a:#x} not aligned to {t['align']}"))
    objs.add(a, a + t["size"], name)
    for f in t["fields"]:
        off, fn = f["offset"], f"{name}.{f['name']}"
        if f["kind"] == "slice":
            p, l, c = mem.word(a + off), mem.word(a + off + 8), mem.word(a + off + 16)
            ok &= check_slice(mem, objs, fn, p, l, c, f["esz"], out)
            if f.get("elem") and None not in (p, l) and depth < 2:
                for i in range(l):
                    q = mem.word(p + 8 * i)
                    if q:
                        ok &= check_obj(mem, objs, f["elem"], q, f"{name}[{i}]", out, depth + 1)
        elif f["kind"] == "ptr":
            q = mem.word(a + off)
            if q is None:
                out.append((fn, None, "not checked: symbolic"))
            elif q:
                ok &= check_obj(mem, objs, f["elem"], q, fn, out, depth + 1)
            else:
                out.append((fn, 0, "nil"))
        elif f["kind"] == "bool":
            v = mem.bytes.get(a + off)
            if v is None:
                out.append((fn, None, "not checked: symbolic"))
            else:
                out.append((fn, v, "ok" if v <= 1 else "bool byte > 1"))
                ok &= v <= 1
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
    objs = Objs()
    if mem.partial:
        out.append(("-", None, "partial: " + mem.partial))
    rax, rbx, rcx, rdi = regs[0], regs[1], regs[2], regs[5]
    rsp = regs[6]
    if rsp is not None:  # Go stack slots are 8-byte words: rsp (the return address slot) is 8-aligned
        out.append(("rsp", hex(rsp), "ok" if rsp % 8 == 0 else "rsp not 8-aligned"))
        ok &= rsp % 8 == 0
    if tgt == "ValidateBitvector":
        ok &= check_slice(mem, objs, "buf", rax, rbx, rcx, 1, out)
    else:
        mm = re.fullmatch(r"(\w+?)(UnmarshalSSZ|MarshalSSZTo|SizeSSZ)", tgt)
        ty, meth = mm[1], mm[2]
        if meth != "SizeSSZ":
            ok &= check_slice(mem, objs, "buf" if meth == "UnmarshalSSZ" else "dst", rbx, rcx, rdi, 1, out)
        if rax is None:
            out.append(("recv", None, "not checked: symbolic"))
        elif rax == 0:
            out.append(("recv", 0, "nil"))  # a nil receiver is a Go value; the path must not use it
        else:
            ok &= check_obj(mem, objs, ty, rax, "recv", out)
    labs = labels_of(txt)
    it = labs.get("go_itab._errors.errorString_error")
    # The type word matters where the code reads it into an interface value
    # (the `%w` argument): the premise places itab+8.
    if it is not None and ('go_itab._errors.errorString_error").toBitVec + 8)' in txt
                           or f"(({it} : UInt64).toBitVec + 8))" in txt):
        w = mem.word(it + 8)
        if w is None:
            out.append(("itab+8", None, "not checked: symbolic"))
        else:
            good = w != 0 and w % 8 == 0 and mem.inblock(w, TYPEDESC)
            out.append(("itab+8", hex(w), "type word ok" if good else "type word is not a pointer to a type descriptor in the block"))
            ok &= good
            if good:
                objs.add(w, w + TYPEDESC, "typedesc")
                size, kind = mem.word(w), mem.bytes.get(w + 23)
                td = size == 8 and kind is not None and kind & 31 == 22
                out.append(("typedesc", f"size {size} kind {None if kind is None else kind & 31}",
                            "ok: *errors.errorString descriptor" if td else "type descriptor is not the ELF's (Size_ 8, Kind_ 22)"))
                ok &= td
    # initialized error globals: (itab, pointer to a 16-byte errorString)
    for g in sorted(set(re.findall(r'\.At \(label "(ssz\.Err\w+)"\)\.toBitVec\)', txt))):
        ga = labs.get(g)
        e0, e1 = (mem.word(ga), mem.word(ga + 8)) if ga is not None else (None, None)
        if e0 is None or e1 is None:
            out.append((g, None, "not checked: symbolic")); continue
        sp, ln = (mem.word(e1), mem.word(e1 + 8)) if e1 else (None, None)
        good = (it is not None and e0 == it and e1 != 0 and e1 % 8 == 0 and mem.inblock(e1, 16)
                and sp is not None and ln is not None and mem.inblock(sp, ln))
        out.append((g, f"({e0:#x}, {e1:#x})", "ok: initialized (itab, errorString)" if good else "error global is not initialized (nil or no errorString)"))
        ok &= good
        if good:
            objs.add(e1, e1 + 16, f"{g}.obj")
    # overlap: Go objects pairwise disjoint; each s_mem chunk inside one object or outside all
    L = sorted(objs.l)
    for i in range(len(L)):
        for j in range(i + 1, len(L)):
            a, b = L[i], L[j]
            if a[0] < b[1] and b[0] < a[1]:
                out.append((f"{a[2]}/{b[2]}", f"[{a[0]:#x},{a[1]:#x}) [{b[0]:#x},{b[1]:#x})", "Go objects overlap"))
                ok = False
    lens = {k: int(v) for k, v in re.findall(r"\(\w+ : (\w+)\.length = (\d+)\)", txt)}
    lens.update({k: int(v) for k, v in re.findall(r"theorem \w+ : \((.+?)\)\.length = (\d+) :=", txt)})
    lens.update({k: int(v) for k, v in re.findall(r"theorem \w+ : (\w+)\.length = (\d+) :=", txt)})
    ch, unread = chunks_of(txt, regs, labs, lens)
    for lo, hi, c in ch:
        for a in L:
            if lo < a[1] and a[0] < hi and not (a[0] <= lo and hi <= a[1]):
                out.append((a[2], f"chunk [{lo:#x},{hi:#x}) object [{a[0]:#x},{a[1]:#x})", "s_mem chunk crosses a Go object boundary"))
                ok = False
    out.append(("chunks", f"{len(ch)} read, {unread} not read", "ok"))
    return ok, out


def main(paths):
    paths = paths or sorted(str(p) for p in pathlib.Path("Fk").glob("Wit*.lean"))
    bad = unchecked = 0
    for p in paths:
        ok, out = check(p)
        bad += not ok
        unchecked += any(why.startswith("not checked") for _, _, why in out)
        for name, val, why in out:
            tag = "-- " if why.startswith(("not checked", "partial")) else "OK " if (
                why in ("ok", "nil", "type word ok") or why.startswith("ok: ")) else "BAD"
            print(f"{tag} {pathlib.Path(p).stem:10} {name:22} {str(val):34} {why}")
    print(f"{len(paths)} witness files, {bad} with a violation, {unchecked} with a value not checked")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
