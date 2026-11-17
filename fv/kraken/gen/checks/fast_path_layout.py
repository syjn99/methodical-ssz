"""Recompute the layout of every generated encoder fast-path theorem, independently of the generator and kindcheck.py.

Usage (from fv/kraken; Python 3 standard library only):
  python3 -I -B gen/checks/fast_path_layout.py
For each lean/Prysm/*/GeneratedEncodeFastPath.lean, it reads the `.S` file and the instruction windows that the proof
steps (`window_infix_at hk a n`). From them it computes the frame size, gd, rt and the first-touch stack regions with
their sizes. It compares them with the layout definition of the generated file, or with the pinned hand layout.
It also checks that the regions do not overlap. It imports neither the generator nor kindcheck.py.
Exit 1 if a layout differs or two regions overlap.
"""
import json, re, glob, pathlib
bad = 0


def hand_layout_src(T, gen_text):
    """The text of the module of `lean/Prysm/<T>/` that the generated file imports and that defines `encodeLayout`."""
    for m in re.findall(rf"(?m)^import Prysm\.{T}\.(\w+)$", gen_text):
        s = pathlib.Path(f"lean/Prysm/{T}/{m}.lean").read_text()
        if "\ndef encodeLayout : EncoderFrameLayout where\n" in s:
            return s
    raise SystemExit(f"hand layout of {T}: no imported module of lean/Prysm/{T}/ defines it")


for f in sorted(glob.glob("lean/Prysm/*/GeneratedEncodeFastPath.lean")):
    t = pathlib.Path(f).read_text()
    J = json.loads([x for x in t.split("\n") if x.startswith("FAST-PATH-JSON: ")][0][len("FAST-PATH-JSON: "):])
    D = [l.strip() for l in pathlib.Path(J["assembly"]).read_text().split("\n") if l.strip()]
    cov = set()
    for a, n in re.findall(r"window_infix_at hk (\d+) (\d+)", t):
        cov.update(range(int(a), int(a) + int(n)))
    lay = J["layout"].split(".")[-1]
    src = hand_layout_src(J["layout"].split(".")[1], t) if J["layout"].endswith(".encodeLayout") else t
    # the def line: root-qualified (a layout of another type than the block), relative to Prysm.<T>, or the last component
    full, m = J["layout"], None
    for d in (f"_root_.{full}", full.split(".", 2)[2], lay):
        m = m or re.search(rf"\ndef {re.escape(d)} : EncoderFrameLayout where\n((?:  .*\n)+)", src)
    L, cur = {}, None
    for l in m[1].split("\n"):
        mm = re.match(r"  (\w+) := (.*)", l)
        if mm: cur = mm[1]; L[cur] = mm[2]
        elif l.startswith("    ") and cur: L[cur] += " " + l.strip()      # continuation line (hand layouts)
    # own derivation
    g = re.fullmatch(r"lea -0x([0-9a-f]+)\(%rsp\),%r12", D[2]); gd = int(g[1], 16) if g else 0
    fr = [re.fullmatch(r"(?:sub \$0x([0-9a-f]+)|add \$-0x([0-9a-f]+)),%rsp", d) for d in D[:9]]
    F = [int(x[1] or x[2], 16) for x in fr if x][0]
    SP = -(F + 8)
    base = {"rsp": SP}; reg = {}
    touched = {}           # offset from the entry rsp -> size
    def touch(o, n):
        for a, s in list(touched.items()):
            if a <= o and o + n <= a + s: return
            assert o + n <= a or a + s <= o, (f, "overlap", a, s, o, n)
        touched[o] = n
    touch(-8, 8)           # push %rbp
    for i in sorted(cov):
        d = D[i]
        m1 = re.fullmatch(r"lea (-?0x[0-9a-f]+)\(%rsp\),%(\w+)", d)
        if m1: reg[m1[2]] = SP + int(m1[1], 16); continue
        m2 = re.fullmatch(r"(mov|movups) %(\w+),(-?0x[0-9a-f]+)?\(%(\w+)\)", d)
        if m2:
            b = m2[4]; off = int(m2[3], 16) if m2[3] else 0
            if b == "rsp": touch(SP + off, 16 if m2[1] == "movups" else 8)
            elif b in reg: touch(reg[b] + off, 16 if m2[1] == "movups" else 8)
            continue
        if d == "callq runtime.memmove": touch(-(F + 16), 8); continue
        m3 = re.fullmatch(r"(?:mov|lea|add|sub|xor) .*,%(\w+)", d)
        if m3 and m3[1] in reg and not m1: del reg[m3[1]]      # the register no longer holds a frame address
    rt = any(D[i] == "callq runtime.memmove" for i in cov)
    pre = re.findall(r"\.at \(\.(above|below) (\d+)\) \(\.original (\d+)\)", L["pre"])
    lens = dict((int(a), int(b)) for a, b in re.findall(r"\((\d+), (\d+)\)", L["stackChunkLengths"]))
    mine = sorted(touched.items())
    theirs = sorted(((int(n) if u == "above" else -int(n)), lens[int(i)]) for u, n, i in pre)
    ok = (mine == theirs and int(L["frame"]) == F and int(L["guardAddend"]) == gd and (L["callsMemmove"] == "true") == rt and int(L["stackChunkCount"]) == len(pre)
          and (".low .scratch" in L["pre"]) == rt and len({i for _, _, i in pre}) == len(pre))
    # disjointness of the pre regions and of the fixed chunks: return slot [0, 8), scratch below -(F+16)
    regs = sorted(theirs + [(0, 8)])
    disj = all(regs[k][0] + regs[k][1] <= regs[k + 1][0] for k in range(len(regs) - 1)) and all(o >= -(F + 16) for o, _ in theirs)
    bad += (not ok) or (not disj)
    print(("OK  " if ok and disj else "DIFF"), J["type"], "F", F, "gd", gd, "rt", rt, "pre regions", len(mine), "disjoint", disj, "" if ok else f"\n   mine   {mine}\n   theirs {theirs} frame {L['frame']} gd {L['gd']} rt {L['rt']}")
print("layouts that differ from the independent recomputation or are not disjoint:", bad)
raise SystemExit(1 if bad else 0)
