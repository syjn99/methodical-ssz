# e2g-r1 reviewer script (reviews/e2g-r1/own_layout.py), copied unchanged by unit E2-C as the non-author
# recomputation of frame, gd, rt and the first-touch stack regions (pre) of every Gen6*Enc layout. Run from fv/kraken:
#   python3 -I -B prysm/go1.26.10/e2e/scal/e2c/own_layout_e2g_r1.py

"""e2g-r1: third, reviewer-written recomputation of the free layout parameters (G1) from the `.S` and the directive windows
that the Lean proofs step (`win hk a n`): frame, gd, rt, and the set of first-touch stack regions (pre) with sizes.
Reads the layout def of the generated file or the pinned hand layout. No import of generator or kindcheck."""
import json, re, glob, pathlib
bad = 0
ties = pathlib.Path("lean/E2eScal/EncTies.lean").read_text()
for f in sorted(glob.glob("lean/E2eScal/Gen6*Enc.lean")):
    t = pathlib.Path(f).read_text()
    J = json.loads([x for x in t.split("\n") if x.startswith("GEN6-JSON: ")][0][11:])
    D = [l.strip() for l in pathlib.Path(J["S"]).read_text().split("\n") if l.strip()]
    cov = set()
    for a, n in re.findall(r"win hk (\d+) (\d+)", t):
        cov.update(range(int(a), int(a) + int(n)))
    lay = J["layout"].split(".")[-1]
    src = ties if J["layout"].startswith("E2eScal.layEnc") else t
    m = re.search(rf"\ndef {lay} : EncLayout where\n((?:  .*\n)+)", src)
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
    pre = re.findall(r"\.at \(\.(up|dn) (\d+)\) \(\.orig (\d+)\)", L["pre"])
    lens = dict((int(a), int(b)) for a, b in re.findall(r"\((\d+), (\d+)\)", L["lens"]))
    mine = sorted(touched.items())
    theirs = sorted(((int(n) if u == "up" else -int(n)), lens[int(i)]) for u, n, i in pre)
    ok = (mine == theirs and int(L["frame"]) == F and int(L["gd"]) == gd and (L["rt"] == "true") == rt and int(L["nstk"]) == len(pre)
          and (".lo .scr" in L["pre"]) == rt and len({i for _, _, i in pre}) == len(pre))
    # disjointness of the pre regions and of the fixed chunks: return slot [0, 8), scratch below -(F+16)
    regs = sorted(theirs + [(0, 8)])
    disj = all(regs[k][0] + regs[k][1] <= regs[k + 1][0] for k in range(len(regs) - 1)) and all(o >= -(F + 16) for o, _ in theirs)
    bad += (not ok) or (not disj)
    print(("OK  " if ok and disj else "DIFF"), J["type"], "F", F, "gd", gd, "rt", rt, "pre regions", len(mine), "disjoint", disj, "" if ok else f"\n   mine   {mine}\n   theirs {theirs} frame {L['frame']} gd {L['gd']} rt {L['rt']}")
print("layouts that differ from the reviewer's recomputation or are not disjoint:", bad)
