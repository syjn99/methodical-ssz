#!/usr/bin/env python3
"""Atom normalisation of generated witness text (REPORT 7.6: witness values as `n#64`).

Rewrites the 64-bit numeral atoms `(N : BitVec 64)` and `BitVec.ofNat 64 N` (N a decimal or hex
numeral) to `N#64`, so one value has one spelling in every hypothesis and goal. `StaticBox (-4 + x)`
style atoms are not touched (they stay opaque through `generalize` in the proofs).

Usage: normalize.py <in-dir> <out-dir> [Wit1,Wit2,...]  -> <out-dir>/<file>, <out-dir>/normalize.json
Python 3 standard library only. Run with python3 -I -B.
"""
import json
import os
import re
import sys

ATOMS = [(re.compile(r"\((0x[0-9a-fA-F]+|\d+) : BitVec 64\)"), r"(\1#64)"),
         (re.compile(r"\bBitVec\.ofNat 64 (0x[0-9a-fA-F]+|\d+)\b"), r"(\1#64)")]
# Lines that bridge the block to `mem` keep their spelling: `wit_split` (Fk.WHost, fix3) matches it.
KEEP = re.compile(r"^(def mem\b|\s*have H : Eq \(\(block\b)")


def normalize(txt):
    n = 0
    out = []
    for line in txt.split("\n"):
        if not KEEP.match(line):
            for rx, rep in ATOMS:
                line, k = rx.subn(rep, line)
                n += k
        out.append(line)
    return "\n".join(out), n


def main(src, out, only=None):
    os.makedirs(out, exist_ok=True)
    rows = []
    for f in sorted(os.listdir(src)):
        if not re.fullmatch(r"Wit\w*\.lean", f) or (only and f[:-5] not in only):
            continue
        t, n = normalize(open(os.path.join(src, f)).read())
        t2, n2 = normalize(t)
        open(os.path.join(out, f), "w").write(t)
        rows.append({"file": f, "atoms_rewritten": n, "idempotent": n2 == 0 and t2 == t})
    res = {"files": len(rows), "atoms_rewritten": sum(r["atoms_rewritten"] for r in rows),
           "files_changed": sum(r["atoms_rewritten"] > 0 for r in rows), "idempotent": all(r["idempotent"] for r in rows), "rows": rows}
    json.dump(res, open(os.path.join(out, "normalize.json"), "w"), indent=1)
    print(json.dumps({k: v for k, v in res.items() if k != "rows"}))
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1], sys.argv[2], sys.argv[3].split(",") if len(sys.argv) > 3 else None))
