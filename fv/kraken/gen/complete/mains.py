#!/usr/bin/env python3
"""Write the input of Complete.lean: fully qualified names of the hand main theorems,
callee function-spec theorems and composition theorems of the frozen list.
The short names come from gen/frozen/THEOREMS.json; the namespace comes from
AXIOMS.txt (module <TAB> name <TAB> axioms), a file of resolved names.
Usage: mains.py <THEOREMS.json> <AXIOMS.txt> [<negative/RESULT>]   (stdout)
With RESULT, the designated theorem of every negative case is added too."""
import json
import sys

th = json.load(open(sys.argv[1]))
names = set()
for r in th["hand_case"]["obligations"]:
    names.update(n for n in r["hand_theorems"] if not n.startswith("Wit"))
for v in th["callee_function_specs"].values():
    names.update(v)
full = {}
for line in open(sys.argv[2]):
    p = line.rstrip("\n").split("\t")
    if len(p) == 3:
        full.setdefault(p[1].rsplit(".", 1)[-1], []).append(p[1])
if len(sys.argv) > 3:
    for line in open(sys.argv[3]):
        f = [x.strip() for x in line.split("|")]
        if len(f) > 2 and f[2].split(" ")[0] in full:
            names.add(f[2].split(" ")[0])
for n in sorted(names):
    c = full.get(n, [])
    if len(c) != 1:
        raise SystemExit(f"{n}: {len(c)} resolved names in AXIOMS.txt")
    print(c[0])
