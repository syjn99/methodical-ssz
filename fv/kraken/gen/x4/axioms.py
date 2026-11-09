#!/usr/bin/env python3
"""Axiom check of the generated theorems, by program.

Usage: axioms.py write <out.lean> <module> <name>...   (#print axioms for each name)
       axioms.py check <lean-log> <out.json> <name>...
Allowed: propext, Classical.choice, Quot.sound (fv/AGENTS.md). Anything else, or a name whose
axiom line is missing, fails. Python 3 standard library only.
"""
import json
import re
import sys

ALLOWED = {"propext", "Classical.choice", "Quot.sound"}

if sys.argv[1] == "write":
    out, mod, names = sys.argv[2], sys.argv[3], sys.argv[4:]
    open(out, "w").write(f"import {mod}\n\n" + "\n".join(f"#print axioms {n}" for n in names) + "\n")
else:
    log, out, names = open(sys.argv[2]).read(), sys.argv[3], sys.argv[4:]
    rows, ok = [], True
    for n in names:
        m = re.search(rf"'{re.escape(n)}' depends on axioms: \[([^\]]*)\]", log)
        free = re.search(rf"'{re.escape(n)}' does not depend on any axioms", log)
        ax = sorted(x.strip() for x in m[1].replace("\n", " ").split(",")) if m else ([] if free else None)
        good = ax is not None and set(ax) <= ALLOWED
        ok &= good
        rows.append({"name": n, "axioms": ax, "standard_only": good})
    json.dump({"allowed": sorted(ALLOWED), "rows": rows, "all_standard": ok}, open(out, "w"), indent=1)
    print(json.dumps({"names": len(rows), "all_standard": ok}))
    sys.exit(0 if ok else 1)
