#!/usr/bin/env python3
"""LV T3: the prysm-e2e axioms gate with the LV and the LV T3 hand lists.

The text of `lvaxioms_gate.py` (not changed): it imports `axioms_gate.py` (not changed) and widens two module
constants before the call: ROOTS gets "E2eList", LISTS gets `gen/e2e/AxiomsLv.lean` and `gen/e2e/AxiomsLvT3.lean`.
Usage: the same as `lvaxioms_gate.py` (run <out.json> <dump.tsv> [...] | check <dump.tsv> <out.json> | --selftest).
Python 3 stdlib only.
"""
import pathlib
import sys

HERE = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import axioms_gate as g  # noqa: E402

g.ROOTS = g.ROOTS + ["E2eList"]
g.LISTS = g.LISTS + [HERE / "AxiomsLv.lean", HERE / "AxiomsLvT3.lean"]

if __name__ == "__main__":
    sys.argv[0] = __file__
    a = sys.argv[1:]
    if a == ["--selftest"]:
        sys.exit(g.selftest())
    if a[:1] == ["check"] and len(a) == 3:
        sys.exit(g.cmd_check(a[1], a[2]))
    if a[:1] == ["run"] and len(a) >= 3:
        xp, xm, rest = [], [], a[3:]
        while rest:
            if rest[0] == "--extra-lean-path":
                xp.append(rest[1])
            elif rest[0] == "--extra-module":
                xm.append(rest[1])
            else:
                sys.exit(__doc__)
            rest = rest[2:]
        sys.exit(g.cmd_run(a[1], a[2], xp, xm))
    sys.exit(__doc__)
