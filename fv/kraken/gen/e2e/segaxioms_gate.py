#!/usr/bin/env python3
"""The axioms gate (`axioms_gate.py`, not changed) over E2e, E2eAd, E2eScal, E2eList, E2eHb, E2eSeg AND E2eDep.

Usage (one gated job, Lean env; the cwd does not matter):
  hbaxioms_gate.py run <out.json> <dump.tsv> [--extra-lean-path DIR --extra-module M]...
  hbaxioms_gate.py check <dump.tsv> <out.json>
  hbaxioms_gate.py --selftest
The text of `hbaxioms_gate.py` (not changed): it imports `axioms_gate.py` and only widens two module constants before
the call: ROOTS gets "E2eList", "E2eHb", "E2eSeg" and "E2eDep" (module list, precheck `lake build --no-build`, `decl_dump.lean --root`) and
LISTS gets the list/vector, HistoricalBatch and segment-lemma hand lists. Every
other line of the gate is the existing code. Python 3 stdlib only.
"""
import pathlib
import sys

HERE = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import axioms_gate as g  # noqa: E402

g.ROOTS = g.ROOTS + ["E2eList", "E2eHb", "E2eSeg", "E2eDep"]
g.LISTS = g.LISTS + [HERE / "AxiomsLv.lean", HERE / "AxiomsHb.lean", HERE / "AxiomsSeg.lean"]

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
