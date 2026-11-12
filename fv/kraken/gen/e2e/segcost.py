#!/usr/bin/env python3
"""SEG: hand code lines (not blank, not comment) per part of the Deposit port, for REPORT-SEG.md §7.

Usage: python3 -I -B gen/e2e/segcost.py      (cwd = fv/kraken; Python 3 stdlib only; imports hbreuse.py, unchanged)
The accept proof is cut at its own section comments: helpers (before `theorem dep_e2e_accept_main`), head (to
`-- the Proof loop`), loop use (to `-- 84–86`), Data object and delegate call (the rest).
"""
import os
import pathlib
import sys
import tempfile

HERE = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import hbreuse as h  # noqa: E402

KR = HERE.parents[1]


def code_lines(p, lo=None, hi=None):
    text = (KR / p).read_text().split("\n")
    a = 0 if lo is None else next(i for i, l in enumerate(text) if lo in l)
    b = len(text) if hi is None else next(i for i, l in enumerate(text) if hi in l)
    # review r5 S9: the slice goes to a temporary directory outside the repository
    with tempfile.TemporaryDirectory() as d:
        tmp = pathlib.Path(d) / "slice.lean"
        tmp.write_text("\n".join(text[a:b]))
        return sum(1 for _, c in h.lines(str(tmp)) if not c)


ACC = "lean/E2eDep/Accept.lean"
PARTS = [
    ("statement (machine)", [("lean/E2eDep/Stmt.lean", None, None)]),
    ("statement (spec) + hand Desc", [("lean/E2eDep/SpecStmt.lean", None, None)]),
    ("size reject proof", [("lean/E2eDep/Reject.lean", None, None)]),
    ("accept: helpers (scratch split, object split)", [(ACC, None, "theorem dep_e2e_accept_main")]),
    ("accept: head steps (directives 0–40)", [(ACC, "theorem dep_e2e_accept_main", "-- the Proof loop")]),
    ("accept: loop use (block facts, v32_loop call)", [(ACC, "-- the Proof loop", "-- 84–86")]),
    ("accept: Data object, delegate call, epilogue", [(ACC, "-- 84–86", None)]),
    ("spec bridge + companions + Desc equality", [("lean/E2eDep/Spec.lean", None, None),
                                                  ("lean/E2eDep/SpecK.lean", None, None),
                                                  ("lean/E2eDep/DescEq.lean", None, None)]),
    ("witnesses (reject, accept) + newobject model", [("lean/E2eDepW/WitR.lean", None, None),
                                                      ("lean/E2eDepW/WitA.lean", None, None),
                                                      ("lean/E2eDepW/BumpNew120.lean", None, None)]),
    ("code include", [("lean/E2eDep/Code.lean", None, None)]),
    ("link script", [("gen/e2e/deplink.py", None, None)]),
]


def main():
    print("Scope: hand code lines (not blank, not comment) of the Deposit port, all files written for it; "
          "reference: none (absolute counts, not a diff).")
    print("| part | code lines |")
    print("| --- | --- |")
    tot = 0
    for name, fs in PARTS:
        n = sum(code_lines(p, a, b) for p, a, b in fs)
        tot += n
        print(f"| {name} | {n} |")
    print(f"| total | {tot} |")


if __name__ == "__main__":
    main()
