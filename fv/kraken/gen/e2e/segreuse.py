#!/usr/bin/env python3
"""SEG stream: line counts for REPORT-SEG.md. Python 3 stdlib only; cwd = fv/kraken.

Usage: python3 -I -B gen/e2e/segreuse.py

1. The Deposit files (proof of use) against their HB sources, with `hbreuse.py`'s classification (verbatim,
   mechanical after renames and numerals, new; comment/doc lines apart). `hbreuse.py` is imported, not changed.
2. Code lines (not blank, not comment) of the general files and of the hand files they replace.
"""
import pathlib
import sys

HERE = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import hbreuse as h  # noqa: E402

h.RENAME = [("HbUnmarshal", "DepUnmarshal"), ("HistoricalBatch", "Deposit"), ("E2eHb", "E2eDep"),
            ("hb_e2e_", "dep_e2e_"), ("hb_accept", "dep_accept"), ("hb_reject", "dep_reject"), ("hbL", "depL"),
            ("hbN", "depN"), ("StmtHb", "Stmt"), ("hblink", "deplink")]

PAIRS = [
    ("lean/E2eDep/Code.lean", ["lean/E2eHb/Code.lean"]),
    ("lean/E2eDep/Stmt.lean", ["lean/E2eHb/StmtHb.lean"]),
    ("lean/E2eDep/Reject.lean", ["lean/E2eHb/HbReject.lean"]),
    ("lean/E2eDep/Accept.lean", ["lean/E2eHb/HbAccept.lean", "lean/E2eSeg/V32Hb.lean"]),
    ("gen/e2e/deplink.py", ["gen/e2e/hblink.py"]),
]
GENERAL = ["lean/E2eSeg/ListG.lean", "lean/E2eSeg/SegG.lean", "lean/E2eSeg/V32.lean", "lean/E2eSeg/V32Loop.lean",
           "lean/E2eSeg/RejG.lean"]
INSTANCES = ["lean/E2eSeg/ListGInst.lean", "lean/E2eSeg/SegGInst.lean", "lean/E2eSeg/V32Hb.lean",
             "lean/E2eSeg/RejGInst.lean"]
REPLACED = ["lean/E2eList/ScLemmas.lean", "lean/E2eHb/HbLemmas.lean", "lean/E2eScal/SegN.lean",
            "lean/E2eList/Seg.lean", "lean/E2eHb/HbLoop1.lean", "lean/E2eHb/HbLoop2.lean", "lean/E2eHb/HbReject.lean",
            "lean/E2eList/ScReject.lean"]


def code(p):
    return sum(1 for _, c in h.lines(p) if not c)


def main():
    print("| Deposit file | source | verbatim | mechanical | new | comment/doc |")
    print("| --- | --- | --- | --- | --- | --- |")
    tot = [0, 0, 0, 0]
    for f, srcs in PAIRS:
        r = h.measure(f, srcs)
        tot = [a + b for a, b in zip(tot, r)]
        print(f"| `{f}` | {', '.join('`' + s + '`' for s in srcs)} | {r[0]} | {r[1]} | {r[2]} | {r[3]} |")
    print(f"| total | | {tot[0]} | {tot[1]} | {tot[2]} | {tot[3]} |")
    print()
    print("| group | file | code lines |")
    print("| --- | --- | --- |")
    for g, fs in (("general", GENERAL), ("instances", INSTANCES), ("hand (replaced)", REPLACED)):
        for f in fs:
            print(f"| {g} | `{f}` | {code(f)} |")


if __name__ == "__main__":
    main()
