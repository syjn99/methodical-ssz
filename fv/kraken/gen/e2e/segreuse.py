#!/usr/bin/env python3
"""Line counts of the Deposit port (reuse and cost tables). Python 3 stdlib only; cwd = fv/kraken.

Usage: python3 -I -B gen/e2e/segreuse.py

1. The Deposit files (proof of use) against their HistoricalBatch sources, with `hbreuse.py`'s classification (verbatim,
   mechanical after renames and numerals, new; comment/doc lines apart). `hbreuse.py` is imported, not changed.
2. Code lines (not blank, not comment) of the general files and of the hand files they replace.
3. Equal scope: the "new" lines of the same file kinds (code include, machine statement, size reject,
   element loop(s), accept, link script) for HistoricalBatch (reference: SyncCommittee sources, rename map SyncCommittee -> HistoricalBatch) and for Deposit
   (reference: HistoricalBatch sources and the general lemmas' instance file, rename map HistoricalBatch -> Deposit). The references and the
   rename maps differ, so the two numbers measure "lines not carried over from the previous type", nothing more.
"""
import pathlib
import sys

HERE = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import hbreuse as h  # noqa: E402

HB_RENAME = list(h.RENAME)  # SyncCommittee -> HistoricalBatch (hbreuse.py)
DEP_RENAME = [("HbUnmarshal", "DepUnmarshal"), ("HistoricalBatch", "Deposit"), ("E2eHb", "E2eDep"),
            ("hb_e2e_", "dep_e2e_"), ("hb_accept", "dep_accept"), ("hb_reject", "dep_reject"), ("hbL", "depL"),
            ("hbN", "depN"), ("StmtHb", "Stmt"), ("hblink", "deplink")]
h.RENAME = DEP_RENAME

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


HB_SCOPE = [
    ("code include", "lean/E2eHb/Code.lean", ["lean/E2eList/Code.lean"]),
    ("machine statement", "lean/E2eHb/StmtHb.lean", ["lean/E2eList/StmtSc.lean"]),
    ("size reject", "lean/E2eHb/HbReject.lean", ["lean/E2eList/ScReject.lean"]),
    ("loop 1", "lean/E2eHb/HbLoop1.lean", ["lean/E2eList/ScLoop.lean"]),
    ("loop 2", "lean/E2eHb/HbLoop2.lean", ["lean/E2eList/ScLoop.lean"]),
    ("accept", "lean/E2eHb/HbAccept.lean", ["lean/E2eList/ScAccept.lean"]),
    ("link script", "gen/e2e/hblink.py", ["gen/e2e/lvlink.py"]),
]


def equal_scope():
    print()
    print("| Scope | HistoricalBatch new (reference SyncCommittee) | Deposit new (reference HistoricalBatch) |")
    print("| --- | --- | --- |")
    h.RENAME = HB_RENAME
    hb = {k: h.measure(f, srcs)[2] for k, f, srcs in HB_SCOPE}
    h.RENAME = DEP_RENAME
    dep = {"code include": h.measure(*PAIRS[0])[2], "machine statement": h.measure(*PAIRS[1])[2],
           "size reject": h.measure(*PAIRS[2])[2], "accept": h.measure(*PAIRS[3])[2],
           "link script": h.measure(*PAIRS[4])[2]}
    for k in ["code include", "machine statement", "size reject", "loop 1", "loop 2", "accept", "link script"]:
        d = dep.get(k, 0 if k.startswith("loop") else None)
        print(f"| {k} | {hb[k]} | {d} (loop: general lemma, no file) |" if k.startswith("loop") else
              f"| {k} | {hb[k]} | {d} |")
    print(f"| total | {sum(hb.values())} | {sum(dep.values())} |")


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
    equal_scope()


if __name__ == "__main__":
    main()
