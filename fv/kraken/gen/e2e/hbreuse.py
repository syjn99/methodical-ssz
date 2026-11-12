#!/usr/bin/env python3
"""HB stream: line-level reuse of the T2 (SyncCommittee) proof files in the HB (HistoricalBatch) files.

Usage: python3 -I -B gen/e2e/hbreuse.py            (cwd = fv/kraken; Python 3 stdlib only; prints a Markdown table)

For each HB file and its T2 source file(s), every non-blank HB line is put in one class:
  verbatim    the stripped line occurs in the T2 source(s) as is;
  mechanical  not verbatim, but equal to a T2 line after the normalization below (renames and numerals);
  new         neither.
Normalization: the rename map RENAME (T2 name -> HB name, applied to the T2 side), then every decimal or hex
numeral -> '#', then whitespace collapsed. Comment lines (starting with '--', '/-', '-/' or inside a /- -/ block)
are counted in their own column and not classified. A line match is per line, without order: it shows how much
text was carried over, not that the proof structure is the same. "Imported" counts the T2 lines of the
declarations that HB uses by `import` (not copied); they are not in the HB files.
"""
import pathlib
import re

KR = pathlib.Path(__file__).resolve().parents[2]
T2 = KR / "lean" / "E2eList"
HB = KR / "lean" / "E2eHb"
GEN = KR / "gen" / "e2e"

PAIRS = [
    ("lean/E2eHb/Code.lean", ["lean/E2eList/Code.lean"]),
    ("lean/E2eHb/Defs.lean", ["lean/E2eList/Defs.lean", "lean/E2eList/Desc.lean"]),
    ("lean/E2eHb/StmtHb.lean", ["lean/E2eList/StmtSc.lean"]),
    ("lean/E2eHb/HbReject.lean", ["lean/E2eList/ScReject.lean"]),
    ("lean/E2eHb/HbLemmas.lean", ["lean/E2eList/ScLemmas.lean"]),
    ("lean/E2eHb/HbLoop1.lean", ["lean/E2eList/ScLoop.lean"]),
    ("lean/E2eHb/HbLoop2.lean", ["lean/E2eList/ScLoop.lean"]),
    ("lean/E2eHb/HbAccept.lean", ["lean/E2eList/ScAccept.lean"]),
    ("lean/E2eHb/HbSpec.lean", ["lean/E2eList/ScSpec.lean"]),
    ("lean/E2eHb/HbSpecK.lean", ["lean/E2eList/ScSpecK.lean"]),
    ("lean/E2eHb/HbSpecChecker.lean", ["lean/E2eList/ScSpecChecker.lean"]),
    ("lean/E2eHb/HbDescEq.lean", ["lean/E2eList/ScDescEq.lean"]),
    ("lean/E2eHb/WitHbA.lean", ["lean/E2eList/WitScA.lean"]),
    ("gen/e2e/hblink.py", ["gen/e2e/lvlink.py"]),
    ("gen/e2e/hbaxioms_gate.py", ["gen/e2e/lvaxioms_gate.py"]),
    ("gen/e2e/AxiomsHb.lean", ["gen/e2e/AxiomsLv.lean"]),
]

RENAME = [
    ("ScUnmarshal", "HbUnmarshal"), ("SyncCommittee", "HistoricalBatch"), ("StmtSc", "StmtHb"),
    ("E2eList.Sc", "E2eHb.Hb"), ("E2eList.WitScA", "E2eHb.WitHbA"), ("WitScA", "WitHbA"),
    ("sc_e2e_", "hb_e2e_"), ("sc_accept_runs", "hb_accept_runs"), ("sc_iter", "hb_iter1"),
    ("sc_exit", "hb_exit1"), ("sc_loop", "hb_loop1"), ("sc_accept", "hb_accept"), ("sc_reject", "hb_reject"),
    ("psc_spec", "phb_spec"), ("psc_", "phb_"), ("prysmScDesc", "prysmHbDesc"), ("scCheckerDesc", "hbCheckerDesc"),
    ("scChecker", "hbChecker"), ("scIn_split", "hbIn_split"), ("scA_split", "hbA_split"), ("scA_join", "hbA_join"),
    ("lv_flatten_length", "hb_flatten_length"), ("PSc", "PHb"), ("pscEnc", "phbEnc"), ("pks", "brs"),
    ("toV48", "toV32"), ("bv48", "bv32"), ("v48", "v32"), ("namespace E2eList", "namespace E2eHb"),
    ("end E2eList", "end E2eHb"), ("E2eList.Code", "E2eHb.Code"), ("AxiomsLv", "AxiomsHb"), ("LV", "HB"),
]


def norm(line, rename):
    if rename:
        for a, b in RENAME:
            line = line.replace(a, b)
    line = re.sub(r"0x[0-9a-fA-F]+|\d+", "#", line)
    return " ".join(line.split())


def lines(p):
    out, block = [], False
    for raw in (KR / p).read_text().split("\n"):
        s = raw.strip()
        if not s:
            continue
        if p.endswith(".py"):
            com = block or s.startswith("#") or s.startswith('"""')
            if s.count('"""') == 1:
                block = not block
        else:
            com = block or s.startswith(("--", "/-", "-/"))
            if s.startswith("/-") and "-/" not in s:
                block = True
            elif block and "-/" in s:
                block = False
        out.append((s, com))
    return out


def measure(hb, srcs):
    src = [s for p in srcs for s, c in lines(p) if not c]
    exact = set(src)
    mech = {norm(s, True) for s in src}
    v = m = n = c = 0
    for s, com in lines(hb):
        if com:
            c += 1
        elif s in exact:
            v += 1
        elif norm(s, False) in mech:
            m += 1
        else:
            n += 1
    return v, m, n, c


def main():
    print("| HB file | T2 source | verbatim | mechanical | new | comment/doc |")
    print("| --- | --- | --- | --- | --- | --- |")
    tot = [0, 0, 0, 0]
    for hb, srcs in PAIRS:
        r = measure(hb, srcs)
        tot = [a + b for a, b in zip(tot, r)]
        print(f"| `{hb}` | {', '.join('`' + s + '`' for s in srcs)} | {r[0]} | {r[1]} | {r[2]} | {r[3]} |")
    print(f"| total | | {tot[0]} | {tot[1]} | {tot[2]} | {tot[3]} |")
    # second loop against the first HB loop (its actual source; not in the total)
    r = measure("lean/E2eHb/HbLoop2.lean", ["lean/E2eHb/HbLoop1.lean"])
    print(f"| `lean/E2eHb/HbLoop2.lean` | `lean/E2eHb/HbLoop1.lean` (not in total) | {r[0]} | {r[1]} | {r[2]} | {r[3]} |")


if __name__ == "__main__":
    main()
