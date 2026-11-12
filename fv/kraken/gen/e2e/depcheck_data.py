#!/usr/bin/env python3
"""SEG (Deposit): lean/E2eDep/Code.lean's hand definition `depDataType_addr` equals the address that the LV data
reader would produce from prysm/go1.26.10/e2e/lv/link-dep/data/depDataType.data.

Usage: depcheck_data.py [--selftest]      (from any cwd; Python 3 standard library only)
The reader (`lvLabelTerm` in lean/E2eList/Include.lean, not changed) turns the line `at <label> <off>` into
`(label "<label>" + <off>).toBitVec` (or `(label "<label>").toBitVec` for off = 0). This script reads the `at` line,
renders that term with the same rule, and compares it with the right-hand side of the Lean definition.
`check.py` (f) compares the data file with the ELF (lv/link-dep/RESULT). Exit 1 on a difference.
--selftest: the same comparison against a changed offset must fail (exit 0 if it does).
"""
import pathlib
import re
import sys

KR = pathlib.Path(__file__).resolve().parents[2]
DATA = KR / "prysm/go1.26.10/e2e/lv/link-dep/data/depDataType.data"
CODE = KR / "lean/E2eDep/Code.lean"


def label_term(lab, off):
    return f'(label "{lab}").toBitVec' if off == 0 else f'(label "{lab}" + {off}).toBitVec'


def expected(text):
    for line in text.splitlines():
        ws = line.split()
        if ws and ws[0] == "at":
            return label_term(ws[1], int(ws[2]))
    raise SystemExit("no `at` line")


def actual(text):
    m = re.search(r"^def depDataType_addr \[Host\] : BitVec 64 := (.+)$", text, re.M)
    if not m:
        raise SystemExit("no depDataType_addr definition")
    return m.group(1).strip()


def main():
    e, a = expected(DATA.read_text()), actual(CODE.read_text())
    if "--selftest" in sys.argv:
        bad = e.replace("1421952", "1421953")
        ok = bad != a
        print("SELFTEST", "PASS (planted offset differs)" if ok else "FAIL")
        return 0 if ok else 1
    print(("SAME" if e == a else "DIFF"), "depDataType_addr", a, "| data:", e)
    return 0 if e == a else 1


if __name__ == "__main__":
    sys.exit(main())
