#!/usr/bin/env python3
"""The Deposit proofs take the address of the `v1alpha1.Deposit_Data` type descriptor from its data file.

Usage: depcheck_data.py [--selftest]      (from any cwd; Python 3 standard library only)
Checks, on the text of the tree:
- lean/Prysm/ElfData/PrysmTarget.lean includes the data file prysm/go1.26.10/link-set/data/typeDeposit_Data.data
  (`prysm_data_include typeDeposit_Data`), and that file exists. The reader turns its `at` line into
  `ElfData.PrysmTarget.typeDeposit_Data_addr`; `check.py` (f) compares the file with the ELF
  (prysm/go1.26.10/link-set/RESULT).
- the modules of lean/Prysm/Deposit/ name `ElfData.PrysmTarget.typeDeposit_Data_addr` and write no hand address term
  `(label "type__" + <offset>)` (an earlier version had a hand definition with that term).
Exit 1 on a failed check.
--selftest: the checks on a copy of the texts with a planted hand definition, and without the include, must fail
(exit 0 if both fail).
"""
import pathlib
import re
import sys

KR = pathlib.Path(__file__).resolve().parents[2]
DATA = KR / "prysm/go1.26.10/link-set/data/typeDeposit_Data.data"
TARGET = KR / "lean/Prysm/ElfData/PrysmTarget.lean"
DEPOSIT = KR / "lean/Prysm/Deposit"


def check(target_text, deposit_texts, data_exists):
    errs = []
    if not re.search(r"^prysm_data_include typeDeposit_Data$", target_text, re.M):
        errs.append("PrysmTarget.lean does not include typeDeposit_Data")
    if not data_exists:
        errs.append(f"no data file {DATA.relative_to(KR)}")
    if not any("ElfData.PrysmTarget.typeDeposit_Data_addr" in t for t in deposit_texts.values()):
        errs.append("no Deposit module names ElfData.PrysmTarget.typeDeposit_Data_addr")
    for name, t in sorted(deposit_texts.items()):
        if re.search(r'\(label "type__" \+ \d+\)', t):
            errs.append(f"{name}: a hand address term (label \"type__\" + ...)")
    return errs


def main():
    target = TARGET.read_text()
    dep = {p.name: p.read_text() for p in sorted(DEPOSIT.glob("*.lean"))}
    if "--selftest" in sys.argv:
        planted = dict(dep)
        planted["Code.lean"] = dep.get("Code.lean", "") + '\ndef hand_address [Host] : BitVec 64 := (label "type__" + 1421952).toBitVec\n'
        a = check(target, planted, True)
        b = check(target.replace("prysm_data_include typeDeposit_Data\n", ""), dep, True)
        ok = bool(a) and bool(b)
        print("SELFTEST", "PASS (planted hand definition and missing include both fail)" if ok else "FAIL", a, b)
        return 0 if ok else 1
    errs = check(target, dep, DATA.exists())
    for e in errs:
        print("FAIL", e)
    if not errs:
        print("SAME typeDeposit_Data_addr: the data include of", DATA.relative_to(KR))
    return 1 if errs else 0


if __name__ == "__main__":
    sys.exit(main())
