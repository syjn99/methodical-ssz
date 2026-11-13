#!/usr/bin/env python3
"""lean/Prysm/ElfData/SyncAggregateAndSyncCommitteeReader.lean's data reader is the text of lean/Prysm/ElfData/CheckpointAndEpochReader.lean's reader.

Usage: lvcheck_include.py      (from any cwd; Python 3 standard library only)
A new file with the method of `check_include.py` (not changed): compares the bodies of e2eHexByte?,
e2eLabelTerm, e2eDataSource (Checkpoint and Epoch reader) with lvHexByte?, lvLabelTerm, lvDataSource (SyncAggregate and SyncCommittee reader) after renaming
the three names, and the elab bodies after renaming the command, the error prefix and the data path.
Exit 1 on a difference.
"""
import pathlib
import sys

L = pathlib.Path(__file__).resolve().parents[2] / "lean"
e2 = (L / "Prysm" / "ElfData" / "CheckpointAndEpochReader.lean").read_text()
lv = (L / "Prysm" / "ElfData" / "SyncAggregateAndSyncCommitteeReader.lean").read_text()


def block(text, start):
    i = text.index(start)
    j = text.find("\n\n", i)
    return text[i:j if j >= 0 else len(text)]


ok = True
names = (("e2eHexByte?", "lvHexByte?"), ("e2eLabelTerm", "lvLabelTerm"), ("e2eDataSource", "lvDataSource"))
for o, n in names:
    x = block(e2, f"meta def {o}")
    y = block(lv, f"meta def {n}")
    for o2, n2 in names:
        x = x.replace(o2, n2)
    same = x == y
    ok &= same
    print(("SAME" if same else "DIFF"), f"meta def {n}")
x = block(e2, 'elab "e2e_data_include "')
y = block(lv, 'elab "lv_data_include "')
x = x.replace("e2e_data_include", "lv_data_include").replace("e2eDataSource", "lvDataSource") \
     .replace("../prysm/go1.26.10/e2e/link/data/", "../prysm/go1.26.10/e2e/lv/link/data/")
same = x == y
ok &= same
print(("SAME" if same else "DIFF"), "elab lv_data_include")
sys.exit(0 if ok else 1)
