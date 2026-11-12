#!/usr/bin/env python3
"""IndexedAttestation: lean/E2eList/IncludeIa.lean's data reader is the text of lean/E2eList/Include.lean's reader.

Usage: lvt3check_include.py      (from any cwd; Python 3 standard library only)
A new file with the method of `lvcheck_include.py` (not changed): compares the bodies of lvHexByte?,
lvLabelTerm, lvDataSource (E2eList/Include.lean) with lvt3HexByte?, lvt3LabelTerm, lvt3DataSource
(E2eList/IncludeIa.lean) after renaming the three names, and the elab bodies after renaming the command, the
error prefix and the data path (lv/link-t3/data).
Exit 1 on a difference.
"""
import pathlib
import sys

L = pathlib.Path(__file__).resolve().parents[2] / "lean"
e2 = (L / "E2eList" / "Include.lean").read_text()
lv = (L / "E2eList" / "IncludeIa.lean").read_text()


def block(text, start):
    i = text.index(start)
    j = text.find("\n\n", i)
    return text[i:j if j >= 0 else len(text)]


ok = True
names = (("lvHexByte?", "lvt3HexByte?"), ("lvLabelTerm", "lvt3LabelTerm"), ("lvDataSource", "lvt3DataSource"))
for o, n in names:
    x = block(e2, f"meta def {o}")
    y = block(lv, f"meta def {n}")
    for o2, n2 in names:
        x = x.replace(o2, n2)
    same = x == y
    ok &= same
    print(("SAME" if same else "DIFF"), f"meta def {n}")
x = block(e2, 'elab "lv_data_include "')
y = block(lv, 'elab "lvt3_data_include "')
x = x.replace("lv_data_include", "lvt3_data_include").replace("lvDataSource", "lvt3DataSource") \
     .replace("../prysm/go1.26.10/e2e/lv/link/data/", "../prysm/go1.26.10/e2e/lv/link-t3/data/")
same = x == y
ok &= same
print(("SAME" if same else "DIFF"), "elab lvt3_data_include")
sys.exit(0 if ok else 1)
