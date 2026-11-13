#!/usr/bin/env python3
"""lean/Prysm/ElfData/PrysmTargetReader.lean's data reader is the text of lean/Machine/Include.lean's reader.

Usage: check_include.py      (from any cwd; Python 3 standard library only)
Compares the bodies of hexByte?, labelTerm and dataSource of the two modules (both keep them private, with the
same names), and the elab bodies after renaming the command `data_include` to `prysm_data_include` (with the error
prefix) and the data path `../link/out/data/` to `../prysm/go1.26.10/link-set/data/`. Exit 1 on a difference.
"""
import pathlib
import sys

L = pathlib.Path(__file__).resolve().parents[2] / "lean"
fk = (L / "Machine" / "Include.lean").read_text()
pt = (L / "Prysm" / "ElfData" / "PrysmTargetReader.lean").read_text()


def block(text, start):
    i = text.index(start)
    j = text.find("\n\n", i)
    return text[i:j if j >= 0 else len(text)]


ok = True
for name in ("meta def hexByte?", "meta def labelTerm", "meta def dataSource"):
    same = block(fk, name) == block(pt, name)
    ok &= same
    print(("SAME" if same else "DIFF"), name)
x = block(fk, 'elab "data_include "')
y = block(pt, 'elab "prysm_data_include "')
x = x.replace("data_include", "prysm_data_include").replace("../link/out/data/", "../prysm/go1.26.10/link-set/data/")
same = x == y
ok &= same
print(("SAME" if same else "DIFF"), "elab prysm_data_include")
sys.exit(0 if ok else 1)
