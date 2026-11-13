#!/usr/bin/env python3
"""lean/Prysm/ElfData/CheckpointAndEpochReader.lean's data reader is the text of lean/Machine/Include.lean's reader.

Usage: check_include.py      (from any cwd; Python 3 standard library only)
Also compares lean/Prysm/ElfData/AttestationDataReader.lean (prefix `ad`, AttestationData data directory) with the Checkpoint and Epoch reader.
Compares the bodies of hexByte?, labelTerm, dataSource (Machine) with e2eHexByte?, e2eLabelTerm,
e2eDataSource (Checkpoint and Epoch reader) after renaming the three names, and the elab bodies after renaming the command,
the error prefix and the data path. Exit 1 on a difference.
"""
import pathlib
import re
import sys

L = pathlib.Path(__file__).resolve().parents[2] / "lean"
fk = (L / "Machine" / "Include.lean").read_text()
e2 = (L / "Prysm" / "ElfData" / "CheckpointAndEpochReader.lean").read_text()


def block(text, start):
    i = text.index(start)
    j = text.find("\n\n", i)
    return text[i:j if j >= 0 else len(text)]


ok = True
for a, b in (("meta def hexByte?", "meta def e2eHexByte?"), ("meta def labelTerm", "meta def e2eLabelTerm"),
             ("meta def dataSource", "meta def e2eDataSource")):
    x = block(fk, a)
    y = block(e2, b)
    for o, n in (("hexByte?", "e2eHexByte?"), ("labelTerm", "e2eLabelTerm"), ("dataSource", "e2eDataSource")):
        x = re.sub(rf"(?<![A-Za-z0-9]){re.escape(o)}", n, x)
    same = x == y
    ok &= same
    print(("SAME" if same else "DIFF"), b)
x = block(fk, 'elab "data_include "')
y = block(e2, 'elab "e2e_data_include "')
x = x.replace("data_include", "e2e_data_include").replace("dataSource", "e2eDataSource") \
     .replace("../link/out/data/", "../prysm/go1.26.10/e2e/link/data/")
same = x == y
ok &= same
print(("SAME" if same else "DIFF"), "elab e2e_data_include")
# Prysm/ElfData/AttestationDataReader.lean (AttestationData link set): the Checkpoint and Epoch reader with the prefix `ad`
ad = (L / "Prysm" / "ElfData" / "AttestationDataReader.lean").read_text()
for a, b in (("meta def e2eHexByte?", "meta def adHexByte?"), ("meta def e2eLabelTerm", "meta def adLabelTerm"),
             ("meta def e2eDataSource", "meta def adDataSource")):
    x = block(e2, a)
    y = block(ad, b)
    for o, n in (("e2eHexByte?", "adHexByte?"), ("e2eLabelTerm", "adLabelTerm"), ("e2eDataSource", "adDataSource")):
        x = x.replace(o, n)
    same = x == y
    ok &= same
    print(("SAME" if same else "DIFF"), b)
x = block(e2, 'elab "e2e_data_include "')
y = block(ad, 'elab "ad_data_include "')
x = x.replace("e2e_data_include", "ad_data_include").replace("e2eDataSource", "adDataSource") \
     .replace("../prysm/go1.26.10/e2e/link/data/", "../prysm/go1.26.10/e2e/ad/link/data/")
same = x == y
ok &= same
print(("SAME" if same else "DIFF"), "elab ad_data_include")
sys.exit(0 if ok else 1)
