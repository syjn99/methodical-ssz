#!/usr/bin/env python3
"""Diff the 698c202 outputs against the committed Prysm files and classify the changes.

Usage: gendiff.py <prysm-tree> <gen-dir> <out-dir>
  <gen-dir>/{mainnet,minimal}/*.ssz.go are the new outputs. The committed twin
  is <prysm-tree>/<package dir>/<same name>, read through `git show HEAD:` so a
  file already replaced in the work tree does not matter.
Writes <out-dir>/<preset>/<file>.diff and <out-dir>/gendiff.json.

A change block is a run of +/- lines. The rules are the three generator
commits that the prysm-fv-pin-smoke run found (its tools/classify_hunks.py);
they are rewritten here, not imported. A block that matches no rule is
"unclassified" and needs a reading by hand.
Python 3 standard library only. Run with python3 -I.
"""
import difflib
import json
import os
import re
import subprocess
import sys

RULES = [
    ("b51620a", "drop unreachable first-offset bound check",
     lambda a, r: not a and len(r) == 3 and re.fullmatch(r"\tif sszVarOffset\d+ > size \{", r[0])
     and r[1] == "\t\treturn ssz.ErrOffset" and r[2] == "\t}"),
    # The same three deleted lines, aligned one line earlier by difflib: the
    # line before the check is also "\t}", so the deleted text is identical.
    ("b51620a", "drop unreachable first-offset bound check (diff aligned one line earlier)",
     lambda a, r: not a and len(r) == 3 and r[0] == "\t}" and re.fullmatch(r"\tif sszVarOffset\d+ > size \{", r[1])
     and r[2] == "\t\treturn ssz.ErrOffset"),
    ("f0b85c7", "ValidateBitvector on marshal",
     lambda a, r: not r and len(a) == 3 and re.fullmatch(r"\tif err = ssz\.ValidateBitvector\(c\.\w+, \d+\); err != nil \{", a[0])
     and re.fullmatch(r'\t\treturn nil, fmt\.Errorf\("\w+: %w", err\)', a[1]) and a[2] == "\t}"),
    ("f0b85c7", "ValidateBitvector on unmarshal",
     lambda a, r: not r and len(a) == 3 and re.fullmatch(r"\tif err = ssz\.ValidateBitvector\(sszSlice\d+, \d+\); err != nil \{", a[0])
     and re.fullmatch(r'\t\treturn fmt\.Errorf\("\w+: %w", err\)', a[1]) and a[2] == "\t}"),
    ("280b752", "Bitlist marshal length in bits (ValidateBitlist)",
     lambda a, r: len(a) == 2 and len(r) == 2
     and (m1 := re.fullmatch(r"\tif len\(c\.(\w+)\) > (\d+) \{", r[0])) is not None
     and r[1] == "\t\treturn nil, ssz.ErrListTooBig"
     and (m2 := re.fullmatch(r"\tif err = ssz\.ValidateBitlist\(c\.(\w+), (\d+)\); err != nil \{", a[0])) is not None
     and m1.group(1) == m2.group(1)
     and re.fullmatch(r'\t\treturn nil, fmt\.Errorf\("\w+: %w", err\)', a[1])),
]
PKGDIR = {"engine": "proto/engine/v1"}


def blocks(old, new):
    out = []
    sm = difflib.SequenceMatcher(a=old, b=new, autojunk=False)
    for tag, i1, i2, j1, j2 in sm.get_opcodes():
        if tag != "equal":
            out.append({"removed": old[i1:i2], "added": new[j1:j2], "old_line": i1 + 1})
    return out


def main():
    tree, gen, outdir = sys.argv[1:4]
    res = {"schema": "fvphase1c.gendiff/1", "rules": [{"commit": c, "title": t} for c, t, _ in RULES], "files": []}
    for preset in ("mainnet", "minimal"):
        os.makedirs(f"{outdir}/{preset}", exist_ok=True)
        for name in sorted(os.listdir(f"{gen}/{preset}")):
            cfg = name.split(".")[0]
            rel = f"{PKGDIR.get(cfg, 'proto/prysm/v1alpha1')}/{name}"
            old = subprocess.run(["git", "-C", tree, "show", f"HEAD:{rel}"], check=True,
                                 capture_output=True, text=True).stdout.split("\n")
            new = open(f"{gen}/{preset}/{name}").read().split("\n")
            udiff = "\n".join(difflib.unified_diff(old, new, f"a/{rel}", f"b/{rel}", lineterm=""))
            with open(f"{outdir}/{preset}/{name}.diff", "w") as f:
                f.write(udiff + ("\n" if udiff else ""))
            bl = []
            for b in blocks(old, new):
                hits = [(c, t) for c, t, fn in RULES if fn(b["added"], b["removed"])]
                b["status"] = "classified" if len(hits) == 1 else ("ambiguous" if hits else "unclassified")
                b["commit"] = hits[0][0] if len(hits) == 1 else None
                b["rule"] = hits[0][1] if len(hits) == 1 else None
                bl.append(b)
            per = {}
            for b in bl:
                if b["commit"]:
                    per[b["commit"]] = per.get(b["commit"], 0) + 1
            res["files"].append({"preset": preset, "file": rel, "identical": not bl, "blocks": len(bl),
                                 "classified": sum(b["status"] == "classified" for b in bl),
                                 "unclassified": sum(b["status"] != "classified" for b in bl),
                                 "per_commit": per, "unclassified_blocks": [b for b in bl if b["status"] != "classified"]})
    fs = res["files"]
    res["totals"] = {"files": len(fs), "identical_files": sum(f["identical"] for f in fs),
                     "blocks": sum(f["blocks"] for f in fs), "classified": sum(f["classified"] for f in fs),
                     "unclassified": sum(f["unclassified"] for f in fs),
                     "per_commit": {c: sum(f["per_commit"].get(c, 0) for f in fs) for c in sorted({r[0] for r in RULES})}}
    with open(f"{outdir}/gendiff.json", "w") as f:
        json.dump(res, f, indent=1)
        f.write("\n")
    print(json.dumps(res["totals"]))
    for f in fs:
        print(f["preset"], f["file"], "blocks", f["blocks"], "unclassified", f["unclassified"], f["per_commit"])


if __name__ == "__main__":
    main()
