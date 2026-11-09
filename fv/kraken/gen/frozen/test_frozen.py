#!/usr/bin/env python3
"""The frozen lists must be reproducible from the repository by program (review phase1c-r2 N1).

Usage: test_frozen.py <repo-root> <scratch-dir>
Runs build_lists.py with --out <scratch-dir> and compares the two files byte by byte with
fv/kraken/gen/frozen/. Also checks that every `sources_sha256` entry of THEOREMS.json is the
sha256 of that file now. Exit status 1 on any difference. Writes nothing into the repository.
Python 3 standard library only. Run with python3 -I.
"""
import hashlib
import json
import os
import subprocess
import sys


def sha(p):
    return hashlib.sha256(open(p, "rb").read()).hexdigest()


def main():
    root, scratch = sys.argv[1:3]
    os.makedirs(scratch, exist_ok=True)
    here = os.path.dirname(os.path.abspath(__file__))
    r = subprocess.run([sys.executable, "-I", f"{here}/build_lists.py", root, "--out", scratch], capture_output=True, text=True)
    res = {"build_rc": r.returncode, "files": {}, "sources": {}}
    for n in ("THEOREMS.json", "ASSUMPTIONS.json"):
        a, b = f"{here}/{n}", f"{scratch}/{n}"
        res["files"][n] = {"committed": sha(a), "regenerated": sha(b) if os.path.exists(b) else None}
    th = json.load(open(f"{here}/THEOREMS.json"))
    for rel, h in th["sources_sha256"].items():
        res["sources"][rel] = {"recorded": h, "now": sha(os.path.join(root, rel))}
    ok = (r.returncode == 0 and all(v["committed"] == v["regenerated"] for v in res["files"].values())
          and all(v["recorded"] == v["now"] for v in res["sources"].values()))
    res["ok"] = ok
    print(json.dumps({"ok": ok, "files": res["files"],
                      "stale_sources": [k for k, v in res["sources"].items() if v["recorded"] != v["now"]]}, indent=1))
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
