#!/usr/bin/env python3
"""Controls of the witness generator boundary (X3).

Usage: test_wit.py <regen-dir> <scratch-dir> <out.json>
  <regen-dir>: an output of `run.py gen` (regen.json inside)
1. symbolic length: a generated text whose block gets one piece of unknown length (`z 24` -> `z n`)
   is refused by wgen.write and no file is written;
2. lean/Fk: wgen.write with $GEN_WIT_OUT = lean/Fk is refused and no file is written;
3. run.py gen into a non-empty directory is refused;
4. normalize.py is idempotent and leaves no `(N : BitVec 64)` / `BitVec.ofNat 64 N` atom.
Python 3 standard library only. Run with python3 -I -B.
"""
import json
import os
import re
import subprocess
import sys

sys.dont_write_bytecode = True
HERE = os.path.dirname(os.path.abspath(__file__))
SRC = os.path.join(HERE, "src")
FK = os.path.normpath(os.path.join(HERE, "..", "..", "lean", "Fk"))
sys.path.insert(0, HERE)
import normalize  # noqa: E402

CALL = ("import sys; sys.path.insert(0, sys.argv[1]); import wgen; "
        "wgen.write(sys.argv[2], open(sys.argv[3]).read())")


def write_via_wgen(out, name, text_path):
    env = dict(os.environ, GEN_WIT_OUT=out)
    return subprocess.run([sys.executable, "-I", "-B", "-c", CALL, SRC, f"Fk/{name}", text_path],
                          env=env, capture_output=True, text=True)


def main(regen, scratch, out_json):
    os.makedirs(scratch, exist_ok=True)
    checks = []
    base = open(os.path.join(regen, "WitSzLu.lean")).read()
    m = re.search(r"^def block[^\n]*:=\n(.*?)\n\n", base, re.S | re.M)
    assert m and "(z 24)" in m[1], "control base changed"
    sym = base[:m.start(1)] + m[1].replace("(z 24)", "(z n)", 1) + base[m.end(1):]
    sp = os.path.join(scratch, "sym.lean.txt")
    open(sp, "w").write(sym)
    o1 = os.path.join(scratch, "o1")
    os.makedirs(o1, exist_ok=True)
    r1 = write_via_wgen(o1, "WitSymCtl.lean", sp)
    checks.append({"id": "symbolic-length", "refused": r1.returncode != 0 and "symbolic length refused" in r1.stderr,
                   "no_file": not os.path.exists(os.path.join(o1, "WitSymCtl.lean")), "stderr": r1.stderr.strip().splitlines()[-1:]})
    tw = os.path.join(scratch, "twin.lean.txt")
    open(tw, "w").write(base)
    r1c = write_via_wgen(o1, "WitTwinCtl.lean", tw)
    checks.append({"id": "symbolic-length twin (unchanged text)", "refused": r1c.returncode != 0,
                   "no_file": not os.path.exists(os.path.join(o1, "WitTwinCtl.lean")), "expect": "written"})
    r2 = write_via_wgen(FK, "WitZzGuardCtl.lean", tw)
    checks.append({"id": "lean/Fk", "refused": r2.returncode != 0 and "refusing to write" in r2.stderr,
                   "no_file": not os.path.exists(os.path.join(FK, "WitZzGuardCtl.lean"))})
    r3 = subprocess.run([sys.executable, "-I", "-B", os.path.join(HERE, "run.py"), "gen", regen], capture_output=True, text=True)
    checks.append({"id": "non-empty out", "refused": r3.returncode != 0 and "not empty" in (r3.stderr + r3.stdout), "no_file": True})
    t, n = normalize.normalize(base)
    t2, n2 = normalize.normalize(t)
    left = re.findall(r"\((?:0x[0-9a-fA-F]+|\d+) : BitVec 64\)|BitVec\.ofNat 64 (?:0x[0-9a-fA-F]+|\d+)\b", t)
    checks.append({"id": "normalize", "rewritten": n, "idempotent": n2 == 0 and t2 == t, "atoms_left": len(left)})
    ok = (checks[0]["refused"] and checks[0]["no_file"] and not checks[1]["refused"] and not checks[1]["no_file"]
          and checks[2]["refused"] and checks[2]["no_file"] and checks[3]["refused"]
          and checks[4]["rewritten"] > 0 and checks[4]["idempotent"] and checks[4]["atoms_left"] == 0)
    res = {"schema": "fvphase1c.wit-test/1", "all_ok": ok, "checks": checks}
    s = json.dumps(res, indent=1).replace(scratch + "/", "").replace(regen + "/", "")
    open(out_json, "w").write(s)
    print(s)
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main(*sys.argv[1:4]))
