#!/usr/bin/env python3
"""phase1c witness generator (X3): the fix3 `tools/wit` generators run from this tree.

Usage (any cwd; run through the gate):
  run.py config                 write gen/wit/config.json from src/wgen.py ALL and src/README.md
  run.py gen <out-dir>          run every configured generator into <out-dir> (must not exist or be
                                empty; never lean/Fk), then compare every output with lean/Fk/<name>
                                -> <out-dir>/regen.json
  run.py gen <out-dir> --only WitX[,WitY]   only the invocations that write these modules

src/ holds byte copies of fv/kraken/lean/tools/wit at the fix3 stage A base (src/SOURCES.sha256).
The one change is `wgen.write`: it writes into $GEN_WIT_OUT. The generators read
../link/out/norm/*.S relative to their cwd, so they run with cwd fv/kraken/lean (read only).
Python 3 standard library only. Run with python3 -I.
"""
import hashlib
import json
import os
import re
import subprocess
import sys

sys.dont_write_bytecode = True
HERE = os.path.dirname(os.path.abspath(__file__))
SRC = os.path.join(HERE, "src")
KRAKEN = os.path.normpath(os.path.join(HERE, "..", ".."))
LEAN = os.path.join(KRAKEN, "lean")
FK = os.path.join(LEAN, "Fk")
CONFIG = os.path.join(HERE, "config.json")


def sha(p):
    return hashlib.sha256(open(p, "rb").read()).hexdigest()


def sources_ok():
    """src/ must still be the recorded copies (wgen.py: the recorded copy plus the write change)."""
    bad = []
    for line in open(os.path.join(SRC, "SOURCES.sha256")):
        h, name = line.split()
        if name != "wgen.py" and sha(os.path.join(SRC, name)) != h:
            bad.append(name)
    return bad


def make_config():
    src = open(os.path.join(SRC, "wgen.py")).read()
    allv = re.search(r'ALL = """(.*?)"""', src, re.S)[1]
    table = {}
    for m in re.finditer(r"^\| (Wit\w+) \| `([^`]+)` \| `([^`]+)`", open(os.path.join(SRC, "README.md")).read(), re.M):
        table[m[1]] = {"readme_generator": m[2], "theorem": m[3]}
    inv = []
    for line in allv.splitlines():
        g, *args = line.split()
        inv.append({"generator": g, "args": args})
    cfg = {"schema": "fvphase1c.wit-config/1",
           "source": "fv/kraken/lean/tools/wit at fix3 stage A (d9cdb40); byte copies in gen/wit/src",
           "invocations": inv, "modules": table,
           "rule": "every invocation runs with cwd fv/kraken/lean and argv[1] = gen/wit/src; outputs go to $GEN_WIT_OUT"}
    json.dump(cfg, open(CONFIG, "w"), indent=1)
    print(json.dumps({"invocations": len(inv), "modules_in_readme": len(table)}))
    return 0


def gen(out, only=None):
    out = os.path.realpath(out)
    fk = os.path.realpath(FK)
    if out == fk or out.startswith(fk + os.sep):
        raise SystemExit(f"refusing to write into {fk}")
    if os.path.exists(out) and os.listdir(out):
        raise SystemExit(f"{out}: exists and is not empty")
    os.makedirs(out, exist_ok=True)
    bad = sources_ok()
    if bad:
        raise SystemExit(f"gen/wit/src differs from SOURCES.sha256: {bad}")
    cfg = json.load(open(CONFIG))
    env = dict(os.environ, GEN_WIT_OUT=out, PYTHONDONTWRITEBYTECODE="1")
    runs = []
    for iv in cfg["invocations"]:
        wl = os.path.join(out, ".written")
        before = open(wl).read().split() if os.path.exists(wl) else []
        r = subprocess.run([sys.executable, "-I", "-B", os.path.join(SRC, iv["generator"] + ".py"), SRC] + iv["args"],
                           cwd=LEAN, env=env, capture_output=True, text=True)
        after = open(wl).read().split() if os.path.exists(wl) else []
        runs.append({"generator": iv["generator"], "args": iv["args"], "rc": r.returncode, "wrote": after[len(before):],
                     "stderr_tail": r.stderr.strip().splitlines()[-1:] if r.returncode else []})
    written = [w for r in runs for w in r["wrote"]]
    if only:
        written = [w for w in written if w[:-5] in only]
    fk_files = sorted(f for f in os.listdir(FK) if re.fullmatch(r"Wit\w*\.lean", f))
    files = []
    for f in sorted(set(written)):
        o, h = os.path.join(out, f), os.path.join(FK, f)
        same = os.path.exists(h) and open(o, "rb").read() == open(h, "rb").read()
        files.append({"file": f, "out_sha256": sha(o), "fk_sha256": sha(h) if os.path.exists(h) else None,
                      "byte_identical": same, "times_written": written.count(f)})
    res = {"schema": "fvphase1c.wit-regen/1", "invocations": len(runs), "failed_invocations": [r for r in runs if r["rc"]],
           "files_written": len(set(written)), "byte_identical": sum(f["byte_identical"] for f in files),
           "different": [f["file"] for f in files if not f["byte_identical"]],
           "fk_wit_files": len(fk_files), "fk_wit_files_not_generated": sorted(set(fk_files) - set(written)),
           "written_twice": sorted({f for f in written if written.count(f) > 1}),
           "runs": runs, "files": files}
    json.dump(res, open(os.path.join(out, "regen.json"), "w"), indent=1)
    print(json.dumps({k: v for k, v in res.items() if k not in ("runs", "files")}, indent=1))
    return 0 if not res["failed_invocations"] and not res["different"] else 1


if __name__ == "__main__":
    if sys.argv[1] == "config":
        sys.exit(make_config())
    only = sys.argv[sys.argv.index("--only") + 1].split(",") if "--only" in sys.argv else None
    sys.exit(gen(sys.argv[2], only))
