#!/usr/bin/env python3
"""Parse the output of `lake env lean <hand list>` into JSON. A hand list is a file of gen/axioms-lists/.
Allowed axioms: propext, Classical.choice, Quot.sound.
Usage: axioms.py <log> <out.json> [<names.lean>]. The default list is gen/axioms-lists/checkpoint-epoch.lean.
The AttestationData set passes gen/axioms-lists/attestation-data.lean.
Exit 1 if any theorem uses another axiom, if a theorem is missing from the output, or if `sorryAx` appears.
axioms.py run <names.lean> <out.json> [<log>]: first `lake build --no-build <imports of names.lean>` in
fv/kraken/lean (`lake env lean` does no trace check); exit 2 if it fails, else run
`lake env lean <names.lean>` and parse as above. The precheck exit code is recorded in <out.json>.
The full gate gen/checks/axioms_gate.py reads every hand list as a "must exist" list."""
import json, pathlib, re, subprocess, sys

LEAN = pathlib.Path(__file__).resolve().parent.parent.parent / "lean"
DEFAULT_LIST = LEAN.parent / "gen" / "axioms-lists" / "checkpoint-epoch.lean"


def parse(log, src, out, extra=None):
    want = re.findall(r"^#print axioms (\S+)\s*$", open(src).read(), re.M)
    ok = {"propext", "Classical.choice", "Quot.sound"}
    res = {}
    # names may contain `'`: match the whole quoted name up to the message text
    for m in re.finditer(r"^'(.+)' depends on axioms: \[([^\]]*)\]", log, re.M):
        res[m[1]] = [a.strip() for a in m[2].split(",") if a.strip()]
    for m in re.finditer(r"^'(.+)' does not depend on any axioms", log, re.M):
        res[m[1]] = []
    missing = [t for t in want if t not in res]
    bad = {t: a for t, a in res.items() if not set(a) <= ok}
    out_d = {"allowed": sorted(ok), "theorems": res, "missing": missing, "nonstandard": bad,
             "count": len(res), "verdict": "PASS" if not missing and not bad and "sorryAx" not in log else "FAIL"}
    if extra:
        out_d.update(extra)
    json.dump(out_d, open(out, "w"), indent=1)
    print(out_d["verdict"], out_d["count"], "missing", missing, "nonstandard", bad)
    return 0 if out_d["verdict"] == "PASS" else 1


def run(src, out, logf=None):
    src = str(pathlib.Path(src).resolve())
    imps = sorted({m for l in open(src).read().splitlines() if l.startswith("import ") for m in l.split()[1:]})
    p = subprocess.run(["lake", "build", "--no-build"] + imps, cwd=LEAN, capture_output=True, text=True)
    fails = [l for l in (p.stdout + p.stderr).splitlines() if l.startswith("- ")]
    pre = {"precheck": {"argv": "lake build --no-build <imports>", "imports": imps, "rc": p.returncode, "failures": fails}}
    print("PRECHECK rc", p.returncode, fails[:10], flush=True)
    if p.returncode != 0:
        json.dump({**pre, "verdict": "FAIL", "reason": "precheck"}, open(out, "w"), indent=1)
        return 2
    r = subprocess.run(["lake", "env", "lean", src], cwd=LEAN, capture_output=True, text=True)
    log = r.stdout + r.stderr
    if logf:
        open(logf, "w").write(log)
    pre["lean_rc"] = r.returncode
    rc = parse(log, src, out, pre)
    return rc if r.returncode == 0 else 1


if __name__ == "__main__":
    if sys.argv[1:2] == ["run"]:
        sys.exit(run(*sys.argv[2:5]))
    log = open(sys.argv[1]).read()
    src = sys.argv[3] if len(sys.argv) > 3 else str(DEFAULT_LIST)
    sys.exit(parse(log, src, sys.argv[2]))
