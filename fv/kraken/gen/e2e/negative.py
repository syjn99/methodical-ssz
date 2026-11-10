#!/usr/bin/env python3
"""prysm-e2e negative suite: every mutant must fail inside its designated theorem; every control passes.

Usage (run inside one gated job, Lean env, cwd anywhere):
  negative.py <cases.json> <work-dir> <result.json> [<case-id>...]
cases.json: list of {"id", "module" (path under fv/kraken/lean, e.g. "E2e/Epoch.lean"), "theorem",
  "kind": "code" | "stmt" | "control",
  code:  "code_def" (Lean name of the included program, e.g. "EpUnmarshal"), "S" (file under
         prysm/go1.26.10/e2e/link/norm), "old", "new" (one exact instruction line, unique in the file,
         or at the 1-based "line" of the file)
  stmt:  "old", "new" (exact text, unique inside the theorem statement)
  control: optional "code_def"/"S" (then an unmutated copy of the .S is included the same way)}
For each case the mutant Lean file is the module's text up to the end of the designated theorem
(the next top-level `theorem`/`def`/`end`/`example`/`/--` after it is cut), with, for code cases, a
new constant `E2e.Code.<code_def>Mut` that includes the mutated .S copy (absolute path in <work-dir>)
and every whole-word use of <code_def> after the imports renamed to it. `lake env lean <file>` runs
under the memory cap from fv/kraken/lean. A mutant passes the suite when Lean reports an error and
every error line lies inside the theorem's line range; a control when Lean reports no error.
Writes <result.json> and, per case, <work-dir>/<id>/{mut.lean, mut.S?, diff, log}. Python 3 stdlib only.
"""
import difflib
import json
import pathlib
import re
import subprocess
import sys
import time

HERE = pathlib.Path(__file__).resolve().parent
KR = HERE.parent.parent
LEAN = KR / "lean"
NORM = KR / "prysm" / "go1.26.10" / "e2e" / "link" / "norm"
MEMCAP = KR / "gen" / "tools" / "memcap.py"
CAP = str(6 * 2 ** 30)
CASE_TIMEOUT = 900  # seconds per case (review e2e-r1 S7)
TOP = re.compile(r"^((theorem|def|end|example|set_option|abbrev|structure|instance|namespace|section|open)\b|/--|/-!)")


def cut(text, thm):
    lines = text.split("\n")
    start = next(i for i, l in enumerate(lines) if re.match(rf"^(private )?theorem {re.escape(thm)}\b", l))
    # include preceding set_option lines that belong to the theorem
    s0 = start
    while s0 > 0 and lines[s0 - 1].startswith("set_option") and lines[s0 - 1].rstrip().endswith(" in"):
        s0 -= 1
    end = next((i for i in range(start + 1, len(lines)) if TOP.match(lines[i])), len(lines))
    while end > start and lines[end - 1].strip() == "":
        end -= 1
    ns = [l for l in lines[:s0] if l.startswith("namespace ")]
    body = lines[:end]
    tail = [f"end {n.split()[1]}" for n in reversed(ns)
            if not any(l.strip() == f"end {n.split()[1]}" for l in lines[:s0])]
    return body + [""] + tail, start + 1, end  # 1-based start, inclusive end


def run_case(c, work):
    d = work / c["id"]
    d.mkdir(parents=True, exist_ok=True)
    src = (LEAN / c["module"]).read_text()
    lines, lo, hi = cut(src, c["theorem"])
    text = "\n".join(lines)
    diff = ""
    if c.get("code_def"):
        S = (NORM / c["S"]).read_text()
        if c["kind"] == "code":
            if "line" in c:  # 1-based line of the .S file (for an instruction that occurs twice)
                sl = S.split("\n")
                assert sl[c["line"] - 1] == c["old"], (c["id"], "line does not hold the old instruction")
                sl[c["line"] - 1] = c["new"]
                S2 = "\n".join(sl)
            else:
                assert S.count(c["old"] + "\n") == 1, (c["id"], "old instruction not unique")
                S2 = S.replace(c["old"] + "\n", c["new"] + "\n")
            diff = "".join(difflib.unified_diff(S.splitlines(True), S2.splitlines(True), "orig.S", "mut.S"))
        else:
            S2 = S
        (d / "mut.S").write_text(S2)
        name = c["code_def"]
        tl = text.split("\n")
        k = max(i for i, l in enumerate(tl) if l.startswith("import ")) + 1
        rest = re.sub(rf"(?<![A-Za-z0-9_.']){re.escape(name)}(?![A-Za-z0-9_'])", name + "Mut", "\n".join(tl[k:]))
        decl = f'def E2e.Code.{name}Mut : Program := include_x64_rt "{d / "mut.S"}"'
        text = "\n".join(tl[:k] + ["", decl] + [rest])
        lo += 2
        hi += 2
    if c["kind"] == "stmt":
        tl = text.split("\n")
        seg = "\n".join(tl[lo - 1:hi])
        assert seg.count(c["old"]) == 1, (c["id"], "statement text not unique in the theorem")
        seg2 = seg.replace(c["old"], c["new"])
        diff = "".join(difflib.unified_diff(seg.splitlines(True), seg2.splitlines(True), "orig", "mut"))
        text = "\n".join(tl[:lo - 1] + seg2.split("\n") + tl[hi:])
    f = d / "mut.lean"
    f.write_text(text)
    (d / "diff").write_text(diff)
    t0 = time.time()
    timed_out = False
    try:
        r = subprocess.run(["python3", "-I", str(MEMCAP), CAP, "--per-proc", CAP, "--", "lake", "env", "lean", str(f)],
                           cwd=LEAN, capture_output=True, text=True, timeout=CASE_TIMEOUT)
        log, rc = r.stdout + r.stderr, r.returncode
    except subprocess.TimeoutExpired as e:  # its own class (review e2e-r1 S7): never a pass
        timed_out = True
        log, rc = (e.stdout or b"").decode(errors="replace") + (e.stderr or b"").decode(errors="replace"), None
    (d / "log").write_text(log)
    errs = [int(m[1]) for m in re.finditer(rf"{re.escape(str(f))}:(\d+):\d+: error", log)]
    first = next((l for l in log.splitlines() if ": error" in l), None)
    killed = "killed=True" in log
    if timed_out:
        ok = False
    elif c["kind"] == "control":
        ok = rc == 0 and not errs and not killed
    else:
        ok = bool(errs) and all(lo <= e <= hi for e in errs) and not killed
    return {"id": c["id"], "kind": c["kind"], "module": c["module"], "theorem": c["theorem"],
            "range": [lo, hi], "error_lines": errs, "first_error": first, "rc": rc,
            "killed": killed, "timeout": timed_out, "seconds": round(time.time() - t0, 1), "pass": ok, "diff": diff}


def main(cases, work, out, *ids):
    cs = json.load(open(cases))
    if ids:
        cs = [c for c in cs if c["id"] in ids]
    work = pathlib.Path(work).resolve()
    work.mkdir(parents=True, exist_ok=True)
    res = []
    for c in cs:
        r = run_case(c, work)
        print(("PASS" if r["pass"] else "FAIL"), r["id"], r["kind"], r["theorem"], r["range"], r["error_lines"][:5],
              (r["first_error"] or "")[-160:], flush=True)
        res.append(r)
    old = json.load(open(out))["cases"] if pathlib.Path(out).exists() else []
    keep = [o for o in old if o["id"] not in {r["id"] for r in res}]
    allr = keep + res
    json.dump({"cases": allr, "pass": sum(r["pass"] for r in allr), "total": len(allr)}, open(out, "w"), indent=1)
    print(json.dumps({"pass": sum(r["pass"] for r in res), "run": len(res)}))
    return 0 if all(r["pass"] for r in res) else 1


if __name__ == "__main__":
    sys.exit(main(*sys.argv[1:]))
