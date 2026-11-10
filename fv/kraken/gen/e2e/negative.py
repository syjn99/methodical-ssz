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
every error line lies inside the theorem's line range and no error is a Lean heartbeat timeout;
a control when Lean reports no error. Each result has a "class": control_pass, inside, outside,
no_error, killed, timeout_wall (CASE_TIMEOUT expired) or timeout_heartbeat (an error line is Lean's
"(deterministic) timeout"; review e2e-r2 N1). The two timeout classes are never a pass.
Old results whose id is not in <cases.json> are dropped from <result.json>.
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
CASE_TIMEOUT = 300  # seconds per case (review e2e-r1 S7; INBOX 007: 300 s)
HEARTBEAT = "(deterministic) timeout"
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
    hb = any(HEARTBEAT in l for l in log.splitlines() if ": error" in l)
    r = {"id": c["id"], "kind": c["kind"], "module": c["module"], "theorem": c["theorem"],
         "range": [lo, hi], "error_lines": errs, "first_error": first, "rc": rc,
         "killed": killed, "timeout": timed_out, "heartbeat_timeout": hb,
         "seconds": round(time.time() - t0, 1), "diff": diff}
    return classify(r)


def classify(r):
    """Class and pass flag from the recorded fields only (also applied to old results)."""
    errs, lo, hi = r["error_lines"], r["range"][0], r["range"][1]
    hb = r.get("heartbeat_timeout", HEARTBEAT in (r.get("first_error") or ""))
    r["heartbeat_timeout"] = hb
    if r["timeout"]:
        k = "timeout_wall"
    elif r["killed"]:
        k = "killed"
    elif r["kind"] == "control":
        k = "control_pass" if r["rc"] == 0 and not errs else "control_fail"
    elif hb:
        k = "timeout_heartbeat"
    elif not errs:
        k = "no_error"
    else:
        k = "inside" if all(lo <= e <= hi for e in errs) else "outside"
    r["class"] = k
    r["pass"] = k in ("control_pass", "inside")
    return r


def main(cases, work, out, *ids):
    cs = json.load(open(cases))
    if ids:
        cs = [c for c in cs if c["id"] in ids]
    work = pathlib.Path(work).resolve()
    work.mkdir(parents=True, exist_ok=True)
    res = []
    for c in cs:
        r = run_case(c, work)
        print(("PASS" if r["pass"] else "FAIL"), r["class"], r["id"], r["kind"], r["theorem"], r["range"], r["error_lines"][:5],
              (r["first_error"] or "")[-160:], flush=True)
        res.append(r)
    known = {c["id"] for c in json.load(open(cases))}
    old = json.load(open(out))["cases"] if pathlib.Path(out).exists() else []
    keep = [classify(o) for o in old if o["id"] not in {r["id"] for r in res} and o["id"] in known]
    allr = keep + res
    cls = {}
    for r in allr:
        cls[r["class"]] = cls.get(r["class"], 0) + 1
    json.dump({"cases": allr, "pass": sum(r["pass"] for r in allr), "total": len(allr), "classes": cls,
               "case_timeout_s": CASE_TIMEOUT}, open(out, "w"), indent=1)
    print(json.dumps({"pass": sum(r["pass"] for r in res), "run": len(res), "classes": cls}))
    return 0 if all(r["pass"] for r in res) else 1


def selftest():
    """Classifier fixture (review e2e-r2 N1): a heartbeat timeout and a wall timeout are never a pass."""
    base = dict(kind="stmt", range=[1, 9], rc=1, killed=False, timeout=False)
    fx = [("hb", dict(error_lines=[5], first_error="x:5:1: error: (deterministic) timeout at `whnf`"), "timeout_heartbeat"),
          ("in", dict(error_lines=[5], first_error="x:5:1: error: type mismatch"), "inside"),
          ("wall", dict(error_lines=[], first_error=None, rc=None, timeout=True), "timeout_wall"),
          ("out", dict(error_lines=[12], first_error="x:12:1: error: e"), "outside"),
          ("none", dict(error_lines=[], first_error=None, rc=0), "no_error"),
          ("ctl", dict(kind="control", error_lines=[], first_error=None, rc=0), "control_pass")]
    bad = []
    for name, f, want in fx:
        r = classify({**base, "id": name, **f})
        if r["class"] != want or r["pass"] != (want in ("inside", "control_pass")):
            bad.append((name, r["class"], want))
    print("selftest", "PASS" if not bad else f"FAIL {bad}")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(selftest() if sys.argv[1:] == ["--selftest"] else main(*sys.argv[1:]))
