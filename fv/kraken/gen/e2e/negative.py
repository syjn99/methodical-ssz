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
  control: optional "code_def"/"S" (then an unmutated copy of the .S is included the same way)
  optional for code/control: "code_ns" (namespace of the code constant, default E2e.Code) and "norm"
  (path of the .S under fv/kraken instead of prysm/go1.26.10/e2e/link/norm/<S>; AttestationData set)}
For each case the mutant Lean file is the module's text up to the end of the designated theorem
(the next top-level `theorem`/`def`/`end`/`example`/`/--` after it is cut), with, for code cases, a
new constant `E2e.Code.<code_def>Mut` that includes the mutated .S copy (absolute path in <work-dir>)
and every whole-word use of <code_def> after the imports renamed to it. `lake env lean <file>` runs
under the memory cap from fv/kraken/lean. A mutant passes the suite when Lean reports an error and
every error line lies inside the theorem's line range and no error is a Lean heartbeat timeout;
a control when Lean reports no error. Each result has a "class": control_pass, inside, outside,
no_error, killed, timeout_wall (CASE_TIMEOUT expired) or timeout_heartbeat (an error line is Lean's
"(deterministic) timeout"; review e2e-r2 N1) or recursion_limit (an error line is "maximum recursion
depth has been reached") or wrong_target (the FIRST error is a parse error or an unknown identifier /
constant: the mutant does not reach its target; audit AU-04); the resource classes are decided by the FIRST error line (a later resource
error is kept in "later_resource_error"). These three resource classes and wrong_target are never a pass.
negative.py --reclassify <result.json> [<work-dir>] recomputes the classes of a result file; --selftest checks them.
On a per-case timeout the whole process tree (memcap.py, and lake/lean in memcap's own session) is killed
and the driver asserts that none survives before the next case (audit AU-03); --selftest-timeout checks
this with a fake child (no Lean).
Old results whose id is not in <cases.json> are dropped from <result.json>.
Writes <result.json> and, per case, <work-dir>/<id>/{mut.lean, mut.S?, diff, log}. Python 3 stdlib only.
"""
import difflib
import json
import os
import pathlib
import re
import signal
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
RECDEPTH = "maximum recursion depth has been reached"
# audit AU-04: a first error that is a parse error or a name-resolution error says nothing about the
# mutated hypothesis or instruction; the mutant does not reach its target. Class wrong_target, never a pass.
WRONG_TARGET = re.compile(
    r"error(\((lean\.)?(unknownIdentifier|unknownConstant|parse\w*)\))?: "
    r"(unknown (identifier|constant)|unexpected (token|end of input|identifier)|expected [^\s])", re.I)
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


def _proc_table():
    """pid -> (ppid, sid, state) from /proc (Linux)."""
    t = {}
    for p in os.listdir("/proc"):
        if not p.isdigit():
            continue
        try:
            st = open(f"/proc/{p}/stat").read()
            f = st[st.rindex(")") + 2:].split()
            t[int(p)] = (int(f[1]), int(f[3]), f[0])
        except (OSError, ValueError, IndexError):
            continue
    return t


def _tree(root):
    """The root, its live descendants, and every other member of their sessions (memcap puts lake/lean
    into a new session). Our own session is excluded."""
    t = _proc_table()
    own = os.getsid(0)
    pids, todo = {root}, [root]
    while todo:
        q = todo.pop()
        for p, (pp, _, _) in t.items():
            if pp == q and p not in pids:
                pids.add(p)
                todo.append(p)
    sids = {t[p][1] for p in pids if p in t} - {own}
    pids |= {p for p, (_, sid, _) in t.items() if sid in sids}
    return pids, sids


def _alive(pids):
    t = _proc_table()
    return sorted(p for p in pids if p in t and t[p][2] != "Z")


def kill_tree(root):
    """SIGKILL the root, its descendants and their sessions; wait up to 10 s; raise if any survives
    (review AU-03: the old timeout killed only memcap.py and left lake/lean running)."""
    pids, sids = _tree(root)
    for p in pids:  # stop first, so that no member forks while we collect
        try:
            os.kill(p, signal.SIGSTOP)
        except ProcessLookupError:
            pass
    pids2, sids2 = _tree(root)
    pids |= pids2
    sids |= sids2
    for s in sids:
        try:
            os.killpg(s, signal.SIGKILL)
        except (ProcessLookupError, PermissionError):
            pass
    for p in pids:
        try:
            os.kill(p, signal.SIGKILL)
        except ProcessLookupError:
            pass
    deadline = time.time() + 10
    while _alive(pids) and time.time() < deadline:
        time.sleep(0.1)
    left = _alive(pids)
    if left:
        raise RuntimeError(f"timeout cleanup: processes survive: {left}")
    return sorted(pids)


def run_capped(argv, cwd, timeout):
    """Run argv; on timeout kill the whole process tree (also new sessions below it) and assert that
    nothing survives before the caller starts the next case. Returns (log, rc, timed_out, reaped pids)."""
    p = subprocess.Popen(argv, cwd=cwd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True,
                         errors="replace")
    try:
        out, err = p.communicate(timeout=timeout)
        return out + err, p.returncode, False, []
    except subprocess.TimeoutExpired:  # its own class (review e2e-r1 S7): never a pass
        reaped = kill_tree(p.pid)
        out, err = p.communicate()
        return (out or "") + (err or ""), None, True, reaped


def run_case(c, work):
    d = work / c["id"]
    d.mkdir(parents=True, exist_ok=True)
    src = (LEAN / c["module"]).read_text()
    lines, lo, hi = cut(src, c["theorem"])
    text = "\n".join(lines)
    diff = ""
    if c.get("code_def"):
        S = (KR / c["norm"] if "norm" in c else NORM / c["S"]).read_text()
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
        ns = c.get("code_ns", "E2e.Code")
        decl = f'def {ns}.{name}Mut : Program := include_x64_rt "{d / "mut.S"}"'
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
    log, rc, timed_out, reaped = run_capped(
        ["python3", "-I", str(MEMCAP), CAP, "--per-proc", CAP, "--", "lake", "env", "lean", str(f)], LEAN, CASE_TIMEOUT)
    (d / "log").write_text(log)
    errs = [int(m[1]) for m in re.finditer(rf"{re.escape(str(f))}:(\d+):\d+: error", log)]
    first = next((l for l in log.splitlines() if ": error" in l), None)
    killed = "killed=True" in log
    errl = [l for l in log.splitlines() if ": error" in l]
    later = next((l for l in errl[1:] if HEARTBEAT in l or RECDEPTH in l), None)
    r = {"id": c["id"], "kind": c["kind"], "module": c["module"], "theorem": c["theorem"],
         "range": [lo, hi], "error_lines": errs, "first_error": first, "rc": rc,
         "killed": killed, "timeout": timed_out, "timeout_reaped_pids": reaped, "later_resource_error": later,
         "seconds": round(time.time() - t0, 1), "diff": diff}
    return classify(r)


def classify(r):
    """Class and pass flag from the recorded fields only (also applied to old results). The resource
    classes follow the FIRST error line (review e2e-r2 N1: the first error is Lean's timeout); a later
    heartbeat or recursion error after a real first error is kept as a flag (`later_resource_error`)."""
    errs, lo, hi = r["error_lines"], r["range"][0], r["range"][1]
    first = r.get("first_error") or ""
    hb = HEARTBEAT in first
    rd = RECDEPTH in first
    r["heartbeat_timeout"] = hb
    r["recursion_limit"] = rd
    if "later_resource_error" not in r:
        r["later_resource_error"] = None
    if r["timeout"]:
        k = "timeout_wall"
    elif r["killed"]:
        k = "killed"
    elif r["kind"] == "control":
        k = "control_pass" if r["rc"] == 0 and not errs else "control_fail"
    elif hb:
        k = "timeout_heartbeat"
    elif rd:
        k = "recursion_limit"
    elif errs and WRONG_TARGET.search(first):
        k = "wrong_target"
    elif not errs:
        k = "no_error"
    else:
        k = "inside" if all(lo <= e <= hi for e in errs) else "outside"
    r["class"] = k
    r["pass"] = k in ("control_pass", "inside")
    return r


def reclassify(out, work=None):
    d = json.load(open(out))
    for c in d["cases"]:  # fill the later-resource flag from the archived log when it is there
        lp = pathlib.Path(work) / c["id"] / "log" if work else None
        if lp and lp.exists():
            errl = [l for l in lp.read_text(errors="replace").splitlines() if ": error" in l]
            c["later_resource_error"] = next((l for l in errl[1:] if HEARTBEAT in l or RECDEPTH in l), None)
    d["cases"] = [classify(c) for c in d["cases"]]
    cls = {}
    for c in d["cases"]:
        cls[c["class"]] = cls.get(c["class"], 0) + 1
    d.update({"pass": sum(c["pass"] for c in d["cases"]), "total": len(d["cases"]), "classes": cls})
    json.dump(d, open(out, "w"), indent=1)
    print(json.dumps({"pass": d["pass"], "total": d["total"], "classes": cls}))
    return 0


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
          ("rd", dict(error_lines=[5], first_error="x:5:0: error: maximum recursion depth has been reached"), "recursion_limit"),
          ("later_hb", dict(error_lines=[5, 7], first_error="x:5:1: error: ecancel failed",
                            later_resource_error="x:7:1: error: (deterministic) timeout at `whnf`"), "inside"),
          ("ctl", dict(kind="control", error_lines=[], first_error=None, rc=0), "control_pass"),
          # audit AU-04: name resolution and parse errors inside the range are wrong_target, not inside
          ("wt_uid", dict(error_lines=[5], first_error="x:5:47: error(lean.unknownIdentifier): Unknown identifier `hms`"),
           "wrong_target"),
          ("wt_uid_old", dict(error_lines=[5], first_error="x:5:47: error: unknown identifier 'hms'"), "wrong_target"),
          ("wt_ucst", dict(error_lines=[5], first_error="x:5:3: error(lean.unknownConstant): Unknown constant `E2e.foo`"),
           "wrong_target"),
          ("wt_ucst_old", dict(error_lines=[5], first_error="x:5:3: error: unknown constant 'E2e.foo'"), "wrong_target"),
          ("wt_parse", dict(error_lines=[5], first_error="x:5:0: error: unexpected token 'theorem'; expected term"),
           "wrong_target"),
          ("wt_parse2", dict(error_lines=[5], first_error="x:5:9: error: expected ':=', 'where' or '|'"), "wrong_target"),
          ("wt_eoi", dict(error_lines=[9], first_error="x:9:0: error: unexpected end of input"), "wrong_target"),
          # a later unknown identifier after a real first error does not change the class
          ("in_then_uid", dict(error_lines=[5, 6], first_error="x:5:1: error: Type mismatch"), "inside"),
          ("in_unsolved", dict(error_lines=[5], first_error="x:5:1: error: unsolved goals"), "inside"),
          ("in_expected_type", dict(error_lines=[5], first_error="x:5:1: error: Application type mismatch: expected type"),
           "inside")]
    bad = []
    for name, f, want in fx:
        r = classify({**base, "id": name, **f})
        if r["class"] != want or r["pass"] != (want in ("inside", "control_pass")):
            bad.append((name, r["class"], want))
    print("selftest", "PASS" if not bad else f"FAIL {bad}")
    return 1 if bad else 0


def selftest_timeout():
    """AU-03 fake child (no Lean): a child that starts a grandchild in a NEW session (as memcap.py does)
    and both sleep. After the timeout no process of the tree may survive."""
    code = ("import subprocess,sys,time\n"
            "g=subprocess.Popen([sys.executable,'-c','import time\\ntime.sleep(600)'],start_new_session=True)\n"
            "print('grandchild',g.pid,flush=True)\n"
            "time.sleep(600)\n")
    t0 = time.time()
    log, rc, to, reaped = run_capped([sys.executable, "-I", "-c", code], "/", 2)
    gc = int(re.search(r"grandchild (\d+)", log)[1])
    left = _alive([gc] + reaped)
    ok = to and rc is None and gc in reaped and not left and time.time() - t0 < 30
    print("selftest-timeout", "PASS" if ok else "FAIL", {"timed_out": to, "grandchild": gc, "reaped": reaped,
                                                         "survivors": left, "s": round(time.time() - t0, 1)})
    # control: a quick child is not a timeout
    log2, rc2, to2, _ = run_capped([sys.executable, "-I", "-c", "print('ok')"], "/", 20)
    ok2 = rc2 == 0 and not to2 and log2.strip() == "ok"
    print("selftest-timeout-control", "PASS" if ok2 else "FAIL")
    return 0 if ok and ok2 else 1


if __name__ == "__main__":
    if sys.argv[1:] == ["--selftest"]:
        sys.exit(selftest())
    if sys.argv[1:] == ["--selftest-timeout"]:
        sys.exit(selftest_timeout())
    if sys.argv[1:2] == ["--reclassify"]:
        sys.exit(reclassify(*sys.argv[2:4]))
    sys.exit(main(*sys.argv[1:]))
