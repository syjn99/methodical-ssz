#!/usr/bin/env python3
"""prysm-e2e negative suite: every mutant must fail inside its designated theorem; every control passes.

Usage (run inside one gated job, Lean env, cwd anywhere):
  negative.py <cases.json> <work-dir> <result.json> [<case-id>...]
cases.json: list of {"id", "module" (path under fv/kraken/lean, e.g. "Prysm/Epoch/DecodeAccept.lean"), "theorem",
  "kind": "code" | "stmt" | "control",
  code:  "code_def" (Lean name of the included program, e.g. "Prysm.Epoch.Code.unmarshalSSZ"), "S" (file under
         prysm/go1.26.10/e2e/link/norm), "old", "new" (one exact instruction line, unique in the file,
         or at the 1-based "line" of the file)
  stmt:  "old", "new" (exact text, unique inside the theorem statement)
  control: optional "code_def"/"S" (then an unmutated copy of the .S is included the same way)
  optional for code/control: "code_ns" (namespace of the code constant, default Prysm.Checkpoint.Code) and "norm"
  (path of the .S under fv/kraken instead of prysm/go1.26.10/e2e/link/norm/<S>; AttestationData set)}
For each case the mutant Lean file is the module's text up to the end of the designated theorem
(the next top-level `theorem`/`def`/`end`/`example`/`/--` after it is cut; a `theorem <thm>_kind` that
directly follows it is kept and belongs to the case range, review fix-r1 M2), with, for code cases, a
new constant `Prysm.Checkpoint.Code.<code_def>Mut` that includes the mutated .S copy (absolute path in <work-dir>)
and every whole-word use of <code_def> after the imports renamed to it. `lake env lean <file>` runs
under the memory cap from fv/kraken/lean. A mutant passes the suite when Lean reports an error and
every error line lies inside the theorem's line range and no error is a Lean heartbeat timeout;
a control when Lean reports no error. Each result has a "class": control_pass, inside, outside,
no_error, killed, timeout_wall (CASE_TIMEOUT expired) or timeout_heartbeat (an error line is Lean's
"(deterministic) timeout"; review e2e-r2 N1) or recursion_limit (an error line is "maximum recursion
depth has been reached") or wrong_target (the FIRST error is a parse error or an unknown identifier /
constant, or another parse / name-resolution form listed at WRONG_TARGET: the mutant does not reach its
target; audit AU-04, review fix-r1 M1); the resource classes are decided by the FIRST error line (a later resource
error is kept in "later_resource_error"). These three resource classes and wrong_target are never a pass.
negative.py --reclassify <result.json> [<work-dir>] recomputes the classes of a result file; --selftest checks them.
negative.py --check-cases <cases.json>... resolves every case to one theorem line and checks the code_def use (no Lean).
"theorem" is the full Lean name or the name as written on the declaration line; the full name selects the namespace
block when one module holds the same written name twice. Without "code_ns", a full name in "code_def" is declared
with `_root_`, and a module under Prysm/<Type>/ uses Prysm.<Type>.Code.
On a per-case timeout the whole process tree (memcap.py, and lake/lean in memcap's own session) is killed
and the driver asserts that none survives before the next case (audit AU-03); --selftest-timeout checks
this with a fake child (no Lean). Before the first case, `lake build --no-build <imports of the case modules>`
must exit 0 (audit AU-05: `lake env lean` does not check traces); otherwise no case runs and the exit code is 2.
The precheck argv and exit code are appended to "prechecks" of <result.json>.
Old results whose id is not in <cases.json> are dropped from <result.json>. A <case-id> that matches no
case is a usage error: nothing runs and the exit code is 2.
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
CASE_TIMEOUT = 300  # seconds per case
HEARTBEAT = "(deterministic) timeout"
RECDEPTH = "maximum recursion depth has been reached"
# audit AU-04: a first error that is a parse error or a name-resolution error says nothing about the
# mutated hypothesis or instruction; the mutant does not reach its target. Class wrong_target, never a pass.
# Review fix-r1 M1: the list is enumerated from the message strings of the pinned toolchain's sources
# (Lean/Parser, Lean/ResolveName.lean, Lean/Elab/*: `errorAtSavedPos`, `throwError`, `logError`), not only
# from observed records. It is matched at the START of the first error message (after `error:` or
# `error(<kind>):`), case-insensitive:
#   parse:            unknown tactic | unexpected token/end of input/identifier/command/tactic | expected <x>
#                     | unknown syntax category | unknown category | unknown parser
#   name resolution:  unknown identifier/constant/namespace/declaration/universe level/attribute/hypothesis
#                     /local declaration/alternative name/tag | unknown `grind` attribute
#                     | Invalid field `f`: The environment does not contain … (and the old lower-case form)
#                     | ambiguous identifier/namespace/…, possible interpretations
#   option / case:    Unknown option `o` | Case tag `t` not found (review fix-r2 N1: both escaped as inside)
# THE LIST IS NOT COMPLETE. It covers the forms named above and no others. A first error of another
# parse or name form that is not listed here still classifies as inside; read the first error of every row.
# Not included (elaborator-internal invariants, not a parse or user-name error): unknown metavariable,
# free variable, goal, let-declaration, parameter, local function, function.
WRONG_TARGET = re.compile(
    r"error(\([\w.]+\))?: "
    r"(unknown (tactic|identifier|constant|namespace|declaration|universe level|attribute|hypothesis"
    r"|local declaration|alternative name|tag|syntax category|category|parser)\b"
    r"|unknown `grind` attribute"
    r"|unknown option\b"
    r"|case tag\b.*\bnot found"
    r"|invalid field\b.*\benvironment does not contain"
    r"|ambiguous\b"
    r"|unexpected (token|end of input|identifier|command|tactic)\b"
    r"|expected [^\s])", re.I)
TOP = re.compile(r"^((theorem|def|end|example|set_option|abbrev|structure|instance|namespace|section|open)\b|/--|/-!)")


DECL_AT = re.compile(r"^(?:private )?(theorem|def) ([^\s:({\[]+)")


def find_decl(lines, name, kinds=("theorem",)):
    """(index, name as written) of the declaration line of `name` in a module. `name` is the full name (the
    namespace blocks above the line and the written name; `_root_.` handled) or the name as written on the line.
    A full-name match wins. Exactly one line must match, else ValueError (two blocks of one module can hold the
    same written name, for example `theorem Decode.accept` of two types)."""
    stack, full_hits, written_hits = [], [], []
    for i, l in enumerate(lines):
        m = re.match(r"^namespace (\S+)\s*$", l)
        if m:
            stack.append(m.group(1))
            continue
        if re.match(r"^section\b", l):
            stack.append("")
            continue
        if re.match(r"^end\b", l) and stack:
            stack.pop()
            continue
        m = DECL_AT.match(l)
        if not m or m.group(1) not in kinds:
            continue
        w = m.group(2)
        ns = ".".join(x for x in stack if x)
        full = w[7:] if w.startswith("_root_.") else (ns + "." if ns else "") + w
        if full == name:
            full_hits.append((i, w))
        if w == name:
            written_hits.append((i, w))
    hits = full_hits or written_hits
    if len(hits) != 1:
        raise ValueError(f"{name}: {len(hits)} declaration lines match")
    return hits[0]


def code_ns_of(c):
    """Namespace of the code constant of a case: `code_ns`, else `_root_` for a full name in `code_def`, else
    `Prysm.<Type>.Code` for a module under Prysm/<Type>/, else Prysm.Checkpoint.Code (the old default set)."""
    if "code_ns" in c:
        return c["code_ns"]
    if "." in c["code_def"]:
        return "_root_"
    p = c["module"].split("/")
    if p[0] == "Prysm" and len(p) > 2:
        return f"Prysm.{p[1]}.Code"
    return "Prysm.Checkpoint.Code"


def cut(text, thm):
    lines = text.split("\n")
    start, written = find_decl(lines, thm)
    thm = written
    # include preceding set_option lines that belong to the theorem
    s0 = start
    while s0 > 0 and lines[s0 - 1].startswith("set_option") and lines[s0 - 1].rstrip().endswith(" in"):
        s0 -= 1
    end = next((i for i in range(start + 1, len(lines)) if TOP.match(lines[i])), len(lines))
    # review fix-r1 M2/S1: a statement-kind identity `theorem <thm>_kind` right after the theorem checks the
    # theorem's whole declared type; it stays in the mutant and in the case range
    j = end
    while j < len(lines) and (lines[j].strip() == "" or lines[j].lstrip().startswith("--")):
        j += 1
    if j < len(lines) and re.match(rf"^theorem {re.escape(thm)}_kind\b", lines[j]):
        end = next((i for i in range(j + 1, len(lines)) if TOP.match(lines[i])), len(lines))
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
    except subprocess.TimeoutExpired:  # its own class: never a pass
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
        ns = code_ns_of(c)
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
    # no absolute work-dir path in the committed result file
    first, later = [x.replace(str(work), "<work>") if x else x for x in (first, later)]
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


def imports_of(modules):
    """Module names imported by the given files (paths under fv/kraken/lean)."""
    mods = set()
    for m in modules:
        for l in (LEAN / m).read_text().split("\n"):
            if l.startswith("import "):
                mods.update(l.split()[1:])
    return sorted(mods)


def precheck(modules):
    """Audit AU-05: `lake env lean` does no trace check, so a stale .olean could be used. Before any case,
    `lake build --no-build <imports>` must exit 0 (every imported module is up to date)."""
    imps = imports_of(modules)
    argv = ["lake", "build", "--no-build"] + imps
    r = subprocess.run(argv, cwd=LEAN, capture_output=True, text=True)
    tail = [l for l in (r.stdout + r.stderr).splitlines() if l.startswith("- ") or "error" in l][-20:]
    print("PRECHECK", "rc", r.returncode, " ".join(argv), flush=True)
    return {"argv": argv, "rc": r.returncode, "failures": tail}


def main(cases, work, out, *ids):
    cs = json.load(open(cases))
    if ids:
        missing = sorted(set(ids) - {c["id"] for c in cs})
        cs = [c for c in cs if c["id"] in ids]
        if missing or not cs:  # an id that matches no case is a usage error, not 0 cases run
            print("NO SUCH CASE:", missing, "; no case run", flush=True)
            return 2
    work = pathlib.Path(work).resolve()
    work.mkdir(parents=True, exist_ok=True)
    pc = precheck(sorted({c["module"] for c in cs}))
    if pc["rc"] != 0:
        print("PRECHECK FAILED: stale or missing imported modules; no case run", pc["failures"], flush=True)
        return 2
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
    prev = json.load(open(out)).get("prechecks", []) if pathlib.Path(out).exists() else []
    pc["cases"] = [r["id"] for r in res]
    json.dump({"cases": allr, "pass": sum(r["pass"] for r in allr), "total": len(allr), "classes": cls,
               "case_timeout_s": CASE_TIMEOUT, "prechecks": (prev + [pc])[-50:]}, open(out, "w"), indent=1)
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
          # review fix-r1 M1: the reviewer's real record rv-unknown-tactic (`exact` -> `exactt`) and crafted forms
          ("wt_tactic", dict(error_lines=[54], first_error="x:54:3: error: unknown tactic", range=[1, 60]), "wrong_target"),
          ("wt_ns", dict(error_lines=[5], first_error="x:5:5: error: unknown namespace `Foo`"), "wrong_target"),
          ("wt_field", dict(error_lines=[5], first_error="x:5:2: error: Invalid field `foo`: The environment does not "
                                                          "contain `Nat.foo`, so it is not possible to project"),
           "wrong_target"),
          ("wt_field_old", dict(error_lines=[5], first_error="x:5:2: error: invalid field 'foo', the environment does "
                                                              "not contain 'Nat.foo'"), "wrong_target"),
          ("wt_ambig", dict(error_lines=[5], first_error="x:5:2: error: Ambiguous identifier `f`; possible "
                                                          "interpretations: [A.f, B.f]"), "wrong_target"),
          ("wt_ambig_old", dict(error_lines=[5], first_error="x:5:2: error: ambiguous, possible interpretations"),
           "wrong_target"),
          ("wt_decl", dict(error_lines=[5], first_error="x:5:2: error: unknown declaration 'E2e.foo'"), "wrong_target"),
          ("wt_univ", dict(error_lines=[5], first_error="x:5:2: error: unknown universe level `v`"), "wrong_target"),
          ("wt_attr", dict(error_lines=[5], first_error="x:5:2: error: Unknown attribute `[simpp]`"), "wrong_target"),
          ("wt_hyp", dict(error_lines=[5], first_error="x:5:2: error: unknown hypothesis `h`"), "wrong_target"),
          ("wt_kind", dict(error_lines=[5], first_error="x:5:2: error(lean.unknownIdentifier): Unknown identifier `h`"),
           "wrong_target"),
          ("wt_cmd", dict(error_lines=[5], first_error="x:5:0: error: unexpected command"), "wrong_target"),
          # review fix-r2 N1: the reviewer's two escapes (real first-error strings of the pinned toolchain)
          ("wt_option", dict(error_lines=[54], first_error="x:54:2: error: Unknown option `rv.nosuch`", range=[21, 55]),
           "wrong_target"),
          ("wt_casetag", dict(error_lines=[54], first_error="x:54:2: error: Case tag `rvnosuch` not found.",
                              range=[21, 55]), "wrong_target"),
          ("wt_casetag_hint", dict(error_lines=[5], first_error="x:5:2: error: Case tag `h` not found.\nHint: x"),
           "wrong_target"),
          # messages that only contain such words later are real failures
          ("in_mentions_expected", dict(error_lines=[5], first_error="x:5:1: error: Application type mismatch: "
                                                                         "hms has type True but is expected to have type"),
           "inside"),
          ("in_unknown_later", dict(error_lines=[5], first_error="x:5:1: error: omega could not prove the goal: "
                                                                     "unknown identifier in a hint"), "inside"),
          ("wt_unexp_tactic", dict(error_lines=[5], first_error="x:5:1: error: Unexpected tactic"), "wrong_target"),
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


def check_cases(*paths):
    """Dry run (no Lean): every case of every given cases file resolves to exactly one theorem line of its module
    (`find_decl`), and a case with `code_def` has a whole-word use of `code_def` after the imports (else the mutant
    would not use the mutated program). A case with "stmt_def" (lvnegative.py) also resolves its def line in
    "stmt_module" or the inlined modules. Prints one line per failure and a summary."""
    bad, n = [], 0
    for p in paths:
        for c in json.load(open(p)):
            n += 1
            try:
                src = (LEAN / c["module"]).read_text()
                lines, lo, hi = cut(src, c["theorem"])
                if c.get("stmt_def"):
                    mods = c.get("inline", [c["stmt_module"]] if c.get("stmt_module") else [])
                    text = "\n".join((LEAN / m).read_text() for m in mods) if mods else "\n".join(lines)
                    find_decl(text.split("\n"), c["stmt_def"], ("def",))
                elif c["kind"] == "stmt" and "\n".join(lines[lo - 1:hi]).count(c["old"]) != 1:
                    raise ValueError("statement text not unique in the theorem")
            except (OSError, ValueError, StopIteration, KeyError) as e:
                bad.append(f"{p}: {c['id']}: {type(e).__name__} {e}")
                continue
            if c.get("code_def"):
                tl = "\n".join(lines).split("\n")
                k = max(i for i, l in enumerate(tl) if l.startswith("import ")) + 1
                name = c["code_def"]
                body = "\n".join(tl[k:])
                for m in c.get("inline", [c["stmt_module"]] if c.get("stmt_module") else []):
                    body += "\n" + (LEAN / m).read_text()
                if not re.search(rf"(?<![A-Za-z0-9_.']){re.escape(name)}(?![A-Za-z0-9_'])", body):
                    bad.append(f"{p}: {c['id']}: code_def {name} is not used in {c['module']}")
    for b in bad:
        print("CHECK FAIL", b)
    print(f"check-cases: {n} cases, {len(bad)} failures")
    return 1 if bad else 0


if __name__ == "__main__":
    if sys.argv[1:2] == ["--check-cases"]:
        sys.exit(check_cases(*sys.argv[2:]))
    if sys.argv[1:] == ["--selftest"]:
        sys.exit(selftest())
    if sys.argv[1:] == ["--selftest-timeout"]:
        sys.exit(selftest_timeout())
    if sys.argv[1:2] == ["--reclassify"]:
        sys.exit(reclassify(*sys.argv[2:4]))
    sys.exit(main(*sys.argv[1:]))
