#!/usr/bin/env python3
"""Negative suite in the style of `negative.py` (not changed) for the theorems of the list and vector types.

Usage (one gated job, Lean env, cwd anywhere):
  list_negative.py <cases.json> <work-dir> <result.json> [<case-id>...]
It imports `negative.py` and uses its `cut`, `classify`, `precheck` and `main` unchanged. Two functions differ:
* run_case: the list/vector main theorems state `theorem X : <frozen stmt def>`, and the stmt defs live in another module
  (`Prysm/SyncAggregate/Statements.lean`, `Prysm/SyncCommittee/Statements.lean`). A case may name "statement_module" (path under fv/kraken/lean), or "inline", a list of
  such modules in dependency order (for example `Prysm/SyncAggregate/SpecDescription.lean` then `Defs.lean` for a Desc mutant). The mutant file then
  inlines those modules' bodies (their imports are replaced by their own imports), so that the code rename
  `<code_def>` → `<code_def>Mut` also reaches the statement. A "stmt" case names "statement_def" and mutates the text
  of that def (old → new, unique inside the def). "norm" is the .S path under fv/kraken; "code_ns" the namespace
  of the code constant (default: `negative.code_ns_of`, Prysm.<Type>.Code for a module under Prysm/<Type>/).
* run_capped: no `gen/tools/memory_limit.py` (it reads /proc, absent on macOS); the job runs under the heavy-job
  gate's cap. A case that exceeds the per-case timeout is killed with its process group (start_new_session).
A mutant passes when Lean reports an error and every error line lies inside the designated theorem and the first
error is not a resource or wrong-target error (negative.py's classes). Python 3 stdlib only.
"""
import difflib
import os
import pathlib
import re
import signal
import subprocess
import sys
import time

HERE = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import negative as n  # noqa: E402

KR, LEAN = n.KR, n.LEAN


def run_capped(argv, cwd, timeout):
    p = subprocess.Popen(argv, cwd=cwd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True,
                         errors="replace", start_new_session=True)
    try:
        out, err = p.communicate(timeout=timeout)
        return out + err, p.returncode, False, []
    except subprocess.TimeoutExpired:
        os.killpg(p.pid, signal.SIGKILL)
        out, err = p.communicate()
        return (out or "") + (err or ""), None, True, [p.pid]


def split_imports(text):
    tl = text.split("\n")
    k = max(i for i, l in enumerate(tl) if l.startswith("import ")) + 1
    return tl[:k], tl[k:]


def theorem_range(lines, thm):
    start, _ = n.find_decl(lines, thm)
    end = next((i for i in range(start + 1, len(lines)) if n.TOP.match(lines[i])), len(lines))
    while end > start and lines[end - 1].strip() == "":
        end -= 1
    return start + 1, end


def run_case(c, work):
    d = work / c["id"]
    d.mkdir(parents=True, exist_ok=True)
    src = (LEAN / c["module"]).read_text()
    lines, _, _ = n.cut(src, c["theorem"])
    imps, body = split_imports("\n".join(lines))
    inl = c.get("inline", [c["statement_module"]] if c.get("statement_module") else [])
    if inl:
        names = {m.removesuffix(".lean").replace("/", ".") for m in inl}
        pre_imps, pre_body = [], []
        for m in inl:  # dependency order: earlier modules first
            mi, mb = split_imports((LEAN / m).read_text())
            pre_imps += [l for l in mi if l not in pre_imps]
            pre_body += mb + [""]
        imps = [l for l in pre_imps + imps if l.split()[1] not in names]
        imps = list(dict.fromkeys(imps))
        body = pre_body + body
    rest = "\n".join(body)
    diff = ""
    if c.get("code_def"):
        S = (KR / c["norm"]).read_text()
        if c["kind"] == "code":
            if "line" in c:
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
        rest = re.sub(rf"(?<![A-Za-z0-9_.']){re.escape(name)}(?![A-Za-z0-9_'])", name + "Mut", rest)
        decl = f'def {n.code_ns_of(c)}.{name}Mut : Program := include_x64_code "{d / "mut.S"}"'
        rest = decl + "\n\n" + rest
    if c["kind"] == "stmt":
        rl = rest.split("\n")
        a, _ = n.find_decl(rl, c["statement_def"], ("def",))
        b = next((i for i in range(a + 1, len(rl)) if n.TOP.match(rl[i])), len(rl))
        seg = "\n".join(rl[a:b])
        assert seg.count(c["old"]) == 1, (c["id"], "statement text not unique in the stmt def")
        seg2 = seg.replace(c["old"], c["new"])
        diff = "".join(difflib.unified_diff(seg.splitlines(True), seg2.splitlines(True), "orig", "mut"))
        rest = "\n".join(rl[:a] + seg2.split("\n") + rl[b:])
    text = "\n".join(imps) + "\n\n" + rest
    lo, hi = theorem_range(text.split("\n"), c["theorem"])
    f = d / "mut.lean"
    f.write_text(text)
    (d / "diff").write_text(diff)
    t0 = time.time()
    log, rc, timed_out, reaped = run_capped(["lake", "env", "lean", str(f)], LEAN, n.CASE_TIMEOUT)
    (d / "log").write_text(log)
    errs = [int(m[1]) for m in re.finditer(rf"{re.escape(str(f))}:(\d+):\d+: error", log)]
    errl = [l for l in log.splitlines() if ": error" in l]
    first = errl[0] if errl else None
    later = next((l for l in errl[1:] if n.HEARTBEAT in l or n.RECDEPTH in l), None)
    first, later = [x.replace(str(work), "<work>") if x else x for x in (first, later)]
    r = {"id": c["id"], "kind": c["kind"], "module": c["module"], "theorem": c["theorem"],
         "range": [lo, hi], "error_lines": errs, "first_error": first, "rc": rc,
         "killed": False, "timeout": timed_out, "timeout_reaped_pids": reaped, "later_resource_error": later,
         "seconds": round(time.time() - t0, 1), "diff": diff}
    return n.classify(r)


n.run_case = run_case
n.run_capped = run_capped

if __name__ == "__main__":
    if len(sys.argv) < 4:
        sys.exit(__doc__)
    sys.exit(n.main(*sys.argv[1:]))
