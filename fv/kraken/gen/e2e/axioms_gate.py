#!/usr/bin/env python3
"""prysm-e2e axioms gate over EVERY declaration of the E2e, E2eAd and E2eScal libraries (audit AU-10, AU-05).

Usage (one gated job, Lean env; the cwd does not matter):
  axioms_gate.py run <out.json> <dump.tsv> [--extra-lean-path DIR --extra-module M]...
  axioms_gate.py check <dump.tsv> <out.json>       (pure Python, no Lean)
  axioms_gate.py --selftest                       (crafted dumps, no Lean)

run:
 1. Module list by program: every *.lean file under fv/kraken/lean/{E2e,E2eAd,E2eScal}.
 2. Freshness precheck (AU-05): `lake build --no-build <all modules>` must exit 0; else exit 2, nothing else runs.
    `lake env lean` itself does no trace check.
 3. `lake env lean --run <decl_dump.lean> --root E2e --root E2eAd --root E2eScal <modules>` writes one row per
    declaration (name, kind, type hash, value hash, sorted Lean.collectAxioms set) to <dump.tsv>. decl_dump.lean is
    the maintaining-methodical-fv skill script (read only). --extra-* adds a scratch .olean (negative control only).
 4. check: every row's axiom set is a subset of {propext, Classical.choice, Quot.sound}; no sorryAx; every name of
    the hand lists (`#print axioms X` in gen/e2e/Axioms.lean, gen/e2e/AxiomsAd.lean, gen/scal/AxiomsScal.lean) exists
    in the dump ("must exist"). Names are read from tab-separated columns, so names with `'` work.
Exit 0 PASS; 1 FAIL (non-standard axiom, sorryAx, a missing hand-list name, or an empty dump); 2 precheck or
dump failed. Python 3 stdlib only."""
import json
import os
import pathlib
import re
import subprocess
import sys

HERE = pathlib.Path(__file__).resolve().parent
KR = HERE.parent.parent
LEAN = KR / "lean"
REPO = KR.parent.parent
DUMP = REPO / ".claude" / "skills" / "maintaining-methodical-fv" / "scripts" / "decl_dump.lean"
ROOTS = ["E2e", "E2eAd", "E2eScal"]
LISTS = [HERE / "Axioms.lean", HERE / "AxiomsAd.lean", KR / "gen" / "scal" / "AxiomsScal.lean"]
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}


def modules():
    ms = []
    for r in ROOTS:
        for f in sorted((LEAN / r).rglob("*.lean")):
            ms.append(".".join(f.relative_to(LEAN).with_suffix("").parts))
    return ms


def hand_names():
    names = []
    for f in LISTS:
        names += re.findall(r"^#print axioms (\S+)\s*$", f.read_text(), re.M)
    return names


def check(rows, header, must):
    """rows: list of (name, kind, axioms list). Returns the result dict."""
    by = {n: (k, a) for n, k, a in rows}
    nonstd = {n: a for n, (k, a) in by.items() if not set(a) <= ALLOWED}
    sorry = sorted(n for n, (k, a) in by.items() if "sorryAx" in a)
    missing = [n for n in must if n not in by]
    kinds = {}
    for n, (k, a) in by.items():
        kinds[k] = kinds.get(k, 0) + 1
    axsets = {}
    for n, (k, a) in by.items():
        key = ",".join(a) or "-"
        axsets[key] = axsets.get(key, 0) + 1
    ok = bool(rows) and not nonstd and not sorry and not missing
    return {"header": header, "allowed": sorted(ALLOWED), "declarations": len(by), "kinds": kinds,
            "axiom_sets": axsets, "theorems": sum(1 for _, (k, _) in by.items() if k == "theorem"),
            "hand_list_names": len(must), "hand_list_missing": missing, "nonstandard": nonstd, "sorryAx": sorry,
            "verdict": "PASS" if ok else "FAIL"}


def parse(tsv):
    lines = tsv.splitlines()
    header = lines[0] if lines and lines[0].startswith("# decl_dump") else None
    rows = []
    for l in lines:
        if not l or l.startswith("#"):
            continue
        f = l.split("\t")
        if len(f) != 5:
            raise ValueError(f"bad row: {l!r}")
        rows.append((f[0], f[1], [] if f[4] == "-" else f[4].split(",")))
    return header, rows


def cmd_check(dump, out, extra_info=None):
    header, rows = parse(pathlib.Path(dump).read_text())
    r = check(rows, header, hand_names())
    if extra_info:
        r.update(extra_info)
    json.dump(r, open(out, "w"), indent=1)
    print(r["verdict"], "declarations", r["declarations"], "theorems", r["theorems"], "hand-list", r["hand_list_names"],
          "missing", r["hand_list_missing"], "nonstandard", len(r["nonstandard"]), "sorryAx", r["sorryAx"][:5])
    return 0 if r["verdict"] == "PASS" else 1


def cmd_run(out, dump, extra_paths, extra_mods):
    ms = modules()
    pre = ["lake", "build", "--no-build"] + ms
    p = subprocess.run(pre, cwd=LEAN, capture_output=True, text=True)
    fails = [l for l in (p.stdout + p.stderr).splitlines() if l.startswith("- ")]
    print("PRECHECK rc", p.returncode, "modules", len(ms), fails[:10], flush=True)
    info = {"modules": len(ms), "precheck": {"argv": "lake build --no-build <modules>", "rc": p.returncode,
                                             "failures": fails}}
    if p.returncode != 0:
        json.dump({**info, "verdict": "FAIL", "reason": "precheck"}, open(out, "w"), indent=1)
        return 2
    env = dict(os.environ)
    argv = ["lake", "env", "lean", "--run", str(DUMP)] + sum((["--root", r] for r in ROOTS), []) + ms
    if extra_paths:  # negative control only: a scratch .olean outside the tree
        argv = ["lake", "env", "sh", "-c", 'LEAN_PATH="$0:$LEAN_PATH" exec "$@"', ":".join(extra_paths),
                "lean", "--run", str(DUMP)] + sum((["--root", r] for r in ROOTS), []) + ms + extra_mods
        info["extra_modules"] = extra_mods
    d = subprocess.run(argv, cwd=LEAN, capture_output=True, text=True)
    pathlib.Path(dump).write_text(d.stdout)
    print("DUMP rc", d.returncode, "rows", d.stdout.count("\n") - 1, d.stderr[-500:], flush=True)
    info["dump"] = {"rc": d.returncode, "stderr_tail": d.stderr[-500:]}
    if d.returncode != 0:
        json.dump({**info, "verdict": "FAIL", "reason": "dump"}, open(out, "w"), indent=1)
        return 2
    return cmd_check(dump, out, info)


def selftest():
    H = "# decl_dump v1 lean=x githash=y roots=E2e"
    ok_rows = "\n".join([H, "E2e.a\ttheorem\t0\t-\tpropext", "E2e.b'\ttheorem\t0\t-\t-",
                         "E2e.c\tdef\t0\t1\tClassical.choice,Quot.sound,propext"])
    cases = [
        ("clean", ok_rows, ["E2e.a", "E2e.b'"], "PASS"),
        ("sorry", ok_rows + "\nE2e.s\ttheorem\t0\t-\tpropext,sorryAx", ["E2e.a"], "FAIL"),
        ("sorry_prime", ok_rows + "\nE2e.s'\ttheorem\t0\t-\tsorryAx", ["E2e.a"], "FAIL"),
        ("axiom", ok_rows + "\nE2e.t\ttheorem\t0\t-\tE2e.myAx,propext", ["E2e.a"], "FAIL"),
        ("missing", ok_rows, ["E2e.a", "E2e.zz"], "FAIL"),
        ("prime_missing", ok_rows, ["E2e.a'"], "FAIL"),
        ("empty", H, [], "FAIL"),
    ]
    bad = []
    for name, tsv, must, want in cases:
        h, rows = parse(tsv)
        got = check(rows, h, must)["verdict"]
        if got != want:
            bad.append((name, got, want))
    names = hand_names()
    if not names or any(" " in n for n in names):
        bad.append(("hand_names", len(names), "nonempty"))
    print("selftest", "PASS" if not bad else f"FAIL {bad}", "hand-list names", len(names))
    return 1 if bad else 0


if __name__ == "__main__":
    a = sys.argv[1:]
    if a == ["--selftest"]:
        sys.exit(selftest())
    if a[:1] == ["check"] and len(a) == 3:
        sys.exit(cmd_check(a[1], a[2]))
    if a[:1] == ["run"] and len(a) >= 3:
        xp, xm, rest = [], [], a[3:]
        while rest:
            if rest[0] == "--extra-lean-path":
                xp.append(rest[1])
            elif rest[0] == "--extra-module":
                xm.append(rest[1])
            else:
                sys.exit(__doc__)
            rest = rest[2:]
        sys.exit(cmd_run(a[1], a[2], xp, xm))
    sys.exit(__doc__)
