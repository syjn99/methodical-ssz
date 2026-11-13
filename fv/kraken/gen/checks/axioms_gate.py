#!/usr/bin/env python3
"""Axioms gate over EVERY declaration of EVERY Lean library of fv/kraken/lean.

Usage (one gated job, Lean env; the cwd does not matter):
  axioms_gate.py run <out.json> <dump.tsv> [--extra-lean-path DIR --extra-module M]...
  axioms_gate.py check <dump.tsv> <out.json>       (pure Python, no Lean)
  axioms_gate.py --selftest                       (crafted inputs, no Lean)

The gate reads two things at run time. It has no library name and no list name in its text.
 * Libraries: the `name = "..."` line of each `[[lean_lib]]` block of fv/kraken/lean/lakefile.toml.
   Each library must have the glob `<name>.+`. Its modules are the *.lean files under fv/kraken/lean/<name>/.
   A library with another glob form, or with no module, stops the gate (exit 2).
 * Hand lists: every *.lean file directly in fv/kraken/gen/axioms-lists/. Each one is a list of
   `#print axioms <name>` lines with the imports that the names need. No list file stops the gate (exit 2).

run:
 1. Freshness precheck: `lake build --no-build <all modules>` must exit 0; else exit 2, nothing else runs.
    `lake env lean` itself does no trace check.
 2. `lake env lean --run <decl_dump.lean> --root <library>... <modules>` (every library) writes one row per
    declaration (name, kind, type hash, value hash, sorted Lean.collectAxioms set) to <dump.tsv>. decl_dump.lean is
    the maintaining-methodical-fv skill script (read only). --extra-* adds a scratch .olean (negative control only).
 3. check: every row's axiom set is a subset of {propext, Classical.choice, Quot.sound}; no sorryAx; every name of
    the hand lists exists in the dump ("must exist"). Names are read from tab-separated columns, so names with `'`
    work.
Exit 0 PASS; 1 FAIL (non-standard axiom, sorryAx, a missing hand-list name, or an empty dump); 2 precheck, dump,
lakefile or hand-list discovery failed. Python 3 stdlib only."""
import json
import os
import pathlib
import re
import subprocess
import sys
import tempfile

HERE = pathlib.Path(__file__).resolve().parent
KR = HERE.parent.parent
LEAN = KR / "lean"
LAKEFILE = LEAN / "lakefile.toml"
LIST_DIR = KR / "gen" / "axioms-lists"
REPO = KR.parent.parent
DUMP = REPO / ".claude" / "skills" / "maintaining-methodical-fv" / "scripts" / "decl_dump.lean"
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}


class SetupError(Exception):
    """The lakefile, a library directory or the hand-list directory is not in the form that the gate reads."""


def libraries(text):
    """The library names of a lakefile.toml text, in file order. Only `[[lean_lib]]` blocks count.
    Each block must have one `name = "..."` line and the line `globs = ["<name>.+"]`."""
    libs, block = [], None

    def close(b):
        if b is None:
            return
        if len(b["name"]) != 1:
            raise SetupError(f"lakefile: a [[lean_lib]] block has {len(b['name'])} name lines")
        n = b["name"][0]
        if b["globs"] != [f'"{n}.+"']:
            raise SetupError(f"lakefile: library {n}: globs {b['globs']} is not [\"{n}.+\"]")
        libs.append(n)

    for line in text.splitlines():
        s = line.split("#", 1)[0].strip() if not line.lstrip().startswith("#") else ""
        if s.startswith("["):
            close(block)
            block = {"name": [], "globs": None} if s == "[[lean_lib]]" else None
            continue
        if block is None:
            continue
        m = re.match(r'^name\s*=\s*"([^"]+)"$', s)
        if m:
            block["name"].append(m.group(1))
            continue
        m = re.match(r"^globs\s*=\s*\[(.*)\]$", s)
        if m:
            block["globs"] = [g.strip() for g in m.group(1).split(",") if g.strip()]
        elif s.startswith("globs"):
            raise SetupError(f"lakefile: globs line not on one line: {line!r}")
    close(block)
    if not libs:
        raise SetupError("lakefile: no [[lean_lib]] block")
    return libs


def modules(lean, libs):
    """The module names of the libraries: every *.lean file under <lean>/<library>/."""
    ms = []
    for r in libs:
        fs = sorted((lean / r).rglob("*.lean")) if (lean / r).is_dir() else []
        if not fs:
            raise SetupError(f"library {r}: no *.lean file under {lean / r}")
        for f in fs:
            ms.append(".".join(f.relative_to(lean).with_suffix("").parts))
    return ms


def list_files(d):
    """The hand-list files: every *.lean file directly in d, sorted by name."""
    fs = sorted(f for f in d.glob("*.lean") if f.is_file()) if d.is_dir() else []
    if not fs:
        raise SetupError(f"no hand-list file (*.lean) in {d}")
    return fs


def hand_names(d=None):
    names = []
    for f in list_files(LIST_DIR if d is None else d):
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
    libs = libraries(LAKEFILE.read_text())
    ms = modules(LEAN, libs)
    list_files(LIST_DIR)
    pre = ["lake", "build", "--no-build"] + ms
    p = subprocess.run(pre, cwd=LEAN, capture_output=True, text=True)
    fails = [l for l in (p.stdout + p.stderr).splitlines() if l.startswith("- ")]
    print("PRECHECK rc", p.returncode, "modules", len(ms), fails[:10], flush=True)
    info = {"modules": len(ms), "precheck": {"argv": "lake build --no-build <modules>", "rc": p.returncode,
                                             "failures": fails}}
    if p.returncode != 0:
        json.dump({**info, "verdict": "FAIL", "reason": "precheck"}, open(out, "w"), indent=1)
        return 2
    roots = sum((["--root", r] for r in libs), [])
    argv = ["lake", "env", "lean", "--run", str(DUMP)] + roots + ms
    if extra_paths:  # negative control only: a scratch .olean outside the tree
        argv = ["lake", "env", "sh", "-c", 'LEAN_PATH="$0:$LEAN_PATH" exec "$@"', ":".join(extra_paths),
                "lean", "--run", str(DUMP)] + roots + ms + extra_mods
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
    bad = []

    def expect(name, got, want):
        if got != want:
            bad.append((name, got, want))

    # 1. check(): crafted dumps. The names use an invented root `Lib`, not a library of the tree.
    H = "# decl_dump v1 lean=x githash=y roots=Lib"
    ok_rows = "\n".join([H, "Lib.a\ttheorem\t0\t-\tpropext", "Lib.b'\ttheorem\t0\t-\t-",
                         "Lib.c\tdef\t0\t1\tClassical.choice,Quot.sound,propext"])
    cases = [
        ("clean", ok_rows, ["Lib.a", "Lib.b'"], "PASS"),
        ("sorry", ok_rows + "\nLib.s\ttheorem\t0\t-\tpropext,sorryAx", ["Lib.a"], "FAIL"),
        ("sorry_prime", ok_rows + "\nLib.s'\ttheorem\t0\t-\tsorryAx", ["Lib.a"], "FAIL"),
        ("axiom", ok_rows + "\nLib.t\ttheorem\t0\t-\tLib.myAx,propext", ["Lib.a"], "FAIL"),
        ("missing", ok_rows, ["Lib.a", "Lib.zz"], "FAIL"),
        ("prime_missing", ok_rows, ["Lib.a'"], "FAIL"),
        ("empty", H, [], "FAIL"),
    ]
    for name, tsv, must, want in cases:
        h, rows = parse(tsv)
        expect(name, check(rows, h, must)["verdict"], want)

    def setup_fails(f):
        try:
            f()
        except SetupError:
            return True
        return False

    # 2. Lakefile parsing: only [[lean_lib]] blocks count; [[require]] and [[input_dir]] names do not.
    lake = "\n".join([
        'name = "pkg"', 'defaultTargets = ["LibA"]', "", "[[require]]", 'name = "Dependency"', 'rev = "0"', "",
        "# [[lean_lib]] in a comment", "[[lean_lib]]", 'name = "LibA"   # trailing comment', 'globs = ["LibA.+"]', "",
        "[[input_dir]]", 'name = "some_input"', 'path = "LibA"', "",
        "[[lean_lib]]", 'name = "LibB"', 'globs = ["LibB.+"]', 'needs = ["some_input"]', ""])
    expect("lakefile_libs", libraries(lake), ["LibA", "LibB"])
    expect("lakefile_bad_glob", setup_fails(lambda: libraries(lake.replace('["LibB.+"]', '["LibB"]'))), True)
    expect("lakefile_no_glob", setup_fails(lambda: libraries(lake.replace('globs = ["LibB.+"]', ""))), True)
    expect("lakefile_no_lib", setup_fails(lambda: libraries('name = "pkg"\n[[require]]\nname = "Dependency"\n')), True)
    real = libraries(LAKEFILE.read_text())
    expect("lakefile_real_nonempty", bool(real), True)
    expect("lakefile_real_modules", setup_fails(lambda: modules(LEAN, real)), False)

    with tempfile.TemporaryDirectory() as t:
        t = pathlib.Path(t)
        # 3. Module discovery: a library without a directory or without a module fails.
        (t / "lean" / "LibA" / "Sub").mkdir(parents=True)
        (t / "lean" / "LibA" / "Sub" / "M.lean").write_text("")
        (t / "lean" / "LibB").mkdir()
        expect("modules_known", modules(t / "lean", ["LibA"]), ["LibA.Sub.M"])
        expect("modules_unknown_root", setup_fails(lambda: modules(t / "lean", ["LibA", "NoSuchLib"])), True)
        expect("modules_empty_root", setup_fails(lambda: modules(t / "lean", ["LibA", "LibB"])), True)
        # 4. Hand-list discovery: every *.lean file of the directory counts, a new file needs no gate change.
        d = t / "lists"
        expect("lists_no_dir", setup_fails(lambda: list_files(d)), True)
        d.mkdir()
        expect("lists_empty_dir", setup_fails(lambda: list_files(d)), True)
        (d / "first.lean").write_text("import LibA.Sub.M\n#print axioms Lib.a\n#print axioms Lib.b'\n")
        (d / "notes.txt").write_text("#print axioms Lib.notInAList\n")
        h, rows = parse(ok_rows)
        expect("lists_found", hand_names(d), ["Lib.a", "Lib.b'"])
        expect("lists_pass", check(rows, h, hand_names(d))["verdict"], "PASS")
        (d / "planted.lean").write_text("#print axioms Lib.planted\n")
        r = check(rows, h, hand_names(d))
        expect("lists_planted_missing", (r["verdict"], r["hand_list_missing"]), ("FAIL", ["Lib.planted"]))

    names = hand_names()
    if not names or any(" " in n for n in names):
        bad.append(("hand_names", len(names), "nonempty"))
    print("selftest", "PASS" if not bad else f"FAIL {bad}", "libraries", len(real), "hand-list files",
          len(list_files(LIST_DIR)), "hand-list names", len(names))
    return 1 if bad else 0


def main(a):
    try:
        if a == ["--selftest"]:
            return selftest()
        if a[:1] == ["check"] and len(a) == 3:
            return cmd_check(a[1], a[2])
        if a[:1] == ["run"] and len(a) >= 3:
            xp, xm, rest = [], [], a[3:]
            while rest:
                if rest[0] == "--extra-lean-path":
                    xp.append(rest[1])
                elif rest[0] == "--extra-module":
                    xm.append(rest[1])
                else:
                    return __doc__
                rest = rest[2:]
            return cmd_run(a[1], a[2], xp, xm)
    except SetupError as e:
        print("SETUP FAIL", e, file=sys.stderr)
        return 2
    return __doc__


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
