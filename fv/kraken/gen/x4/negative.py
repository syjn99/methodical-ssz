#!/usr/bin/env python3
"""Negative tests of the X4 proofs: one machine-code mutation per designated theorem, plus a control.

Usage:
  negative.py prepare <work> <desccheck-result> <desc-dir>   mutant .S copies, Lean files, run.sh
  negative.py evaluate <work> <out.json>                       after `sh <work>/run.sh` in the gate

Each case writes a copy of the normalised .S with one instruction changed, generates the obligation
with gen/x4/x4gen.py --mutant (statement and proof generated from the original code; only the code
constant is the mutant) and elaborates it alone. Expected: the mutant fails with its first error
inside the designated theorem; the control (an unchanged copy through the same path) elaborates.
Python 3 standard library only. Run with python3 -I -B.
"""
import json
import os
import re
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
KRAKEN = os.path.normpath(os.path.join(HERE, "..", ".."))
NORM = os.path.join(KRAKEN, "link", "out", "norm")
T = "github.com/OffchainLabs/methodical-ssz/fv/kraken/target"

CASES = [  # id, type, method, designated obligation, old instruction, new instruction
    ("sc-size-imm", "Scalars", "SizeSSZ", "size", "mov $0x10,%eax", "mov $0x11,%eax"),
    ("sc-accept-ja", "Scalars", "UnmarshalSSZ", "accept", "ja L_target.Scalars.UnmarshalSSZ_41", "jae L_target.Scalars.UnmarshalSSZ_41"),
    ("sc-rbool-cmp", "Scalars", "UnmarshalSSZ", "reject_bool", "cmp $0x1,%cl", "cmp $0x2,%cl"),
    ("sc-rsize-cmp", "Scalars", "UnmarshalSSZ", "reject_size", "cmp $0x10,%rcx", "cmp $0x11,%rcx"),
    ("sc-marshal-add", "Scalars", "MarshalSSZTo", "marshal", "add $0x2,%rdx", "add $0x3,%rdx"),
    ("lu-size-add", "ListU64", "SizeSSZ", "size", "add $0x4,%rax", "add $0x5,%rax"),
    ("lu-short-cmp", "ListU64", "UnmarshalSSZ", "reject_short", "cmp $0x4,%rcx", "cmp $0x3,%rcx"),
    ("lu-off-cmp", "ListU64", "UnmarshalSSZ", "reject_offset", "cmp $0x4,%rdx", "cmp $0x5,%rdx"),
    ("lu-mis-test", "ListU64", "UnmarshalSSZ", "reject_misaligned", "test $0x7,%rcx", "test $0x3,%rcx"),
    ("lu-big-cmp", "ListU64", "UnmarshalSSZ", "reject_toobig", "cmp $0x10,%rcx", "cmp $0x11,%rcx"),
    ("lu-acc-store", "ListU64", "UnmarshalSSZ", "accept", "mov %rdx,0x8(%rsi)", "mov %rdx,0x18(%rsi)"),
    ("lu-marshal-off", "ListU64", "MarshalSSZTo", "marshal", "movl $0x4,-0x4(%rdx,%rbx,1)", "movl $0x5,-0x4(%rdx,%rbx,1)"),
    # statement mutation (method "stmt"): the generated composition must fail if it claims another length
    ("sc-compose-len", "Scalars", "stmt", "compose", "st'.data.regs.rbx = dlen + 16", "st'.data.regs.rbx = dlen + 17"),
]
import sys as _sys
if "--ids" in _sys.argv:   # restrict to the named cases (the others were run before)
    _ids = _sys.argv[_sys.argv.index("--ids") + 1].split(",")
    CASES = [c for c in CASES if c[0] in _ids]
    del _sys.argv[_sys.argv.index("--ids"):_sys.argv.index("--ids") + 2]


def prepare(work, result, ddir):
    os.makedirs(work, exist_ok=True)
    cases, run = [], ["#!/bin/sh", "# elaborate every case alone; one 'id rc' line each", f": > {work}/rc.txt"]
    for cid, ty, meth, obl, old, new in CASES:
        if meth == "stmt":
            for kind in ("mutant", "control"):
                name = f"{cid}-{kind}"
                lf = os.path.join(work, f"{name}.lean")
                ns = "Gen1cX4.Neg." + re.sub(r"\W", "_", name)
                r = subprocess.run([sys.executable, "-I", "-B", os.path.join(HERE, "x4gen.py"), "--desccheck-result", result,
                                    "--desc-dir", ddir, "--type", f"{T}.{ty}", "--out-lean", lf, "--only", f"accept,marshal,{obl}",
                                    "--ns", ns], capture_output=True, text=True)
                assert r.returncode == 0, r.stderr
                text = open(lf).read()
                if kind == "mutant":
                    assert text.count(old) == 1, (cid, old)
                    text = text.replace(old, new)
                open(lf, "w").write(text)
                lines = text.split("\n")
                lo = next(i for i, l in enumerate(lines) if l.startswith(f"theorem {obl} ")) + 1
                hi = next(i for i in range(lo, len(lines)) if lines[i] == "") + 1
                cases.append({"id": cid, "kind": kind, "type": ty, "method": meth, "designated": f"{ns}.{obl}",
                              "mutation": f"statement '{old}' -> '{new}'" if kind == "mutant" else "none (unchanged)",
                              "lean": lf, "theorem_lines": [lo, hi], "log": os.path.join(work, f"{name}.log")})
                run.append(f"lake env lean {lf} > {work}/{name}.log 2>&1; echo \"{name} $?\" >> {work}/rc.txt")
            continue
        src = open(os.path.join(NORM, f"target.{ty}.{meth}.S")).read()
        assert src.count("  " + old + "\n") == 1, (cid, old)
        for kind, text in (("mutant", src.replace("  " + old + "\n", "  " + new + "\n")), ("control", src)):
            name = f"{cid}-{kind}"
            sf = os.path.join(work, f"{name}.S")
            open(sf, "w").write(text)
            lf = os.path.join(work, f"{name}.lean")
            ns = "Gen1cX4.Neg." + re.sub(r"\W", "_", name)
            r = subprocess.run([sys.executable, "-I", "-B", os.path.join(HERE, "x4gen.py"), "--desccheck-result", result,
                                "--desc-dir", ddir, "--type", f"{T}.{ty}", "--out-lean", lf, "--only", obl, "--ns", ns,
                                "--mutant", f"{meth}={sf}"], capture_output=True, text=True)
            assert r.returncode == 0, r.stderr
            lines = open(lf).read().split("\n")
            lo = next(i for i, l in enumerate(lines) if l.startswith(f"theorem {obl} ")) + 1
            hi = next(i for i in range(lo, len(lines)) if lines[i] == "") + 1
            cases.append({"id": cid, "kind": kind, "type": ty, "method": meth, "designated": f"{ns}.{obl}",
                          "mutation": f"'{old}' -> '{new}'" if kind == "mutant" else "none (unchanged copy)",
                          "lean": lf, "theorem_lines": [lo, hi], "log": os.path.join(work, f"{name}.log")})
            run.append(f"lake env lean {lf} > {work}/{name}.log 2>&1; echo \"{name} $?\" >> {work}/rc.txt")
    open(os.path.join(work, "run.sh"), "w").write("\n".join(run) + "\n")
    json.dump(cases, open(os.path.join(work, "cases.json"), "w"), indent=1)
    print(json.dumps({"cases": len(cases)}))


def evaluate(work, out):
    cases = json.load(open(os.path.join(work, "cases.json")))
    rc = dict(l.split() for l in open(os.path.join(work, "rc.txt")))
    rows, bad = [], 0
    for c in cases:
        name = f"{c['id']}-{c['kind']}"
        log = open(c["log"]).read()
        errs = [(int(m[1]), m[2]) for m in re.finditer(r"\.lean:(\d+):\d+: error[^:]*: ?(.*)", log)]
        lo, hi = c["theorem_lines"]
        if c["kind"] == "control":
            ok = rc.get(name) == "0" and not errs
        else:
            ok = rc.get(name) not in ("0", None) and bool(errs) and lo <= errs[0][0] <= hi
        bad += not ok
        rows.append({"id": c["id"], "kind": c["kind"], "designated": c["designated"], "mutation": c["mutation"],
                     "exit": rc.get(name), "first_error": f"line {errs[0][0]}: {errs[0][1][:120]}" if errs else None,
                     "theorem_lines": c["theorem_lines"], "as_expected": ok})
    res = {"schema": "fvphase1c.x4-negative/1", "cases": len(rows), "as_expected": len(rows) - bad, "rows": rows}
    json.dump(res, open(out, "w"), indent=1)
    print(json.dumps({"cases": len(rows), "as_expected": len(rows) - bad}))
    return 0 if not bad else 1


if __name__ == "__main__":
    if sys.argv[1] == "prepare":
        prepare(*sys.argv[2:5])
    else:
        sys.exit(evaluate(*sys.argv[2:4]))
