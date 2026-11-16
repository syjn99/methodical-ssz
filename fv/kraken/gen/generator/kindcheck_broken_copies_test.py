#!/usr/bin/env python3
"""Broken copies of kindcheck.py: one copy per sub-rule of rule 13, with that sub-rule switched off.
The selftest of every copy must fail. A copy whose selftest passes shows a sub-rule that no selftest control tests.

usage: python3 -I -B kindcheck_broken_copies_test.py     (run from anywhere)
exit 0 = the selftest of every copy fails; 1 = a copy passes its selftest, or a pattern is not found once

Each copy is written next to kindcheck.py (kindcheck.py finds the tree from its own path) and deleted after its run.
Not listed: the 13b def-line test. The def count and the layout lookup of 13b / 13c catch every def mutant
of the selftest, so a broken copy of that sub-check does not fail the selftest.
"""
import pathlib
import subprocess
import sys

K = pathlib.Path(__file__).resolve().with_name("kindcheck.py")
# variant -> (text in kindcheck.py, replacement that switches the sub-rule off)
BROKEN = {
    "13b-banned-ignored": ('    if BANNED.search(body):\n        errs.append("rule 13b: banned token")',
                           '    if False:\n        errs.append("rule 13b: banned token")'),
    "13b-theorem-list-ignored": ('    if thms not in (want, want + [f"{P}_statement"]):', '    if False:'),
    "13b-set-option-ignored": ('            if l.startswith("set_option ") and l not in', '            if False and l not in'),
    "13c-kind-line-ignored": ('        if fast_path_norm(hdr) != fast_path_norm(line) or rl[0]',
                              '        if False and fast_path_norm(hdr) != fast_path_norm(line) or rl[0]'),
    "13c-layout-ignored": ('            if fileL.get(k) != X["L"][k]:', '            if False:'),
    "13c-binding-ignored": ('    if not bound:\n', '    if False:\n'),
    "13c-sha-ignored": ('        if tsha(S) != J["assembly_sha256"] or tsha(IR) != J["ir_sha256"]:', '        if False:'),
    "13c-recompute-wrong-order": ('        mem = [-8] + sorted(o for o in first if o > 0) + [o for o in first if o < 0 and o not in (-8, RS)] + \\\n',
                                  '        mem = [-8] + sorted(o for o in first if o > 0) + sorted(o for o in first if o < 0 and o not in (-8, RS)) + \\\n'),
    "13d-chain-ignored": ('        if fp.count(t) != 1:', '        if False:'),
    "13e-generated-name-ignored": ('                errs.append(f"rule 13e: {x} is a generated name")', '                pass'),
    "13e-via-ignored": ('            if via and via not in FAST_PATH_VIA:', '            if False:'),
}


def main():
    src = K.read_text()
    bad = 0
    for name, (old, new) in BROKEN.items():
        if src.count(old) != 1:
            print(f"BAD {name}: the pattern occurs {src.count(old)} times in kindcheck.py (expected 1)")
            bad = 1
            continue
        f = K.with_name(f"_kindcheck_broken_{name.replace('-', '_')}.py")
        f.write_text(src.replace(old, new))
        try:
            r = subprocess.run([sys.executable, "-I", "-B", str(f), "--selftest"], capture_output=True, text=True)
        finally:
            f.unlink()
        last = (r.stdout.strip().split("\n") or [""])[-1] or "(no stdout) stderr: " + r.stderr.strip().split("\n")[-1]
        ok = r.returncode != 0
        bad |= not ok
        print(("OK  " if ok else "BAD ") + f"{name}: selftest exit {r.returncode}: {last[:220]}")
    print("kindcheck_broken_copies_test:", "PASS (every broken copy fails its selftest)" if not bad else "FAIL")
    return 1 if bad else 0


if __name__ == "__main__":
    if len(sys.argv) != 1:
        print(__doc__)
        sys.exit(2)
    sys.exit(main())
