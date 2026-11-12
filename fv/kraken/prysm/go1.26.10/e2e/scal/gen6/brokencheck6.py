# One deliberately broken copy of kindcheck.py per sub-rule of rule 13; each copy's selftest must FAIL.
# usage (cwd = fv/kraken): python3 -I -B brokencheck6.py   -> one line per copy, exit 0 iff every copy fails
import pathlib, subprocess, sys
K = pathlib.Path("gen/scal/kindcheck.py")
src = K.read_text()
# Not listed: the 13b def-line test. Its broken copy passed the selftest (run 1, brokencheck6-run1.out): the def count
# and the layout lookup of 13b / 13c catch every def mutant of the selftest, so that sub-check is redundant.
BROKEN = {
    "13a-pins-ignored": ('        if blobs.get(m) != b:\n            errs.append(f"rule 13a', '        if False:\n            errs.append(f"rule 13a'),
    "13b-banned-ignored": ('    if BANNED.search(body):\n        errs.append("rule 13b: banned token")',
                           '    if False:\n        errs.append("rule 13b: banned token")'),
    "13b-theorem-list-ignored": ('    if thms not in (want, want + [f"{P}_stmt"]):', '    if False:'),
    "13b-set-option-ignored": ('            if l.startswith("set_option ") and l not in', '            if False and l not in'),
    "13c-kind-line-ignored": ('        if g6_norm(hdr) != g6_norm(line) or rl[0]', '        if False and g6_norm(hdr) != g6_norm(line) or rl[0]'),
    "13c-layout-ignored": ('            if fileL.get(k) != X["L"][k]:', '            if False:'),
    "13c-binding-ignored": ('    if not bound:\n', '    if False:\n'),
    "13c-sha-ignored": ('        if tsha(S) != J["S_sha256"] or tsha(IR) != J["ir_sha256"]:', '        if False:'),
    "13c-recompute-wrong-order": ('        mem = [-8] + sorted(o for o in first if o > 0) + [o for o in first if o < 0 and o not in (-8, RS)] + \\\n',
                                  '        mem = [-8] + sorted(o for o in first if o > 0) + sorted(o for o in first if o < 0 and o not in (-8, RS)) + \\\n'),
    "13d-chain-ignored": ('        if fp.count(t) != 1:', '        if False:'),
    "13e-generated-name-ignored": ('                errs.append(f"rule 13e: {x} is a generated name")', '                pass'),
    "13e-via-ignored": ('            if via and via not in GEN6_VIA:', '            if False:'),
}
bad = 0
for name, (old, new) in BROKEN.items():
    assert src.count(old) == 1, name
    f = K.with_name(f"_kc_broken_{name.replace('-', '_')}.py")
    f.write_text(src.replace(old, new))
    try:
        r = subprocess.run([sys.executable, "-I", "-B", str(f), "--selftest"], capture_output=True, text=True)
    finally:
        f.unlink()
    last = (r.stdout.strip().split("\n") or [""])[-1] or "(no stdout) stderr: " + r.stderr.strip().split("\n")[-1]
    ok = r.returncode != 0
    bad |= not ok
    print(("OK  " if ok else "BAD ") + f"{name}: selftest exit {r.returncode}: {last[:220]}")
print("brokencheck6:", "PASS (every broken copy fails its selftest)" if not bad else "FAIL")
sys.exit(1 if bad else 0)
