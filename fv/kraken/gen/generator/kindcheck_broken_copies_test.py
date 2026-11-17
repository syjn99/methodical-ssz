#!/usr/bin/env python3
"""Broken copies of kindcheck.py: one copy per sub-rule of rule 13, with that sub-rule switched off.
A replacement text switches the sub-rule off: it removes the error report and keeps the control flow.
The selftest of every copy must fail in a selftest control of that sub-rule.
A copy counts as detected only when all of these conditions are true:
- its selftest exits with code 1 and writes no Python traceback;
- its last stdout line starts with `selftest FAIL`;
- the failing cases of that line include at least one expected case of the variant.
Each other result is BAD: a crash, a passing selftest, or a failure only in other cases.
A BAD result shows a sub-rule that no selftest control tests.

usage: python3 -I -B kindcheck_broken_copies_test.py     (run from anywhere)
exit 0 = every copy is detected; 1 = a copy is BAD, or a pattern is not found once

Each copy is written next to kindcheck.py (kindcheck.py finds the tree from its own path) and deleted after its run.
Not listed: the 13b def-line test. The def count and the layout lookup of 13b / 13c catch every def mutant
of the selftest, so a broken copy of that sub-check does not fail the selftest.
"""
import ast
import pathlib
import subprocess
import sys

K = pathlib.Path(__file__).resolve().with_name("kindcheck.py")
# variant -> (text in kindcheck.py, replacement that switches the sub-rule off, expected failing selftest cases)
BROKEN = {
    "13b-banned-ignored": ('    if BANNED.search(body):\n        errs.append("rule 13b: banned token")',
                           '    if False:\n        errs.append("rule 13b: banned token")',
                           {"fast_path_sorry"}),
    "13b-theorem-list-ignored": ('        return errs + [f"rule 13b: theorems {thms}, expected {want} [+ {P}_fast_statement_tie]"], info',
                                 '        return errs, info',
                                 {"fast_path_kind_line_missing", "fast_path_extra_theorem"}),
    "13b-set-option-ignored": ('            if l.startswith("set_option ") and l not in', '            if False and l not in',
                               {"fast_path_heartbeats"}),
    "13c-kind-line-ignored": ('        if fast_path_norm(hdr) != fast_path_norm(line) or rl[0]',
                              '        if False and fast_path_norm(hdr) != fast_path_norm(line) or rl[0]',
                              {"fast_path_fields_param", "fast_path_boundary_pc", "fast_path_boundary_done",
                               "fast_path_boundary_reg_dropped", "fast_path_kind_name_swapped", "fast_path_kind_const",
                               "fast_path_beacon_block_header_state_slot"}),
    "13c-layout-ignored": ('            if fileL.get(k) != X["L"][k]:', '            if False:',
                           {"fast_path_layout_frame", "fast_path_layout_gd", "fast_path_layout_pre_order",
                            "fast_path_layout_exs", "fast_path_layout_post_fld", "fast_path_layout_lens",
                            "fast_path_historical_summary_frame_state"}),
    "13c-binding-ignored": ('    if not bound:\n', '    if False:\n', {"fast_path_const_unbound"}),
    "13c-sha-ignored": ('        if tsha(S) != J["assembly_sha256"] or tsha(IR) != J["ir_sha256"]:', '        if False:',
                        {"fast_path_json_sha"}),
    "13c-recompute-wrong-order": ('        mem = [-8] + sorted(o for o in first if o > 0) + [o for o in first if o < 0 and o not in (-8, RS)] + \\\n',
                                  '        mem = [-8] + sorted(o for o in first if o > 0) + sorted(o for o in first if o < 0 and o not in (-8, RS)) + \\\n',
                                  {"fast_path_good_historical_summary_frame_test", "fast_path_recompute_DepositMessage",
                                   "fast_path_recompute_HistoricalSummary"}),
    "13d-chain-ignored": ('        if fp.count(t) != 1:', '        if False:', {"fast_path_fast_skips_f0"}),
    "13e-generated-name-ignored": ('                errs.append(f"rule 13e: {x} is a generated name")', '                pass',
                                   {"fast_path_statement_generated"}),
    "13e-via-ignored": ('            if via and via not in FAST_PATH_VIA:', '            if False:',
                        {"fast_path_statement_via_unknown"}),
}


def failing_cases(line):
    """The case names of a `selftest FAIL [...] (n cases ...)` line, or None for a line of another form."""
    if not line.startswith("selftest FAIL "):
        return None
    try:
        return [e[0] for e in ast.literal_eval(line[len("selftest FAIL "):].rpartition(" (")[0])]
    except (ValueError, SyntaxError, TypeError, IndexError):
        return None


def check_variant(src, name, old, new, expect):
    """(ok, message) for one broken copy of the kindcheck.py text src."""
    if src.count(old) != 1:
        return False, f"the pattern occurs {src.count(old)} times in kindcheck.py (expected 1)"
    f = K.with_name(f"_kindcheck_broken_{name.replace('-', '_')}.py")
    f.write_text(src.replace(old, new))
    try:
        r = subprocess.run([sys.executable, "-I", "-B", str(f), "--selftest"], capture_output=True, text=True)
    finally:
        f.unlink()
    out = r.stdout.strip().split("\n")[-1]
    head = f"selftest exit {r.returncode}: "
    if "Traceback" in r.stderr:
        return False, head + "Python traceback: " + r.stderr.strip().split("\n")[-1][:200]
    cases = failing_cases(out)
    if r.returncode != 1 or cases is None:
        return False, head + "no `selftest FAIL` result: " + (out or "(no stdout)")[:200]
    hit = sorted(set(cases) & expect)
    if not hit:
        return False, head + f"failing cases {cases} include no expected case {sorted(expect)}"
    other = [c for c in cases if c not in expect]
    return True, head + f"selftest FAIL in expected cases {hit}" + (f", other cases {other}" if other else "")


def main():
    src = K.read_text()
    bad = 0
    for name, (old, new, expect) in BROKEN.items():
        ok, msg = check_variant(src, name, old, new, expect)
        bad |= not ok
        print(("OK  " if ok else "BAD ") + f"{name}: {msg}")
    print("kindcheck_broken_copies_test:", "PASS (each broken copy fails in an expected selftest case)" if not bad else "FAIL")
    return 1 if bad else 0


if __name__ == "__main__":
    if len(sys.argv) != 1:
        print(__doc__)
        sys.exit(2)
    sys.exit(main())
