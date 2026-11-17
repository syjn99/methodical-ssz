#!/bin/sh
# Python-only checks of the tree. No Lean, no build.
#
# usage (from the repository root):
#   sh fv/kraken/gen/checks/python_checks.sh <out dir>
#
#   <out dir>  directory for the outputs. It must not exist. Delete it later with `trash`.
#
# Each check writes <name>.txt and one line `<name> rc=<n>` to summary.txt.
# Expected: rc=0 for every check.
# kindcheck.py runs on the outputs of gen/generator/generator.py: lean/Prysm/*/Generated*.lean, without the
# identity and specification modules whose names also start with Generated.
set -u
if [ $# -ne 1 ]; then
  sed -n '2,12p' "$0" >&2
  exit 2
fi
OUT=$1
if [ -e "$OUT" ]; then
  echo "error: $OUT exists. Delete it with trash, or give another directory." >&2
  exit 2
fi
mkdir -p "$OUT" || exit 2
OUT=$(cd "$OUT" && pwd)
REPO=$(git rev-parse --show-toplevel) || exit 2
cd "$REPO/fv/kraken" || exit 2
: > "$OUT/summary.txt"

run() {
  name=$1; shift
  "$@" > "$OUT/$name.txt" 2>&1
  echo "$name rc=$?" | tee -a "$OUT/summary.txt"
}

run axioms_gate_selftest python3 -I -B gen/checks/axioms_gate.py --selftest
run deposit_data_include_check python3 -I -B gen/checks/deposit_data_include_check.py
run deposit_data_include_check_selftest python3 -I -B gen/checks/deposit_data_include_check.py --selftest
run kindcheck_selftest python3 -I -B gen/generator/kindcheck.py --selftest
run kindcheck_broken_copies_test python3 -I -B gen/generator/kindcheck_broken_copies_test.py
run fast_path_layout python3 -I -B gen/checks/fast_path_layout.py

KINDCHECK_INPUTS=$(ls lean/Prysm/*/Generated*.lean | grep -v -e GeneratedEncodeFastPathSpec)
# shellcheck disable=SC2086
run kindcheck_generated python3 -I -B gen/generator/kindcheck.py $KINDCHECK_INPUTS
run negative_selftest python3 -I -B gen/checks/negative.py --selftest
run negative_selftest_timeout python3 -I -B gen/checks/negative.py --selftest-timeout
# git ls-files in fv/kraken prints paths relative to fv/kraken.
CASES=$(git ls-files '*negative-cases*.json' | sort)
echo "$CASES" > "$OUT/negative_case_files.txt"
# shellcheck disable=SC2086
run negative_check_cases python3 -I -B gen/checks/negative.py --check-cases $CASES
# shellcheck disable=SC2086
run negative_case_ranges \
  python3 -I -B gen/checks/negative_case_ranges.py $CASES

# Every tracked Python file under fv/ parses (the py_compile check without .pyc files).
run python_syntax python3 -I -B -c '
import ast, subprocess, sys
root = subprocess.run(["git", "rev-parse", "--show-toplevel"], capture_output=True, text=True).stdout.strip()
files = subprocess.run(["git", "-C", root, "ls-files", "fv/*.py"], capture_output=True, text=True).stdout.split()
bad = 0
for f in files:
    try:
        ast.parse(open(root + "/" + f, encoding="utf-8").read(), f)
    except SyntaxError as e:
        print("SYNTAX", f, e); bad += 1
print(len(files), "files,", bad, "syntax errors")
sys.exit(1 if bad else 0)'
echo "outputs in $OUT"
