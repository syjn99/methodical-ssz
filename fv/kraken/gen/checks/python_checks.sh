#!/bin/sh
# Python-only checks of the tree. No Lean, no build.
#
# usage (from the repository root):
#   sh fv/kraken/gen/checks/python_checks.sh <out dir>
#
#   <out dir>  directory for the outputs. It must not exist. Delete it later with `trash`.
#
# Each check writes <name>.txt and one line `<name> rc=<n>` to summary.txt.
# To check a change, run it before and after the change, with two out dirs, and compare: `diff -r <before> <after>`.
# Expected: the same rc for every check. A text difference needs a stated reason (for example a library count).
# A check whose script is not in the tree gets the line `<name> not run (no <script>)`.
# The default kindcheck list also has example files that no generator writes (for example the hand-written `Prysm/*/DecodeStepExamples.lean`).
# So kindcheck_generated can exit 1 on an unchanged tree too. `kindcheck.py --partial` never exits 0 (see its usage text).
#
# Environment:
#   KINDCHECK_FILES  the generated Lean files for kindcheck.py, as paths relative to fv/kraken.
#                    Default: the non-partial generated and example modules lean/Prysm/*/Generated*.lean and
#                    lean/Prysm/*/Decode*Example*.lean, without the identity and specification modules whose
#                    names also start with Generated.
#   PARTIAL_FILES    the partial generator outputs for `kindcheck.py --partial`, relative to fv/kraken.
#                    Default: lean/Prysm/*/Generated*Partial.lean.
set -u
if [ $# -ne 1 ]; then
  sed -n '2,22p' "$0" >&2
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
  name=$1; script=$2; shift 2
  if [ ! -f "$script" ]; then
    echo "$name not run (no $script)" | tee -a "$OUT/summary.txt"
    return
  fi
  "$@" > "$OUT/$name.txt" 2>&1
  echo "$name rc=$?" | tee -a "$OUT/summary.txt"
}

run axioms_gate_selftest gen/checks/axioms_gate.py python3 -I -B gen/checks/axioms_gate.py --selftest
run deposit_data_include_check gen/checks/deposit_data_include_check.py python3 -I -B gen/checks/deposit_data_include_check.py
run deposit_data_include_check_selftest gen/checks/deposit_data_include_check.py python3 -I -B gen/checks/deposit_data_include_check.py --selftest
run kindcheck_selftest gen/generator/kindcheck.py python3 -I -B gen/generator/kindcheck.py --selftest
run fast_path_layout gen/checks/fast_path_layout.py python3 -I -B gen/checks/fast_path_layout.py

if [ -z "${KINDCHECK_FILES:-}" ]; then
  KINDCHECK_FILES=$(ls lean/Prysm/*/Generated*.lean lean/Prysm/*/Decode*Example*.lean 2>/dev/null | grep -v -e 'Partial\.lean$' -e SameAsHand -e GeneratedEncodeFastPathSpec -e CompositionKind)
fi
if [ -n "$KINDCHECK_FILES" ]; then
  # shellcheck disable=SC2086
  run kindcheck_generated gen/generator/kindcheck.py python3 -I -B gen/generator/kindcheck.py $KINDCHECK_FILES
else
  echo "kindcheck_generated not run (no files)" | tee -a "$OUT/summary.txt"
fi
if [ -z "${PARTIAL_FILES:-}" ]; then
  PARTIAL_FILES=$(ls lean/Prysm/*/Generated*Partial.lean 2>/dev/null)
fi
for f in $PARTIAL_FILES; do
  run "kindcheck_partial_$(basename "$(dirname "$f")")_$(basename "$f" .lean)" gen/generator/kindcheck.py python3 -I -B gen/generator/kindcheck.py --partial "$f"
done

run negative_selftest gen/checks/negative.py python3 -I -B gen/checks/negative.py --selftest
# git ls-files in fv/kraken prints paths relative to fv/kraken.
CASES=$(git ls-files '*negative-cases*.json' | sort)
echo "$CASES" > "$OUT/negative_case_files.txt"
# shellcheck disable=SC2086
run negative_check_cases gen/checks/negative.py python3 -I -B gen/checks/negative.py --check-cases $CASES
# shellcheck disable=SC2086
run negative_case_ranges gen/checks/negative_case_ranges.py \
  python3 -I -B gen/checks/negative_case_ranges.py $CASES

# Every tracked Python file under fv/ parses (the py_compile check without .pyc files).
run python_syntax gen/checks/python_checks.sh python3 -I -B -c '
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
