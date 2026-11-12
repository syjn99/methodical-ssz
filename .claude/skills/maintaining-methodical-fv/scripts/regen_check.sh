#!/bin/sh
# Rerun a generator into scratch (twice) and compare with the committed output.
#
# usage: regen_check.sh COMMITTED_PATH -- GENERATOR ARGV...
#
# The generator runs with the environment variable REGEN_OUT set to a fresh
# scratch path. It must write there what it would write to COMMITTED_PATH
# (one file, or a directory tree). The generator runs twice, into two scratch
# paths, so nondeterminism is caught separately from drift.
#
# Exit codes:
#   0 same: both runs equal each other and the committed output
#   1 differ: deterministic output differs from the committed output (diff shown)
#   2 usage error (no "--", committed path missing)
#   3 generator failed (its exit code is printed); this is never a pass
#   4 generator exited 0 but wrote nothing at REGEN_OUT
#   5 nondeterministic: the two runs differ from each other
#
# Limits: byte comparison only. It says nothing about whether the committed
# output is correct, and a generator that reads the committed output could
# reproduce it trivially. Heavy generators (go run, lake, the sszgen generator)
# must be run under the heavy-job gate: gate the whole regen_check.sh call.
# The scratch directory is removed on exit 0; otherwise its path is printed.
set -u
if [ $# -lt 3 ] || [ "$2" != "--" ]; then
  echo "usage: regen_check.sh COMMITTED_PATH -- GENERATOR ARGV..." >&2
  exit 2
fi
committed=$1
shift 2
if [ ! -e "$committed" ]; then
  echo "regen_check: committed path not found: $committed" >&2
  exit 2
fi
scratch=$(mktemp -d "${TMPDIR:-/tmp}/regen_check.XXXXXX") || exit 2
for run in 1 2; do
  REGEN_OUT=$scratch/run$run "$@"
  rc=$?
  if [ $rc -ne 0 ]; then
    echo "GENERATOR-FAILED run=$run exit=$rc scratch=$scratch"
    exit 3
  fi
  if [ ! -e "$scratch/run$run" ]; then
    echo "NO-OUTPUT run=$run scratch=$scratch"
    exit 4
  fi
done
if ! diff -r "$scratch/run1" "$scratch/run2" > "$scratch/nondet.diff" 2>&1; then
  echo "NONDETERMINISTIC scratch=$scratch"
  head -40 "$scratch/nondet.diff"
  exit 5
fi
if ! diff -r "$committed" "$scratch/run1" > "$scratch/drift.diff" 2>&1; then
  echo "DIFFER committed=$committed scratch=$scratch"
  head -40 "$scratch/drift.diff"
  exit 1
fi
rm -r "$scratch"
echo "SAME committed=$committed"
exit 0
