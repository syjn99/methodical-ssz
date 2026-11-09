#!/bin/sh
# X4 check runner (review r5 S4): every step runs under the fix3 memory cap; the script ends with the
# first non-zero step code, so the gate record's exit code is the verdict.
# Usage (cwd fv/kraken/lean, inside the gate):
#   run_checks.sh <memcap.py> <out-dir> <compare.lean> <axioms.lean> [<negative run.sh>]
set -u
MC=$1; O=$2; CMP=$3; AX=$4; NEG=${5:-}
mkdir -p "$O"; : > "$O/rc.txt"; fail=0
step() { name=$1; shift; python3 -I -B "$MC" 6442450944 -- "$@" > "$O/$name.log" 2>&1; rc=$?
         echo "$name $rc" >> "$O/rc.txt"; [ "$rc" -ne 0 ] && [ "$fail" -eq 0 ] && fail=$rc; }
step build lake build Gen1cX4
step compare lake env lean "$CMP"
step axioms lake env lean "$AX"
[ -n "$NEG" ] && step negative sh "$NEG"
cat "$O/rc.txt"
exit "$fail"
