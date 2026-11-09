#!/bin/sh
# Run Complete.lean on the real input and on a control input (one *_main removed).
# Run inside the heavy-job gate with the Lean env, cwd fv/kraken/lean.
# Usage: run_complete.sh <mains.txt> <out-dir>
#   <out>/real.log, <out>/control.log, <out>/rc.txt
# Exit status: 0 only if the real run exits 0 and the control run exits non-zero
# (the environment cross-check must reject the shortened input).
set -u
M=$1
O=$2
mkdir -p "$O"
grep -v '^cp_size_main$' "$M" > "$O/mains-control.txt"
COMPLETE_MAINS=$M lake env lean ../gen/complete/Complete.lean > "$O/real.log" 2>&1
r=$?
COMPLETE_MAINS=$O/mains-control.txt lake env lean ../gen/complete/Complete.lean > "$O/control.log" 2>&1
c=$?
printf 'real %s\ncontrol %s\n' "$r" "$c" | tee "$O/rc.txt"
[ "$r" -eq 0 ] && [ "$c" -ne 0 ]
