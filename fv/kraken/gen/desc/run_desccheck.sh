#!/bin/sh
# Run the Desc checker for test_desc.py. Run inside the heavy-job gate with the Lean env.
# Usage: run_desccheck.sh <work-dir> <fv/kraken/lean>
#   main     : DESC_LIST=list.txt (originals), DESC_MUTANTS=mutants.txt (controls, known passes)
#   scen-<id>: DESC_LIST=scen/<id>.txt (originals with one change): must exit non-zero
#   replay   : DESC_LIST=list.txt, DESC_MUTANTS=replay.txt (review mutants)
# Writes <work>/logs/*.log and <work>/logs/rc.txt ("<run> <rc>").
# Exit status: 0 only if main and replay exit 0 and every scenario exits non-zero.
set -u
W=$1
L=$2
mkdir -p "$W/logs"
: > "$W/logs/rc.txt"
cd "$L" || exit 98
fail=0
DESC_LIST=$W/list.txt DESC_MUTANTS=$W/mutants.txt lake env lean ../gen/desccheck/DescCheck.lean > "$W/logs/main.log" 2>&1
rc=$?; echo "main $rc" >> "$W/logs/rc.txt"; [ $rc -eq 0 ] || fail=1
for s in "$W"/scen/*.txt; do
  id=$(basename "$s" .txt)
  DESC_LIST=$s lake env lean ../gen/desccheck/DescCheck.lean > "$W/logs/scen-$id.log" 2>&1
  rc=$?; echo "$id $rc" >> "$W/logs/rc.txt"; [ $rc -ne 0 ] || fail=1
done
DESC_LIST=$W/list.txt DESC_MUTANTS=$W/replay.txt lake env lean ../gen/desccheck/DescCheck.lean > "$W/logs/replay.log" 2>&1
rc=$?; echo "replay $rc" >> "$W/logs/rc.txt"; [ $rc -eq 0 ] || fail=1
cat "$W/logs/rc.txt"
exit $fail
