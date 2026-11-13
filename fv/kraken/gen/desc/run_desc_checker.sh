#!/bin/sh
# Run the Desc checker for test_desc.py. Run inside the heavy-job gate with the Lean env.
# Usage: run_desc_checker.sh <work-dir> <fv/kraken/lean>
#   main : DESC_LIST=list.txt (originals), DESC_MUTANTS=mutants.txt (controls, known passes,
#          review replay) -> <work>/main.result.json, <work>/logs/main.log
#   batch: DESC_BATCH=batch.txt (list scenarios, one result file each) -> <work>/logs/batch.log
# The expected key set is the checker's table + the committed inventory (DESC_INVENTORY
# defaults to ../prysm/inventory.json relative to fv/kraken/lean).
# Exit status: 0 only if the main run ends with verdict OK (exit 0) and the batch ran (exit 0).
set -u
W=$1
L=$2
mkdir -p "$W/logs"
: > "$W/logs/rc.txt"
cd "$L" || exit 98
DESC_LIST=$W/list.txt DESC_MUTANTS=$W/mutants.txt DESC_RESULT=$W/main.result.json \
  lake env lean ../gen/desc-checker/DescChecker.lean > "$W/logs/main.log" 2>&1
m=$?
DESC_BATCH=$W/batch.txt lake env lean ../gen/desc-checker/DescChecker.lean > "$W/logs/batch.log" 2>&1
b=$?
printf 'main %s\nbatch %s\n' "$m" "$b" | tee "$W/logs/rc.txt"
[ "$m" -eq 0 ] && [ "$b" -eq 0 ]
