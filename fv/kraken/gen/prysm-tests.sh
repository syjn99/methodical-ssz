#!/bin/bash
# Prysm tests on the temporary tree with the 698c202 outputs (P1 / review phase1c-r1 S7).
# Run inside the heavy-job gate with Go 1.26.10. go test -p 1. Output is not truncated.
# Exit status: that of gen/prysm_tests_classify.py (0 = only the known failures).
# Usage: prysm-tests.sh <prysm-tree> <out-dir>
#   <out-dir>/tNN.out  full output of each run;  <out-dir>/summary.txt  one line per run with its rc
set -u -o pipefail
P=$1
O=$2
mkdir -p "$O"
cd "$P" || exit 98
: > "$O/summary.txt"
n=0
t() { # <tags> <run regexp or empty> <packages...>
  local tags=$1 run=$2
  shift 2
  n=$((n + 1))
  local f
  f=$(printf '%s/t%02d.out' "$O" "$n")
  if [ -n "$run" ]; then
    go test -p 1 -count=1 -tags "$tags" -run "$run" -v "$@" > "$f" 2>&1
  else
    go test -p 1 -count=1 -tags "$tags" "$@" > "$f" 2>&1
  fi
  local rc=$?
  echo "t$n rc=$rc tags=[$tags] run=[$run] pkgs=$*" | tee -a "$O/summary.txt"
  grep -E '^(--- FAIL|FAIL|ok |panic)|^    --- FAIL' "$f"
}
t "" 'Fulu|PartialDataColumns' ./proto/prysm/v1alpha1
t minimal 'Fulu|PartialDataColumns' ./proto/prysm/v1alpha1
t "" 'DataColumn|PartsMetadata|PartialColumn|DecodePartialColumnSidecar' ./consensus-types/blocks
t minimal 'DataColumn|PartsMetadata|PartialColumn|DecodePartialColumnSidecar' ./consensus-types/blocks
t "" 'TestSlotFromBlock|TestByState|TestUnmarshalState|TestDetectAndUnmarshalBlock' ./encoding/ssz/detect
t minimal 'TestSlotFromBlock|TestByState|TestUnmarshalState|TestDetectAndUnmarshalBlock' ./encoding/ssz/detect
t "" "" ./proto/prysm/v1alpha1 ./proto/engine/v1 ./consensus-types/blocks ./encoding/ssz/detect
# Exit status = verdict of the committed classifier: 0 only if every failure is a known one.
python3 -I "$(dirname "$0")/prysm_tests_classify.py" "$O" "$O/classified.json"
