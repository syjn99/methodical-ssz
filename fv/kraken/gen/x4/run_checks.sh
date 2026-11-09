#!/bin/sh
# X4 check runner (review r5 S4): every step runs under the memory cap; the script ends with the
# first non-zero step code, so the gate record's exit code is the verdict.
# Usage (cwd fv/kraken/lean, inside the gate):
#   run_checks.sh <memcap.py> <out-dir> <compare.lean> <axioms.lean> [<negative run.sh>]
# Cap (review r7 S1, orchestrator decision): 6 GiB session anonymous RSS and 6 GiB per-process VmRSS
# (file-backed .olean pages count in VmRSS). <memcap.py> = gen/tools/memcap.py (phase1c copy of fix3's tool).
set -u
MC=$1; O=$2; CMP=$3; AX=$4; NEG=${5:-}
mkdir -p "$O"; : > "$O/rc.txt"; fail=0
step() { name=$1; shift; python3 -I -B "$MC" 6442450944 --per-proc 6442450944 -- "$@" > "$O/$name.log" 2>&1; rc=$?
         echo "$name $rc" >> "$O/rc.txt"; [ "$rc" -ne 0 ] && [ "$fail" -eq 0 ] && fail=$rc; }
# one lake call per module (proof modules first, then witnesses): a parallel rebuild of several witness
# modules exceeds the 6 GiB session cap (logs/102, logs/105)
: > "$O/build.log"; brc=0
for f in $(ls Gen1cX4/*.lean | grep -v '/Wit') $(ls Gen1cX4/Wit*.lean); do
  m=$(echo "$f" | sed 's|/|.|; s|\.lean$||')
  python3 -I -B "$MC" 6442450944 --per-proc 6442450944 -- lake build "$m" >> "$O/build.log" 2>&1; rc=$?
  [ "$rc" -ne 0 ] && [ "$brc" -eq 0 ] && brc=$rc
done
echo "build $brc" >> "$O/rc.txt"; [ "$brc" -ne 0 ] && fail=$brc
step compare lake env lean "$CMP"
step axioms lake env lean "$AX"
[ -n "$NEG" ] && step negative sh "$NEG"   # the case files run under this one cap (session and per process)
cat "$O/rc.txt"
exit "$fail"
