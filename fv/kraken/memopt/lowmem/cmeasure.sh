#!/bin/sh
# cmeasure.sh <label> <cmd...> — runs inside the container, cwd = build dir.
# Writes to /logs (host fv/kraken/memopt/logs):
#   lm-<label>.out.txt     stdout and stderr of <cmd>
#   lm-<label>.time.txt    GNU /usr/bin/time -v output (max RSS in KiB)
#   lm-<label>.cg.txt      every 0.5 s: el_s memory.current memory.peak (bytes) n_lean
#   lm-<label>.summary.txt exit, wall, max RSS, cgroup peak, oom_kill delta
# Each docker run has its own cgroup, so memory.peak covers this step and setup.
set -u
L=$1; shift
P=/logs/lm-$L; CG=/sys/fs/cgroup
peak() { cat $CG/memory.peak 2>/dev/null || echo NA; }
oom() { awk '$1=="oom_kill"{print $2}' $CG/memory.events; }
O0=$(oom); T0=$(date +%s)
echo "el_s current peak n_lean" > $P.cg.txt
/usr/bin/time -v -o $P.time.txt "$@" > $P.out.txt 2>&1 &
TP=$!
( while kill -0 $TP 2>/dev/null; do
    echo "$(($(date +%s)-T0)) $(cat $CG/memory.current) $(peak) $(pgrep -cx lean)" >> $P.cg.txt; sleep 0.5
  done ) &
SP=$!
wait $TP; RC=$?; T1=$(date +%s); wait $SP 2>/dev/null
G=1073741824
{
  echo "label: $L"; echo "cmd: $*"; echo "cwd: $(pwd)"; echo "exit: $RC"
  echo "wall_s: $((T1-T0))"
  awk -F': ' '/Maximum resident/ {printf "time_maxrss_gib: %.2f\n", $2/1048576} /Exit status/ {print "time_exit: "$2} /Elapsed/ {print "time_wall: "$2}' $P.time.txt
  awk -v g=$G 'NR>1 { if ($2>m) m=$2; if ($4>n) n=$4 } END {printf "sampled_current_max_gib: %.2f\nmax_lean_procs: %d\n", m/g, n}' $P.cg.txt
  p=$(peak); [ "$p" = NA ] && echo "memory.peak: NA" || awk -v p=$p -v g=$G 'BEGIN{printf "memory.peak_gib: %.2f (%d bytes)\n", p/g, p}'
  echo "memory.max: $(cat $CG/memory.max)  memory.swap.max: $(cat $CG/memory.swap.max)"
  echo "oom_kill_delta: $(($(oom)-O0))"
  echo "memory.events:"; sed 's/^/  /' $CG/memory.events
} > $P.summary.txt
cat $P.summary.txt
exit $RC
