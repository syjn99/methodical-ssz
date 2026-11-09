#!/bin/sh
# measure.sh <label> <cmd...>
# Runs <cmd> under /usr/bin/time -l and samples the RSS of its process tree.
# Writes, under logs/ next to this script:
#   <label>.out.txt     stdout and stderr of <cmd>
#   <label>.time.txt    /usr/bin/time -l output (wall, max RSS in bytes)
#   <label>.rss.txt     samples every 0.5 s: n el_s total_kb max_kb max_comm nproc
#                       (n = sample index, el_s = elapsed whole seconds)
#   <label>.summary.txt exit status, wall, time max RSS, sampled peaks
# total_kb is the sum over all descendants of /usr/bin/time.
# max_kb is the largest single descendant. ps rss is in KiB.
set -u
[ $# -ge 2 ] || { echo "usage: $0 <label> <cmd...>" >&2; exit 2; }
L=$1; shift
D=$(cd "$(dirname "$0")" && pwd)/logs
mkdir -p "$D"
OUT=$D/$L.out.txt TM=$D/$L.time.txt RS=$D/$L.rss.txt SM=$D/$L.summary.txt
echo "n el_s total_kb max_kb max_comm nproc" > "$RS"

/usr/bin/time -l -o "$TM" "$@" > "$OUT" 2>&1 &
TP=$!
T0=$(date +%s)
(
  i=0
  while kill -0 "$TP" 2>/dev/null; do
    ps -A -o pid=,ppid=,rss=,comm= | awk -v root="$TP" -v t="$i" -v e="$(($(date +%s)-T0))" '
      { par[$1]=$2; rss[$1]=$3; c=$4; for (k=5;k<=NF;k++) c=c"_"$k; cm[$1]=c }
      END {
        tot=0; mx=0; mc="-"; n=0
        for (p in par) {
          q=p; d=0
          while (q in par && q!=0 && q!=1 && d<64) { if (par[q]==root) { d=-1; break }; q=par[q]; d++ }
          if (d==-1) { n++; tot+=rss[p]; if (rss[p]>mx) { mx=rss[p]; mc=cm[p] } }
        }
        sub(".*/","",mc)
        printf "%d %d %d %d %s %d\n", t, e, tot, mx, mc, n
      }' >> "$RS"
    i=$((i+1))
    sleep 0.5
  done
) &
SP=$!
wait "$TP"; RC=$?
T1=$(date +%s)
wait "$SP" 2>/dev/null

{
  echo "label: $L"
  echo "cmd: $*"
  echo "cwd: $(pwd)"
  echo "start_epoch: $T0"
  echo "exit: $RC"
  echo "wall_s_date: $((T1-T0))"
  awk '/real/ {print "wall_s_time: "$1} /maximum resident set size/ {printf "time_maxrss_bytes: %d\ntime_maxrss_gib: %.2f\n", $1, $1/1073741824}' "$TM"
  awk 'NR>1 { if ($3>t) t=$3; if ($4>m) m=$4 } END { printf "sampled_peak_total_gib: %.2f\nsampled_peak_single_gib: %.2f\nsamples: %d\n", t/1048576, m/1048576, NR-1 }' "$RS"
} > "$SM"
cat "$SM"
exit "$RC"
