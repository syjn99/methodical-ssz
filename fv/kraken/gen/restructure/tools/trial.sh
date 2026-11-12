#!/bin/sh
# Trial forward run of a map on a fresh copy of a commit. No Lean, no build. The working tree does not change.
#
# usage (from the repository root):
#   sh fv/kraken/gen/restructure/tools/trial.sh [--no-manual] <map dir> <out dir> [<base commit>]
#
#   --no-manual    do not copy manual-edits.tsv. Use the result to find the lines that need manual-edits rows.
#   <map dir>      repository-relative map directory of the working tree
#   <out dir>      directory for the copy. It must not exist. Delete it later with `trash`.
#   <base commit>  the commit to copy. Default: HEAD.
#
# The script copies fv/ of the base commit to <out dir>, then rename.py and the map directory of the working tree
# (without applied-lines.tsv). Then it runs the forward mode with --root <out dir>.
# Output: the tool output in <out dir>.forward.out. Read every `warning:` line.
set -u
NO_MANUAL=0
if [ "${1:-}" = --no-manual ]; then NO_MANUAL=1; shift; fi
if [ $# -lt 2 ] || [ $# -gt 3 ]; then
  sed -n '2,14p' "$0" >&2
  exit 2
fi
MAP=$1; OUT=$2; BASE=${3:-HEAD}
if [ -e "$OUT" ]; then
  echo "error: $OUT exists. Delete it with trash, or give another directory." >&2
  exit 2
fi
REPO=$(git rev-parse --show-toplevel) || exit 2
cd "$REPO" || exit 2
[ -d "$MAP" ] || { echo "error: $MAP is not a directory" >&2; exit 2; }
mkdir -p "$OUT" || exit 2
OUT=$(cd "$OUT" && pwd)
TOOL=fv/kraken/gen/restructure/rename.py
git archive "$BASE" fv | tar -x -C "$OUT" || exit 1
cp "$TOOL" "$OUT/$TOOL" || exit 1
[ -d "$OUT/$MAP" ] && { echo "error: $BASE already has $MAP" >&2; exit 1; }
mkdir -p "$OUT/$MAP"
if [ $NO_MANUAL -eq 1 ]; then
  (cd "$MAP" && tar -cf - --exclude=applied-lines.tsv --exclude=manual-edits.tsv .) | (cd "$OUT/$MAP" && tar -xf -) || exit 1
else
  (cd "$MAP" && tar -cf - --exclude=applied-lines.tsv .) | (cd "$OUT/$MAP" && tar -xf -) || exit 1
fi
(cd "$OUT" && python3 -I -B "$TOOL" forward "$MAP" --root "$OUT") > "$OUT.forward.out" 2>&1
rc=$?
echo "forward rc=$rc: $(tail -n 1 "$OUT.forward.out")"
grep '^warning' "$OUT.forward.out" | head -n 20
exit $rc
