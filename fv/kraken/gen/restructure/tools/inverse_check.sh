#!/bin/sh
# Inverse check of one restructuring step. No Lean, no build.
#
# usage (from the repository root):
#   sh fv/kraken/gen/restructure/tools/inverse_check.sh <map dir> <base commit> <new tree> <out dir>
#
#   <map dir>      repository-relative map directory, for example fv/kraken/gen/restructure/maps/attestation-data
#   <base commit>  the commit from which the forward run of the step started
#   <new tree>     the tree after the step: a commit, or the word WORKTREE for the current working tree
#                  (tracked files and untracked files that git does not ignore)
#   <out dir>      scratch directory for the copies. It must not exist. Delete it later with `trash`.
#
# The script does these steps:
#   1. It writes the base commit to <out dir>/base and to <out dir>/fresh.
#   2. It copies rename.py and the map directory of the new tree (without applied-lines.tsv) into <out dir>/fresh.
#   3. It runs the forward mode of the map on <out dir>/fresh.
#   4. It compares <out dir>/fresh with the new tree. Expected differences: the files of the hand edits,
#      the files of this directory that the step did not get from the tool, and commits between the base and
#      the new tree that are not part of the step.
#   5. It runs the inverse mode of the map on <out dir>/fresh.
#   6. It compares <out dir>/fresh with <out dir>/base. Expected differences: rename.py (if the step changed it)
#      and the map directory. Any difference outside fv/kraken/gen/restructure/ is a failure.
#
# Exit 0: the inverse equals the base outside fv/kraken/gen/restructure/. Exit 1: it does not, or a tool run failed.
# Exit 2: usage error.
set -u
if [ $# -ne 4 ]; then
  sed -n '2,12p' "$0" >&2
  exit 2
fi
MAP=$1; BASE=$2; NEW=$3; OUT=$4
if [ -e "$OUT" ]; then
  echo "error: $OUT exists. Delete it with trash, or give another directory." >&2
  exit 2
fi
REPO=$(git rev-parse --show-toplevel) || exit 2
cd "$REPO" || exit 2
if [ ! -d "$MAP" ] && [ "$NEW" = WORKTREE ]; then
  echo "error: $MAP is not a directory of the working tree" >&2
  exit 2
fi
mkdir -p "$OUT/base" "$OUT/fresh" "$OUT/new" || exit 2
OUT=$(cd "$OUT" && pwd)
TOOL=fv/kraken/gen/restructure/rename.py

git archive "$BASE" fv | tar -x -C "$OUT/base" || exit 1
git archive "$BASE" fv | tar -x -C "$OUT/fresh" || exit 1
if [ "$NEW" = WORKTREE ]; then
  git ls-files -co --exclude-standard fv | while IFS= read -r f; do
    if [ -f "$f" ]; then
      mkdir -p "$OUT/new/$(dirname "$f")" && cp -p "$f" "$OUT/new/$f"
    fi
  done
else
  git archive "$NEW" fv | tar -x -C "$OUT/new" || exit 1
fi
if [ ! -d "$OUT/new/$MAP" ]; then
  echo "error: the new tree has no $MAP" >&2
  exit 1
fi

# Step 2: the tool and the map of the new tree, without the record of the earlier forward run.
cp "$OUT/new/$TOOL" "$OUT/fresh/$TOOL" || exit 1
[ -d "$OUT/fresh/$MAP" ] && { echo "error: the base already has $MAP" >&2; exit 1; }
mkdir -p "$OUT/fresh/$MAP"
(cd "$OUT/new/$MAP" && tar -cf - --exclude=applied-lines.tsv .) | (cd "$OUT/fresh/$MAP" && tar -xf -) || exit 1

# Step 3: forward run on the fresh copy.
(cd "$OUT/fresh" && python3 -I -B "$TOOL" forward "$MAP" --root "$OUT/fresh") > "$OUT/forward.out" 2>&1
rc=$?
echo "== forward run on the base (rc=$rc): $(tail -n 1 "$OUT/forward.out")"
grep -c '^warning' "$OUT/forward.out" | sed 's/^/   warnings: /'
[ $rc -eq 0 ] || { tail -n 5 "$OUT/forward.out"; exit 1; }

# Step 4: the new tree against the fresh forward run.
echo "== new tree against the fresh forward run (expected: hand edits and changes that are not part of the step)"
diff -rq "$OUT/fresh/fv" "$OUT/new/fv" | sed "s#$OUT/##g"
diff -r "$OUT/fresh/fv" "$OUT/new/fv" > "$OUT/new-vs-forward.diff"

# Step 5: inverse run on the fresh copy.
(cd "$OUT/fresh" && python3 -I -B "$TOOL" inverse "$MAP" --root "$OUT/fresh") > "$OUT/inverse.out" 2>&1
rc=$?
echo "== inverse run (rc=$rc): $(tail -n 1 "$OUT/inverse.out")"
[ $rc -eq 0 ] || { tail -n 5 "$OUT/inverse.out"; exit 1; }

# Step 6: the inverse against the base.
echo "== inverse against the base (expected: rename.py and the map directory only)"
diff -rq "$OUT/base/fv" "$OUT/fresh/fv" | sed "s#$OUT/##g" | tee "$OUT/inverse-vs-base.txt"
diff -r "$OUT/base/fv" "$OUT/fresh/fv" > "$OUT/inverse-vs-base.diff"
if grep -v 'fv/kraken/gen/restructure' "$OUT/inverse-vs-base.txt" | grep -q .; then
  echo "FAIL: the inverse differs from the base outside fv/kraken/gen/restructure/"
  exit 1
fi
echo "PASS: the inverse equals the base outside fv/kraken/gen/restructure/"
exit 0
