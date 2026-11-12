#!/bin/sh
# Declaration dump of every module of every library of fv/kraken/lean/lakefile.toml, for the map builders.
#
# usage (from the repository root):
#   sh fv/kraken/gen/restructure/tools/dump_all.sh --modules     print the module list only (no Lean)
#   sh fv/kraken/gen/restructure/tools/dump_all.sh <out.tsv>     write the dump (a Lean job)
#
# The dump needs the built tree: run `lake build` of every library first.
# The dump is a heavy job. Run it under the heavy-job gate, and only when no other lake or lean job runs
# (check with `pgrep -lx lake` and `pgrep -lx lean`).
# Output: one line per constant, `module<TAB>name<TAB>kind<TAB>internal`. See dump_all.lean.
set -eu
if [ $# -ne 1 ]; then
  sed -n '2,11p' "$0" >&2
  exit 2
fi
REPO=$(git rev-parse --show-toplevel)
LEAN_DIR="$REPO/fv/kraken/lean"
modules() {
  cd "$LEAN_DIR"
  for lib in $(awk '/^\[\[lean_lib\]\]/ { getline; if (sub(/^name = "/, "")) { sub(/"$/, ""); print } }' lakefile.toml); do
    find "$lib" -name '*.lean'
  done | sed 's/\.lean$//; s#/#.#g' | sort
}
if [ "$1" = --modules ]; then
  modules
  exit 0
fi
case "$1" in
  /*) OUT=$1 ;;
  *) OUT="$(pwd)/$1" ;;
esac
MODULES=$(modules)
cd "$LEAN_DIR"
# shellcheck disable=SC2086
lake env lean --run ../gen/restructure/tools/dump_all.lean "$OUT" $MODULES
wc -l "$OUT"
