#!/bin/sh
# run.sh <stage...> — memopt M4 low-memory check in a Linux aarch64 container.
# Run from the repository root (a git worktree is fine). Needs docker (OrbStack).
# Every stage is its own `docker run` with 9922 MiB RAM and no swap
# (--memory-swap equal to --memory), so each step gets a fresh cgroup.
# State lives in the docker volume memopt-lowmem-work:
#   /work/new  = clone at NEW, /work/orig = clone at ORIG,
#   /work/pkgs = Lake package sources; both clones link .lake/packages to it.
# Logs go to fv/kraken/memopt/logs/lm-*.txt.
# Stages, in order:
#   image setup env prebuild-new prebuild-orig orig-1 orig-2 new-1 new-2
#   full axioms clean
# This Lake has no -j option, so a lower-parallelism retry is not a stage.
set -eu
NEW=${NEW:-e5fb3d332c4b813dd497f2aace0787e8b6d9ff2a}
ORIG=${ORIG:-86fd060349257c133e981e420120f63c61f582e1}
MEM=9922m   # 9.69 GiB, the RAM that Linux reports in the user's Colima VM
IMG=memopt-lowmem VOL=memopt-lowmem-work
REPO=$(git rev-parse --show-toplevel)
GCD=$(cd "$(git rev-parse --git-common-dir)" && pwd)
HERE=$REPO/fv/kraken/memopt/lowmem
LOGS=$REPO/fv/kraken/memopt/logs
LD=fv/kraken/lean

dr() { # <workdir> <cmd...>
  w=$1; shift
  docker run --rm --memory=$MEM --memory-swap=$MEM \
    -v $VOL:/work -v "$LOGS":/logs -v "$HERE":/lowmem:ro \
    -v "$REPO":"$REPO":ro -v "$GCD":"$GCD":ro -w "$w" $IMG "$@"
}
m() { # <clone> <label> <cmd...>: measured step in /work/<clone>/fv/kraken/lean
  c=$1; shift; dr /work/$c/$LD sh /lowmem/cmeasure.sh "$@"
}
# Remove the outputs of Fk.WitLcM4x16 so that lake builds it again.
unbuild() { dr /work/$1/$LD sh -c 'find .lake/build -name "WitLcM4x16.*" -print -delete'; }

for s in "$@"; do
  echo "== stage $s"
  case $s in
  image) docker build -t $IMG "$HERE" ;;
  setup)
    docker volume create $VOL
    # Package sources only: the .lake of each package holds macOS build output.
    # macOS .olean files must not enter a Linux build (platform mixing).
    dr /work sh -c "set -e
      for c in new orig; do [ -d /work/\$c ] || git clone -q --no-checkout '$REPO' /work/\$c; done
      git -C /work/new checkout -q $NEW; git -C /work/orig checkout -q $ORIG
      rsync -a --delete --exclude='/*/.lake' '$REPO/$LD/.lake/packages/' /work/pkgs/
      for c in new orig; do mkdir -p /work/\$c/$LD/.lake; ln -sfn /work/pkgs /work/\$c/$LD/.lake/packages; done
      for c in new orig; do echo \$c \$(git -C /work/\$c rev-parse HEAD); done
      find /work/pkgs -maxdepth 2 -name .lake | wc -l" ;;
  env)
    dr /work/new/$LD sh -c 'cd /sys/fs/cgroup; for f in memory.max memory.swap.max memory.peak; do echo "$f: $(cat $f 2>&1)"; done
      echo "nproc: $(nproc)"; free -m; echo "uname -m: $(uname -m)"; uname -r
      cd /work/new/fv/kraken/lean; cat lean-toolchain; lean --version; lake --version
      echo "LEAN env:"; env | grep -i "^lean" || echo "(none)"
      echo "new: $(git -C /work/new rev-parse HEAD)"; echo "orig: $(git -C /work/orig rev-parse HEAD)"
      ls -l .lake' > "$LOGS/lm-env.txt" 2>&1
    cat "$LOGS/lm-env.txt" ;;
  prebuild-new) m new prebuild-new lake build Fk.LcMarshal Fk.RtCopy Fk.WHost ;;
  prebuild-orig) m orig prebuild-orig lake build Fk.LcMarshal Fk.RtCopy Fk.WHost ;;
  orig-[123]) unbuild orig; m orig $s lake build Fk.WitLcM4x16 || true ;;
  new-[12]) unbuild new; m new $s lake build Fk.WitLcM4x16 || true ;;
  full) dr /work/new/$LD rm -rf .lake/build; m new full lake build || true ;;
  axioms) m new axioms sh tools/axioms.sh || true ;;
  clean) docker volume rm $VOL ;;
  *) echo "unknown stage $s" >&2; exit 2 ;;
  esac
done
