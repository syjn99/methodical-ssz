#!/bin/sh
# Generate the Fulu-relevant Prysm SSZ files with the pinned generator and dump
# the generator IR. Run inside the heavy-job gate, with Go 1.26.10 on PATH.
#
# Usage: prysm-gen.sh <prysm-tree> <generator-binary> <outdir> [gen|ir|all]
#   gen   : <outdir>/gen/{mainnet,minimal}/<config>[.minimal].ssz.go
#   ir    : <outdir>/ir-{mainnet,minimal}.json (fv/kraken/gen/inventory-tool)
#   other : <outdir>/gen/GEN_RC (one line per run), <outdir>/bin/invtool
#
# Flags are the ones of Prysm build/gen/ssz.go (genMethodical): mainnet loads
# the default sources and stamps //go:build !minimal; minimal loads
# -tags minimal sources and stamps //go:build minimal; progressive is on
# (no --disable-progressive). Output goes outside the Prysm tree. The only
# write into the Prysm tree is the invtool scratch package fvphase1c/invtool.
set -eu
P=$1
GEN=$2
O=$3
MODE=${4:-all}
HERE=$(cd "$(dirname "$0")" && pwd)
cd "$P"
mkdir -p "$O/gen/mainnet" "$O/gen/minimal" "$O/bin"
[ "$MODE" = ir ] || : > "$O/gen/GEN_RC"
fail=0
run() { # <preset> <config> <pkgname> <outname>
  if [ "$1" = mainnet ]; then
    set -- "$1" "$2" "$3" "$4" "--go-build-constraint=!minimal"
  else
    set -- "$1" "$2" "$3" "$4" --build-tags=minimal --go-build-constraint=minimal
  fi
  preset=$1 cfg=$2 pkg=$3 outname=$4
  shift 4
  echo "### gen $preset $cfg"
  if "$GEN" gen --config="$cfg" --output="$O/gen/$preset/$outname" --override-package-name="$pkg" "$@"; then
    rc=0
  else
    rc=$?
    fail=1
  fi
  echo "$preset $cfg $outname $rc" >> "$O/gen/GEN_RC"
}
V=proto/prysm/v1alpha1
if [ "$MODE" != ir ]; then
for c in phase0 altair bellatrix capella deneb electra fulu; do
  run mainnet "$V/$c.yaml" eth "$c.ssz.go"
  run minimal "$V/$c.yaml" eth "$c.minimal.ssz.go"
done
run mainnet proto/engine/v1/engine.yaml enginev1 engine.ssz.go
run minimal proto/engine/v1/engine.yaml enginev1 engine.minimal.ssz.go
cat "$O/gen/GEN_RC"
fi
[ "$MODE" = gen ] && exit $fail

mkdir -p fvphase1c/invtool
cp "$HERE/inventory-tool/main.go" fvphase1c/invtool/main.go
go build -p 2 -o "$O/bin/invtool" ./fvphase1c/invtool
CFGS="$V/phase0.yaml $V/altair.yaml $V/bellatrix.yaml $V/capella.yaml $V/deneb.yaml $V/electra.yaml $V/fulu.yaml
$V/gloas.yaml $V/heze.yaml $V/non-core.yaml proto/engine/v1/engine.yaml proto/eth/v1/gateway.yaml
proto/ssz_query/response.yaml proto/ssz_query/testing/test_containers.yaml"
# shellcheck disable=SC2086
"$O/bin/invtool" -out "$O/ir-mainnet.json" $CFGS
# shellcheck disable=SC2086
"$O/bin/invtool" -tags minimal -out "$O/ir-minimal.json" $CFGS
exit $fail
