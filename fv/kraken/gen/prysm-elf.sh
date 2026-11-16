#!/bin/sh
# Build the Go 1.26.10 target ELF twice and dump its SSZ functions.
# Run inside the heavy-job gate, with Go 1.26.10 (env-go12610.sh) on PATH,
# from the temporary Prysm tree that already holds the 698c202 outputs and
# fv/prysm-target/main.go (fv/kraken/gen/keepalive.py).
#
# Usage: prysm-elf.sh <prysm-tree> <outdir> <fresh-gocache-dir>
#   <outdir>/prysm-target-amd64                the first build (shared GOCACHE)
#   <outdir>/prysm-target-amd64.second-build   the second build (empty GOCACHE <fresh-gocache-dir>)
#   <outdir>/prysm-target-amd64.objdump, .nm, BUILD-INFO
set -eu
P=$1
O=$2
C2=$3
cd "$P"
mkdir -p "$O"
FLAGS="-p 2 -tags purego -trimpath"
echo "### first build"
# shellcheck disable=SC2086
GOOS=linux GOARCH=amd64 GOAMD64=v1 CGO_ENABLED=0 go build $FLAGS -o "$O/prysm-target-amd64" ./fv/prysm-target
echo "### second build (empty GOCACHE)"
mkdir -p "$C2"
# shellcheck disable=SC2086
GOCACHE=$C2 GOOS=linux GOARCH=amd64 GOAMD64=v1 CGO_ENABLED=0 go build $FLAGS -o "$O/prysm-target-amd64.second-build" ./fv/prysm-target
RE='(proto/prysm/v1alpha1|proto/engine/v1)\.\(\*[A-Za-z0-9_]+\)\.(MarshalSSZTo|SizeSSZ|UnmarshalSSZ)$|consensus-types/primitives\.\(\*[A-Za-z0-9_]+\)\.(MarshalSSZTo|MarshalSSZ|SizeSSZ|UnmarshalSSZ)$|methodical-ssz/ssz\.Validate(Bitlist|Bitvector)$'
echo "### objdump"
go tool objdump -gnu -s "$RE" "$O/prysm-target-amd64" > "$O/prysm-target-amd64.objdump"
go tool nm -size -sort address "$O/prysm-target-amd64" > "$O/prysm-target-amd64.nm"
{
  echo "go: $(go version)"
  echo "target: GOOS=linux GOARCH=amd64 GOAMD64=v1 CGO_ENABLED=0 go build $FLAGS"
  echo "host: $(uname -sm)"
  echo "elf sha256: $(sha256sum "$O/prysm-target-amd64" | cut -d' ' -f1)"
  echo "elf size: $(stat -c %s "$O/prysm-target-amd64")"
  echo "second build sha256: $(sha256sum "$O/prysm-target-amd64.second-build" | cut -d' ' -f1)"
  echo "go build id: $(go tool buildid "$O/prysm-target-amd64")"
  echo "second build go build id: $(go tool buildid "$O/prysm-target-amd64.second-build")"
  echo "objdump sha256: $(sha256sum "$O/prysm-target-amd64.objdump" | cut -d' ' -f1)"
  echo "nm sha256: $(sha256sum "$O/prysm-target-amd64.nm" | cut -d' ' -f1)"
  echo "main.go sha256: $(sha256sum fv/prysm-target/main.go | cut -d' ' -f1)"
} > "$O/BUILD-INFO"
go version -m "$O/prysm-target-amd64" > "$O/prysm-target-amd64.version-m.txt"
cat "$O/BUILD-INFO"
# The two builds must be byte-identical; a difference is a failure of this script.
if cmp "$O/prysm-target-amd64" "$O/prysm-target-amd64.second-build"; then
  echo "REPRODUCIBLE: identical"
else
  echo "REPRODUCIBLE: DIFFERENT"
  exit 3
fi
