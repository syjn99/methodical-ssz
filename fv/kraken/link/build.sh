#!/bin/sh
# Build the amd64 target, dump the target functions (1a: Scalars, FixedVec,
# ListU64; 1b: BitVec, Nested, ListC, BitL, prysm Checkpoint, AttestationData;
# and ssz.ValidateBitlist), convert them to labeled .S.
# Run from the repository root: fv/kraken/link/build.sh
set -eu
O=fv/kraken/link/out
mkdir -p "$O/raw" "$O/norm"
GOOS=linux GOARCH=amd64 GOAMD64=v1 CGO_ENABLED=0 go build -tags purego -trimpath -o "$O/p1bin-amd64" ./fv/kraken/cmd/p1bin
go tool objdump -gnu -s 'target(/prysm)?\.\(\*(Scalars|FixedVec|ListU64|BitVec|Nested|ListC|BitL|Checkpoint|AttestationData)\)\.(SizeSSZ|MarshalSSZ|MarshalSSZTo|UnmarshalSSZ)$|ssz\.ValidateBitlist$|ssz\.ValidateBitvector$' "$O/p1bin-amd64" > "$O/target.objdump"
go tool nm -size -sort address "$O/p1bin-amd64" > "$O/p1bin-amd64.nm"
python3 fv/kraken/link/conv.py "$O/target.objdump" "$O/p1bin-amd64.nm" "$O/raw"
python3 fv/kraken/link/conv.py "$O/target.objdump" "$O/p1bin-amd64.nm" "$O/norm" --norm
(cd fv/kraken && link/shash.sh)
{
  echo "go: $(go version), GOAMD64=v1"
  echo "elf sha256: $(shasum -a 256 "$O/p1bin-amd64" | cut -d' ' -f1)"
  echo "objdump sha256: $(shasum -a 256 "$O/target.objdump" | cut -d' ' -f1)"
  echo "types.ssz.go sha256: $(shasum -a 256 fv/kraken/target/types.ssz.go | cut -d' ' -f1)"
  echo "types1b.ssz.go sha256: $(shasum -a 256 fv/kraken/target/types1b.ssz.go | cut -d' ' -f1)"
  echo "prysm/types.ssz.go sha256: $(shasum -a 256 fv/kraken/target/prysm/types.ssz.go | cut -d' ' -f1)"
  echo "ssz tree: $(git rev-parse HEAD:ssz)"
} > "$O/build-ids.txt"
cat "$O/build-ids.txt"
