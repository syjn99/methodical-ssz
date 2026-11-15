#!/bin/sh
# Build the amd64 target, dump the target functions (Scalars, FixedVec,
# ListU64, BitVec, Nested, ListC, BitL, the reduced Prysm Checkpoint and
# AttestationData, ssz.ValidateBitlist and ssz.ValidateBitvector),
# convert them to labeled .S, extract the data files.
# Run from the repository root: fv/kraken/link/build.sh
set -eu
O=fv/kraken/link/out
mkdir -p "$O/norm"
GOOS=linux GOARCH=amd64 GOAMD64=v1 CGO_ENABLED=0 go build -tags purego -trimpath -o "$O/target-amd64" ./fv/kraken/cmd/test-target
go tool objdump -gnu -s 'target(/prysm)?\.\(\*(Scalars|FixedVec|ListU64|BitVec|Nested|ListC|BitL|Checkpoint|AttestationData)\)\.(SizeSSZ|MarshalSSZ|MarshalSSZTo|UnmarshalSSZ)$|ssz\.ValidateBitlist$|ssz\.ValidateBitvector$' "$O/target-amd64" > "$O/target.objdump"
go tool nm -size -sort address "$O/target-amd64" > "$O/target-amd64.nm"
python3 fv/kraken/link/convert_objdump.py "$O/target.objdump" "$O/target-amd64.nm" "$O/norm" --norm
python3 -B fv/kraken/link/data.py "$O"
{
  echo "go: $(go version), GOAMD64=v1"
  echo "elf sha256: $(shasum -a 256 "$O/target-amd64" | cut -d' ' -f1)"
  echo "objdump sha256: $(shasum -a 256 "$O/target.objdump" | cut -d' ' -f1)"
  echo "types.ssz.go sha256: $(shasum -a 256 fv/kraken/target/types.ssz.go | cut -d' ' -f1)"
  echo "types_bits_and_nesting.ssz.go sha256: $(shasum -a 256 fv/kraken/target/types_bits_and_nesting.ssz.go | cut -d' ' -f1)"
  echo "prysm/types.ssz.go sha256: $(shasum -a 256 fv/kraken/target/prysm/types.ssz.go | cut -d' ' -f1)"
  echo "ssz tree: $(git rev-parse HEAD:ssz)"
} > "$O/build-ids.txt"
cat "$O/build-ids.txt"
