#!/bin/sh
# Build the amd64 target, dump the nine functions, convert them to labeled .S.
# Run from the repository root: fv/kraken/link/build.sh
set -eu
O=fv/kraken/link/out
mkdir -p "$O/raw" "$O/norm"
GOOS=linux GOARCH=amd64 CGO_ENABLED=0 go build -tags purego -trimpath -o "$O/p1bin-amd64" ./fv/phase1/cmd/p1bin
go tool objdump -gnu -s 'target\.\(\*(Scalars|FixedVec|ListU64)\)\.(SizeSSZ|MarshalSSZTo|UnmarshalSSZ)$' "$O/p1bin-amd64" > "$O/target.objdump"
go tool nm -size -sort address "$O/p1bin-amd64" > "$O/p1bin-amd64.nm"
python3 fv/kraken/link/conv.py "$O/target.objdump" "$O/p1bin-amd64.nm" "$O/raw"
python3 fv/kraken/link/conv.py "$O/target.objdump" "$O/p1bin-amd64.nm" "$O/norm" --norm
{
  echo "go: $(go version)"
  echo "elf sha256: $(shasum -a 256 "$O/p1bin-amd64" | cut -d' ' -f1)"
  echo "objdump sha256: $(shasum -a 256 "$O/target.objdump" | cut -d' ' -f1)"
  echo "types.ssz.go sha256: $(shasum -a 256 fv/phase1/target/types.ssz.go | cut -d' ' -f1)"
  echo "ssz tree: $(git rev-parse HEAD:ssz)"
} > "$O/build-ids.txt"
cat "$O/build-ids.txt"
