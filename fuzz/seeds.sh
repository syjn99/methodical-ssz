#!/usr/bin/env bash
# Extracts the Fulu and Gloas ssz_static vectors of both presets into ./.seeds.
# The fuzz targets use them as seed corpus.
# usage: seeds.sh [dir]   dir holds mainnet.tar.gz and minimal.tar.gz; without
# it the script downloads them.
set -euo pipefail
cd "$(dirname "$0")"
VERSION=v1.7.0-beta.4 # consensus_spec_version of the pinned Prysm
mkdir -p .seeds
rm -f .seeds/complete
for preset in mainnet minimal; do
	tar=${1:+$1/$preset.tar.gz}
	if [[ $# -eq 0 ]]; then
		tar=$(mktemp)
		curl -fsSL -o "$tar" "https://github.com/ethereum/consensus-specs/releases/download/$VERSION/$preset.tar.gz"
	fi
	tar -xzf "$tar" -C .seeds --strip-components 1 --exclude "*.yaml" "tests/$preset/fulu/ssz_static" "tests/$preset/gloas/ssz_static"
	[[ $# -gt 0 ]] || rm "$tar"
done
# The harness and the workflow cache accept only a complete extraction.
echo "$VERSION" >.seeds/complete
