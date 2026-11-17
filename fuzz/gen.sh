#!/usr/bin/env bash
# Puts a writable copy of the pinned Prysm module in ./.prysm and regenerates
# its *.ssz.go files (both presets) with the methodical-ssz generator in $GEN
# (default: the repository that holds this module). go.mod replaces Prysm
# with ./.prysm and methodical-ssz with ./.gen, a link to $GEN. The fuzz
# targets then test the output and the runtime of that generator.
set -euo pipefail
cd "$(dirname "$0")"

PRYSM=github.com/OffchainLabs/prysm/v7@v7.3.1-0.20261109112246-2e8dd0ffd708 # develop 2e8dd0ffd7
GEN=$(cd "${GEN:-..}" && pwd)

src=$(go mod download -json "$PRYSM" | sed -n 's/^\t"Dir": "\(.*\)",*$/\1/p')
rsync -a --delete --chmod=u+w "$src/" .prysm/
ln -sfn "$GEN" .gen

tmp=$(mktemp -d)
trap 'rm -r "$tmp"' EXIT
(cd "$GEN" && go build -o "$tmp/ssz" ./cmd/ssz)

cd .prysm
go mod edit -replace "github.com/OffchainLabs/methodical-ssz=$GEN"
# enginev1 first: the eth package delegates to its methods.
for cfg in proto/engine/v1/engine.yaml proto/prysm/v1alpha1/*.yaml; do
	pkg=eth
	[[ $cfg == proto/engine/* ]] && pkg=enginev1
	"$tmp/ssz" gen --config="$cfg" --output="${cfg%.yaml}.ssz.go" \
		--go-build-constraint='!minimal' --override-package-name=$pkg >/dev/null
	"$tmp/ssz" gen --config="$cfg" --output="${cfg%.yaml}.minimal.ssz.go" --build-tags=minimal \
		--go-build-constraint=minimal --override-package-name=$pkg >/dev/null
done
echo "generated with $(git -C "$GEN" rev-parse --short HEAD) from $GEN"
