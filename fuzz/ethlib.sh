#!/usr/bin/env bash
# Builds the EthLib SSZ export at the pinned commit and prints the cgo
# environment that links it:  eval "$(./ethlib.sh)"
# The checkout and its build live in $ETHLIB_DIR. About 8 GB, of which 7 GB is
# the downloaded Mathlib cache. A cold build took 6 minutes on 18 cores.
set -euo pipefail

COMMIT=f4c856c869228b7223752dbf10a73bd850ee7dae
DIR=${ETHLIB_DIR:-$HOME/.cache/ethlib-fuzz/EthLib}

# The link needs only libethlib.a and the Lean toolchain that lean-toolchain
# names. When the archive of $COMMIT is present, the script skips the checkout.
if [[ $(cat "$DIR/libethlib.commit" 2>/dev/null) != "$COMMIT" ]]; then
	[[ -d $DIR/.git ]] || git clone -q https://github.com/ethereum/EthLib "$DIR"
	cd "$DIR"
	[[ $(git rev-parse HEAD) == "$COMMIT" ]] || { git fetch -q origin "$COMMIT" && git checkout -q "$COMMIT"; }
	lake exe cache get
	# The :c.o facet adds the object of the export module itself. Lake builds
	# only the objects of its imports by default.
	lake build EthLib.Consensus.Exports.Ssz EthLib.Consensus.Exports.Ssz:c.o
	# Every module object goes in the archive. The linker takes the ones
	# that the export needs.
	rm -f libethlib.a
	find .lake/build/ir/EthLib -name '*.c.o.export' -print0 | xargs -0 ar rcs libethlib.a
	nm libethlib.a | grep ' T _*eth_consensus_ssz_static$' >/dev/null
	echo "$COMMIT" >libethlib.commit
fi >&2

lean=$(cd "$DIR" && lean --print-prefix)
strip=-Wl,--gc-sections
[[ $(uname) == Darwin ]] && strip=-Wl,-dead_strip
# Go does not hash C libraries. The define puts the commit in its cache key.
echo "export CGO_CFLAGS='-I$lean/include -DETHLIB_COMMIT=$COMMIT'"
# Stripping drops the compile-time initializers, which refer to proof modules
# that are not linked.
echo "export CGO_LDFLAGS='$DIR/libethlib.a -L$lean/lib/lean -lleanshared -Wl,-rpath,$lean/lib/lean $strip'"
