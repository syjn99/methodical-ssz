#!/usr/bin/env bash
# Builds the EthLib SSZ export at the pinned commit and prints the cgo
# environment that links it:  eval "$(./ethlib.sh)"
# The checkout and its build live in $ETHLIB_DIR (about 8 GB, 30 minutes cold).
set -euo pipefail

COMMIT=f4c856c869228b7223752dbf10a73bd850ee7dae
DIR=${ETHLIB_DIR:-$HOME/.cache/ethlib-fuzz/EthLib}

{
	[[ -d $DIR/.git ]] || git clone -q https://github.com/ethereum/EthLib "$DIR"
	cd "$DIR"
	[[ $(git rev-parse HEAD) == "$COMMIT" ]] || { git fetch -q origin "$COMMIT" && git checkout -q "$COMMIT"; }
	if [[ ! -f libethlib.a || $(cat libethlib.commit 2>/dev/null) != "$COMMIT" ]]; then
		lake exe cache get
		lake build EthLib.Consensus.Exports.Ssz
		# Every module object goes in the archive. The linker takes the ones
		# that the export needs.
		rm -f libethlib.a
		find .lake/build/ir/EthLib -name '*.c.o.export' -print0 | xargs -0 ar rcs libethlib.a
		echo "$COMMIT" >libethlib.commit
	fi
} >&2

lean=$(cd "$DIR" && lean --print-prefix)
strip=-Wl,--gc-sections
[[ $(uname) == Darwin ]] && strip=-Wl,-dead_strip
echo "export CGO_CFLAGS='-I$lean/include'"
# Stripping drops the compile-time initializers, which refer to proof modules
# that are not linked.
echo "export CGO_LDFLAGS='$DIR/libethlib.a -L$lean/lib/lean -lleanshared -Wl,-rpath,$lean/lib/lean $strip'"
