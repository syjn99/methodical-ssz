#!/usr/bin/env bash
# Runs every fuzz target for FUZZTIME (default 5m), JOBS targets at a time
# with WORKERS fuzz workers each. Writes one log per target to $OUT and prints
# one summary line per target. A failing input lands in testdata/fuzz/<target>/.
# Minimization calls the oracle without counting executions, so MINIMIZE caps it.
# PRESET=minimal fuzzes the minimal preset, where a BeaconState is 300 times smaller.
# Arguments select targets by regular expression, e.g. ./fuzzall.sh BeaconState
# The harness skips differences that known.txt lists. STRICT=1 fails on all of them.
set -uo pipefail
cd "$(dirname "$0")"
env=$(./ethlib.sh) || exit 1
eval "$env"
export FUZZTIME=${FUZZTIME:-5m} MINIMIZE=${MINIMIZE:-5s} WORKERS=${WORKERS:-2}
PRESET=${PRESET:-mainnet}
export OUT=${OUT:-logs/$PRESET}
mkdir -p "$OUT"
go test -c -fuzz=. -tags "$PRESET" -o "$OUT/fuzz.test" . || exit 1
export CACHE=$(go env GOCACHE)/fuzz/github.com/OffchainLabs/methodical-ssz/fuzz/$PRESET

one() {
	local status=ok
	"$OUT/fuzz.test" -test.run '^$' -test.fuzz "^$1\$" -test.fuzztime "$FUZZTIME" \
		-test.fuzzminimizetime "$MINIMIZE" -test.parallel "$WORKERS" -test.fuzzcachedir "$CACHE" >"$OUT/$1.log" 2>&1 || status=FAIL
	# The Go fuzzer can end with this error when the time runs out during
	# minimization. That is not a difference.
	if [[ $status == FAIL ]] && grep -q 'context deadline exceeded' "$OUT/$1.log" && ! grep -q 'Failing input' "$OUT/$1.log"; then
		status=ok
	fi
	echo "$status $1 $(grep '^fuzz: elapsed' "$OUT/$1.log" | tail -1)"
	[[ $status == ok ]]
}
export -f one
"$OUT/fuzz.test" -test.list "${1:-.}" | grep '^Fuzz' | xargs -P "${JOBS:-4}" -I{} bash -c 'one {}'
