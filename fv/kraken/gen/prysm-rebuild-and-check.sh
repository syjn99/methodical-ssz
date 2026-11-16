#!/bin/sh
# Build the Prysm target ELF again in Docker, then run the link check and the Go differential check.
#
# Usage (from any directory):
#   sh fv/kraken/gen/prysm-rebuild-and-check.sh <prysm-tree> <generator-tree> <scratch-dir>
#
#   <prysm-tree>      a Prysm tree at the pinned commit. It holds the generated files of the pinned generator,
#                     fv/prysm-target/main.go (gen/keepalive.py) and the go.mod changes of prysm/go1.26.10/prysm-go.mod.diff.
#   <generator-tree>  the methodical-ssz tree at the pinned generator commit.
#   <scratch-dir>     a new directory for all outputs. It must not exist.
# The script writes nothing into the two trees. Docker mounts them read only.
#
# Environment:
#   GO_IMAGE        the Docker image with Go 1.26.10. Default: golang:1.26.10.
#   GO_MODULE_CACHE a filled Go module cache. With it, the containers have no network.
#                   Without it, Go downloads the modules into <scratch-dir>/gomodcache.
#
# The host needs Docker, python3, and clang and llvm-objdump through xcrun (link/check.py).
# Exit 0 only if every step passes:
#   1. The ELF build: BUILD-INFO is equal to prysm/go1.26.10/build-ids.txt.
#   2. The link set from gen/checks/link_set.py is equal to prysm/go1.26.10/link-set (target.objdump, norm/, data/).
#   3. link/check.py passes, and its RESULT is equal to the tracked RESULT.
#   4. The case files from gen/checks/differential.py are equal to prysm/differential-cases/.
#   5. The Go program gives no mismatch on these cases.
#   6. The negative control: on the planted copy of the cases, the check reports mismatches (exit 1).
set -eu
if [ $# -ne 3 ]; then
  sed -n '2,27p' "$0" >&2
  exit 2
fi
if [ -e "$3" ]; then
  echo "error: $3 exists. Give a new directory." >&2
  exit 2
fi
P=$(cd "$1" && pwd)
G=$(cd "$2" && pwd)
mkdir -p "$3"
S=$(cd "$3" && pwd)
K=$(cd "$(dirname "$0")/.." && pwd)
T=$K/prysm/go1.26.10
IMAGE=${GO_IMAGE:-golang:1.26.10}

# The ELF records the required version and the path of the replace line. So the generator tree must be at that path in the container.
GPATH=$(sed -n 's|^+replace github.com/OffchainLabs/methodical-ssz => ||p' "$T/prysm-go.mod.diff")
GREQ=$(sed -n 's|^+[[:space:]]github.com/OffchainLabs/methodical-ssz ||p' "$T/prysm-go.mod.diff")
grep -q "^replace github.com/OffchainLabs/methodical-ssz => $GPATH\$" "$P/go.mod" || {
  echo "error: $P/go.mod has not the replace line of $T/prysm-go.mod.diff" >&2
  exit 2
}
grep -q "^[[:space:]]github.com/OffchainLabs/methodical-ssz $GREQ\$" "$P/go.mod" || {
  echo "error: $P/go.mod has not the require line of $T/prysm-go.mod.diff" >&2
  exit 2
}
if [ -n "${GO_MODULE_CACHE:-}" ]; then
  MODCACHE=$(cd "$GO_MODULE_CACHE" && pwd)
  NET="--network none -e GOPROXY=off"
else
  MODCACHE=$S/gomodcache
  NET=""
fi
mkdir -p "$S/elf" "$S/gocache" "$S/gomodcache" "$S/link-set/norm" "$S/differential"
# shellcheck disable=SC2086
go_run() { # <extra docker arguments> -- <command>
  docker run --rm --memory 12g $NET -e GOFLAGS=-mod=readonly \
    -v "$P:/work/prysm:ro" -v "$G:$GPATH:ro" -v "$MODCACHE:/go/pkg/mod" -v "$S/gocache:/root/.cache/go-build" \
    -v "$K/gen:/fvgen:ro" -w /work/prysm "$@"
}

echo "### 1. ELF build"
go_run -v "$S/elf:/elf" "$IMAGE" sh /fvgen/prysm-elf.sh /work/prysm /elf /tmp/gocache-empty
diff "$S/elf/BUILD-INFO" "$T/build-ids.txt"
echo "BUILD-INFO is equal to build-ids.txt"

echo "### 2. link set"
python3 -I -B "$K/gen/checks/link_set.py" "$S/link-set" "$S/elf/prysm-target-amd64" \
  "$S/elf/prysm-target-amd64.objdump" "$S/elf/prysm-target-amd64.nm"
cmp "$S/link-set/target.objdump" "$T/link-set/target.objdump"
diff -r "$S/link-set/norm" "$T/link-set/norm"
diff -r "$S/link-set/data" "$T/link-set/data"
echo "target.objdump, norm/ and data/ are equal to the tracked link set"

echo "### 3. link check"
python3 -B "$K/link/check.py" "$S/link-set" > "$S/link-check.log"
echo "PASS lines: $(grep -c '^PASS' "$S/link-set/RESULT"), FAIL lines: $(grep -c FAIL "$S/link-set/RESULT" || true)"
diff "$S/link-set/RESULT" "$T/link-set/RESULT"
echo "RESULT is equal to the tracked RESULT"

echo "### 4. differential cases"
D=$S/differential
python3 -I -B "$K/gen/checks/differential.py" cases "$D/cases"
diff -r "$D/cases" "$K/prysm/differential-cases"
echo "the case files are equal to prysm/differential-cases/"

echo "### 5. differential run"
# The overlay adds the program as the package fv/differential of the Prysm module. The tree does not change.
cp "$K/gen/checks/differential-main.go.txt" "$D/main.go"
echo '{"Replace": {"/work/prysm/fv/differential/main.go": "/diff/main.go"}}' > "$D/overlay.json"
go_run -v "$D:/diff" "$IMAGE" sh -c \
  'go build -overlay /diff/overlay.json -o /diff/differential ./fv/differential && /diff/differential /diff/cases/*.json > /diff/go-out.json'
python3 -I -B "$K/gen/checks/differential.py" check "$D/cases" "$D/go-out.json" "$D/result.json"

echo "### 6. negative control"
python3 -I -B "$K/gen/checks/differential.py" plant "$D/cases" "$D/planted"
rc=0
python3 -I -B "$K/gen/checks/differential.py" check "$D/planted" "$D/go-out.json" "$D/planted-result.json" || rc=$?
if [ "$rc" -ne 1 ]; then
  echo "FAIL: the check on the planted cases gave exit $rc, not 1" >&2
  exit 1
fi
echo "the check finds the planted mismatches"
echo "ALL PASS: outputs in $S"
