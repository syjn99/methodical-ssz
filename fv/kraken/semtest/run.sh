#!/bin/sh
# B4: hardware comparison of the verified amd64 code. Run on x86-64 Linux from
# the repository root:  fv/kraken/semtest/run.sh
# 1. Rebuild the ELF with the pinned flags (link/build.sh: GOAMD64=v1) in a
#    scratch directory and check its sha256 against link/out/build-ids.txt
#    (the bundle the proofs and link/check.py are about).
# 2. Run it with -test on cases.txt and compare with expected.txt (the Go
#    reference, made by gen-expected.sh; cases.why names the theorem behind
#    each line).
# Not run on the development host (macOS arm64).
set -eu
K=fv/kraken
[ "$(uname -s)-$(uname -m)" = "Linux-x86_64" ] || { echo "run.sh needs Linux x86-64 (this host: $(uname -s)-$(uname -m))"; exit 2; }
tmp=$(mktemp -d)
GOOS=linux GOARCH=amd64 GOAMD64=v1 CGO_ENABLED=0 go build -tags purego -trimpath -o "$tmp/p1bin" ./$K/cmd/p1bin
got=$(sha256sum "$tmp/p1bin" | cut -d' ' -f1)
want=$(sed -n 's/^elf sha256: //p' $K/link/out/build-ids.txt)
echo "ELF sha256 $got (bundle $want)"
[ "$got" = "$want" ] || { echo "FAIL: the ELF differs from the verified bundle"; exit 1; }
"$tmp/p1bin" -test < $K/semtest/cases.txt > "$tmp/out.txt"
if diff -u $K/semtest/expected.txt "$tmp/out.txt"; then echo "PASS: $(wc -l < $K/semtest/cases.txt) cases"; else echo "FAIL"; exit 1; fi
