#!/bin/sh
# The Go reference for run.sh (any architecture). Run from the repository root.
set -eu
go run ./fv/kraken/cmd/p1bin -test < fv/kraken/semtest/cases.txt > fv/kraken/semtest/expected.txt
