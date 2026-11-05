#!/bin/sh
# B4b: enumerate every theorem of Fk, Fv1, Fv with its axioms (AXIOMS.txt).
# Fails if any theorem depends on an axiom other than propext,
# Classical.choice, Quot.sound (sorryAx, Lean.ofReduceBool, ...).
# Run from fv/kraken/lean after `lake build`.
set -eu
out=../AXIOMS.txt
lake env lean tools/Axioms.lean > "$out.tmp"
grep -q '^TOTAL ' "$out.tmp"
mv "$out.tmp" "$out"
tail -1 "$out"
grep -q 'NONSTANDARD 0$' "$out"
# All-declarations scope (defs, instances, internal auxiliary declarations too).
lake env lean tools/AxiomsAll.lean > ../AXIOMS-ALL.txt
tail -1 ../AXIOMS-ALL.txt
grep -q 'NONSTANDARD 0$' ../AXIOMS-ALL.txt
