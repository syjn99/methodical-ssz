#!/bin/sh
# B2.7 negative cases. Each mutation edits one directive of a converted .S file
# in a scratch clone (same directive count, so every index-based step before
# the mutated directive is unchanged; Kraken layouts are abstract, so no address
# needs regenerating), rebuilds the Lean code there, and records whether the
# designated theorem still checks. Run from the repository root:
#   fv/kraken/negative/run.sh <scratch-dir>
set -eu
SCR=$1
K=fv/kraken
OUT=$K/negative/RESULT
: > "$OUT"
mutate() { # name file directive-index old new theorem-file theorem
  name=$1; file=$2; idx=$3; old=$4; new=$5; tf=$6; thm=$7
  d="$SCR/neg-$name"
  if [ -e "$d" ]; then trash "$d"; fi
  mkdir -p "$d/fv/kraken"
  cp -Rc "$K/lean" "$d/fv/kraken/lean"
  cp -R "$K/link" "$d/fv/kraken/link"
  python3 - "$d/fv/kraken/link/out/norm/$file" "$idx" "$old" "$new" <<'PY'
import sys
p, idx, old, new = sys.argv[1], int(sys.argv[2]), sys.argv[3], sys.argv[4]
ls = open(p).read().split("\n")
assert ls[idx].strip() == old, (ls[idx], old)
ls[idx] = "  " + new
open(p, "w").write("\n".join(ls))
PY
  (cd "$d/fv/kraken" && link/shash.sh)
  log="$d/check.log"
  mod=$(echo "$tf" | sed 's/\.lean$//; s#/#.#g')
  (cd "$d/fv/kraken/lean" && lake build "$mod" > "$log" 2>&1) || true
  first=$(grep -m1 'error: Fk/' "$log" | cut -c1-200 || true)
  if [ -n "$first" ]; then res=FAIL; else res=PASS; fi
  echo "$name | $file:$idx '$old' -> '$new' | $thm ($tf) | $res | $first" | tee -a "$OUT"
}
# 1. offset constant: the decoder compares the offset with 8 instead of 4
mutate offset target.ListU64.UnmarshalSSZ.S 15 'cmp $0x4,%rdx' 'cmp $0x8,%rdx' Fk/LuAccept.lean lu_accept_main
# 2. length check removed: the jg to the "more than 16 elements" error is gone
mutate maxlen target.ListU64.UnmarshalSSZ.S 28 'jg L_target.ListU64.UnmarshalSSZ_ce' 'nop' Fk/LuRejectCall.lean lu_reject_toobig_main
# 3. loop bound off by one: the W copy loop stops after 3 elements
mutate loop target.FixedVec.UnmarshalSSZ.S 47 'cmp $0x4,%rax' 'cmp $0x3,%rax' Fk/FvLoop.lean fv_iter
# control: a directive rewritten to itself must still check
mutate control target.FixedVec.UnmarshalSSZ.S 47 'cmp $0x4,%rax' 'cmp $0x4,%rax' Fk/FvLoop.lean fv_iter
