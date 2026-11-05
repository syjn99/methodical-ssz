#!/bin/sh
# Negative cases. Each mutation edits one directive of a converted .S file in a
# scratch clone (same directive count, so every index-based step before the
# mutated directive is unchanged; Kraken layouts are abstract, so no address
# needs regenerating), rebuilds the Lean module there, and checks the result:
# - a mutation must make `lake build` exit non-zero, and the first error must
#   lie inside the designated theorem (its line span in the theorem file);
# - the control (a directive rewritten to itself) must build (exit 0);
# - a link mutation must make link/check.py exit non-zero.
# Any other outcome is UNEXPECTED and the script exits 1.
# Run from the repository root:
#   fv/kraken/negative/run.sh <scratch-dir> [name ...]
set -eu
SCR=$1; shift
ONLY="$*"
K=fv/kraken
OUT=$K/negative/RESULT
[ -n "$ONLY" ] || : > "$OUT"
bad=0
want() { [ -z "$ONLY" ] || echo " $ONLY " | grep -q " $1 "; }

clone() { # name
  d="$SCR/neg-$1"
  if [ -e "$d" ]; then trash "$d"; fi
  mkdir -p "$d/fv/kraken"
  cp -Rc "$K/lean" "$d/fv/kraken/lean"
  cp -R "$K/link" "$d/fv/kraken/link"
}

edit() { # file index old new
  python3 - "$1" "$2" "$3" "$4" <<'PY'
import sys
p, idx, old, new = sys.argv[1], int(sys.argv[2]), sys.argv[3], sys.argv[4]
ls = open(p).read().split("\n")
assert ls[idx].strip() == old, (ls[idx], old)
ls[idx] = "  " + new
open(p, "w").write("\n".join(ls))
PY
}

span() { # theorem-file theorem -> "start end" (1-based, end inclusive)
  awk -v t="$2" '
    /^(theorem|lemma|def|abbrev|instance|example|end|namespace|section|set_option|\/--|\/-!)/ {
      if (s && !e && NR > s) e = NR - 1 }
    $0 ~ "^theorem " t "([ (:]|$)" { s = NR }
    END { if (!e) e = NR; print s, e }' "$1"
}

mutate() { # name file directive-index old new theorem-file theorem expect(FAIL|PASS)
  name=$1; file=$2; idx=$3; old=$4; new=$5; tf=$6; thm=$7; expect=$8
  want "$name" || return 0
  clone "$name"; d="$SCR/neg-$name"
  edit "$d/fv/kraken/link/out/norm/$file" "$idx" "$old" "$new"
  (cd "$d/fv/kraken" && link/shash.sh)
  log="$d/check.log"
  mod=$(echo "$tf" | sed 's/\.lean$//; s#/#.#g')
  rc=0; (cd "$d/fv/kraken/lean" && lake build "$mod" > "$log" 2>&1) || rc=$?
  first=$(grep -m1 '^error: ' "$log" | cut -c1-200 || true)
  set -- $(span "$K/lean/$tf" "$thm"); s=$1; e=$2
  line=$(echo "$first" | sed -n "s#^error: $tf:\([0-9]*\):.*#\1#p")
  if [ "$rc" -ne 0 ] && [ -n "$line" ] && [ "$line" -ge "$s" ] && [ "$line" -le "$e" ]; then res=FAIL
  elif [ "$rc" -eq 0 ]; then res=PASS
  else res="FAIL-ELSEWHERE"; fi
  if [ "$res" = "$expect" ]; then ok=ok; else ok=UNEXPECTED; bad=1; fi
  echo "$name | $file:$idx '$old' -> '$new' | $thm ($tf:$s-$e) | exit $rc | $res | $ok | $first" | tee -a "$OUT"
}

linkmut() { # name file directive-index old new: mutate the .S and expect check.py to fail
  name=$1; file=$2; idx=$3; old=$4; new=$5
  want "$name" || return 0
  clone "$name"; d="$SCR/neg-$name"
  edit "$d/fv/kraken/link/out/norm/$file" "$idx" "$old" "$new"
  rc=0; python3 "$d/fv/kraken/link/check.py" "$d/fv/kraken/link/out" > "$d/check.log" 2>&1 || rc=$?
  first=$(grep -m1 'FAIL' "$d/check.log" | cut -c1-200 || true)
  if [ "$rc" -ne 0 ]; then res=FAIL; ok=ok; else res=PASS; ok=UNEXPECTED; bad=1; fi
  echo "$name | $file:$idx '$old' -> '$new' | link/check.py | exit $rc | $res | $ok | $first" | tee -a "$OUT"
}

# 1. offset constant: the decoder compares the offset with 8 instead of 4
mutate offset target.ListU64.UnmarshalSSZ.S 15 'cmp $0x4,%rdx' 'cmp $0x8,%rdx' Fk/LuAccept.lean lu_accept_main FAIL
# 2. length check removed: the jg to the "more than 16 elements" error is gone
mutate maxlen target.ListU64.UnmarshalSSZ.S 28 'jg L_target.ListU64.UnmarshalSSZ_ce' 'nop' Fk/LuRejectCall.lean lu_reject_toobig_main FAIL
# 3. loop bound off by one: the W copy loop stops after 3 elements
mutate loop target.FixedVec.UnmarshalSSZ.S 47 'cmp $0x4,%rax' 'cmp $0x3,%rax' Fk/FvLoop.lean fv_iter FAIL
# 4. growslice num (X1): BitL passes num = 0 (rcx was cleared) instead of n,
#    so the old slice would have n bytes; GrowsliceC's premise fails at the call
mutate gsnum target.BitL.UnmarshalSSZ.S 76 'mov %rbx,%rdi' 'mov %rcx,%rdi' Fk/BlAccept.lean bl_accept_main FAIL
# control: a directive rewritten to itself must still check
mutate control target.FixedVec.UnmarshalSSZ.S 47 'cmp $0x4,%rax' 'cmp $0x4,%rax' Fk/FvLoop.lean fv_iter PASS
# 5. link (X6): a padding nop becomes retq; the link check must reject it
linkmut nopret target.BitVec.UnmarshalSSZ.S 8 'nop' 'retq'

exit $bad
