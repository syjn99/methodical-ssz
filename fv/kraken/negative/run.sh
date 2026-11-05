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
  cp -R "$K/target" "$d/fv/kraken/target"
  # check.py (g) reads the Go source of ValidateBitvector's format string
  mkdir -p "$d/ssz"; cp "$K/../../ssz/unmarshal.go" "$d/ssz/"
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

linkmut() { # name file directive-index old new: mutate the function .S and all.S
  # consistently, regenerate SHash.lean, and expect check.py to fail in (d)
  name=$1; file=$2; idx=$3; old=$4; new=$5
  want "$name" || return 0
  clone "$name"; d="$SCR/neg-$name"
  edit "$d/fv/kraken/link/out/norm/$file" "$idx" "$old" "$new"
  fn=$(head -1 "$K/link/out/norm/$file" | sed 's/:$//')
  aidx=$(awk -v f="$fn:" '$0 == f { print NR - 1; exit }' "$K/link/out/norm/all.S")
  edit "$d/fv/kraken/link/out/norm/all.S" $((aidx + idx)) "$old" "$new"
  (cd "$d/fv/kraken" && link/shash.sh)
  rc=0; python3 "$d/fv/kraken/link/check.py" "$d/fv/kraken/link/out" > "$d/check.log" 2>&1 || rc=$?
  first=$(grep -m1 'DIFF (d).* FAIL\|^FAIL' "$d/check.log" | cut -c1-200 || true)
  if [ "$rc" -ne 0 ] && grep -q 'DIFF (d).* FAIL' "$d/check.log"; then res=FAIL; ok=ok
  else res="exit $rc"; ok=UNEXPECTED; bad=1; fi
  echo "$name | $file:$idx '$old' -> '$new' (also all.S, SHash regenerated) | link/check.py (d) | exit $rc | $res | $ok | $first" | tee -a "$OUT"
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
# 5. nil errorf (X2): ListC zero path returns the nil from fmt.errorf instead of
#    building the errors.errorString (jne -> je); the error result must break
mutate nilerr target.ListC.UnmarshalSSZ.S 165 'jne L_target.ListC.UnmarshalSSZ_2e7' 'je L_target.ListC.UnmarshalSSZ_2e7' Fk/LcReject.lean lc_reject_zero_main FAIL
# 6. R3: ValidateBitvector accepts on a set padding bit and rejects on a clear
#    one (je -> jne after `test %dl,%dl`); its accept theorem must break
mutate vbvje ssz.ValidateBitvector.S 26 'je L_ssz.ValidateBitvector_9c' 'jne L_ssz.ValidateBitvector_9c' Fk/Vbv.lean vbv_accept_main FAIL
# 7. R3: BitVec.UnmarshalSSZ drops the wrapped ValidateBitvector error and goes
#    on decoding (jne to the return -> jmp to the accept path, a directive only
#    on the reject path); the F1 rejection theorem must break
mutate bvnochk target.BitVec.UnmarshalSSZ.S 34 'jne L_target.BitVec.UnmarshalSSZ_b3' 'jmpq L_target.BitVec.UnmarshalSSZ_b9' Fk/BvSpec.lean bv_reject_padding_main FAIL
# 8. R4: BitL.MarshalSSZTo drops the wrapped ValidateBitlist error and goes on
#    encoding (jne to the error return -> jmp to the append path, a directive
#    only on the reject path); the F2 rejection theorem must break
mutate blmnochk target.BitL.MarshalSSZTo.S 49 'jne L_target.BitL.MarshalSSZTo_102' 'jmpq L_target.BitL.MarshalSSZTo_118' Fk/BlMarshal.lean bl_marshal_reject_main FAIL
# control: a directive rewritten to itself must still check
mutate control target.FixedVec.UnmarshalSSZ.S 47 'cmp $0x4,%rax' 'cmp $0x4,%rax' Fk/FvLoop.lean fv_iter PASS
# 9. link (X6): a padding nop becomes retq; the link check must reject it
linkmut nopret target.BitVec.UnmarshalSSZ.S 8 'nop' 'retq'

exit $bad
