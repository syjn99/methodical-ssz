#!/bin/sh
# Positive and negative controls for decl_dump.lean + decl_drift.py,
# stale_olean.py and regen_check.sh. One line per control.
#
# usage: selftest.sh [--no-lean]
#
# The Lean part compiles tiny core-only fixtures and runs `lean`: run the
# whole selftest under the heavy-job gate. Set LEAN_TOOLCHAIN (for example the
# content of fv/kraken/lean/lean-toolchain) to choose the elan toolchain;
# otherwise the `lean` on PATH is used as it is.
#
# Requires GNU coreutils `date -d` and `touch -d` (the stale_olean controls set
# fixed mtimes). On BSD/macOS those controls fail; they do not pass falsely.
#
# Exit: 0 every control ran and passed; 1 at least one control failed;
# 3 no failure but some controls were skipped (--no-lean). A skip is not a pass.
set -u
here=$(cd "$(dirname "$0")" && pwd)
nolean=0
[ "${1:-}" = "--no-lean" ] && nolean=1
tmp=$(mktemp -d "${TMPDIR:-/tmp}/fv-selftest.XXXXXX") || exit 1
fail=0
skip=0
pass=0

# ctl NAME WANT_RC PATTERN CMD... : pass iff exit code == WANT_RC and the
# combined output matches the extended regex PATTERN ('' = no pattern).
ctl() {
  name=$1 want=$2 pat=$3
  shift 3
  "$@" > "$tmp/out.$name" 2>&1
  rc=$?
  if [ "$rc" -ne "$want" ]; then
    echo "FAIL $name (exit $rc, want $want)"
    sed 's/^/    | /' "$tmp/out.$name" | head -20
    fail=$((fail + 1))
  elif [ -n "$pat" ] && ! grep -Eq -- "$pat" "$tmp/out.$name"; then
    echo "FAIL $name (exit $rc ok, output lacks /$pat/)"
    sed 's/^/    | /' "$tmp/out.$name" | head -20
    fail=$((fail + 1))
  else
    echo "PASS $name (exit $rc)"
    pass=$((pass + 1))
  fi
}

# ---------- regen_check.sh ----------
R=$here/regen_check.sh
g=$tmp/regen
mkdir -p "$g/committed/b"
printf 'hello\n' > "$g/committed/a.txt"
printf 'nested 42\n' > "$g/committed/b/c.txt"
cat > "$g/gen_ok.sh" <<'EOF'
#!/bin/sh
mkdir -p "$REGEN_OUT/b" && printf 'hello\n' > "$REGEN_OUT/a.txt" && printf 'nested %d\n' 42 > "$REGEN_OUT/b/c.txt"
EOF
cat > "$g/gen_nondet.sh" <<'EOF'
#!/bin/sh
mkdir -p "$REGEN_OUT/b" && printf 'hello %s\n' "$$" > "$REGEN_OUT/a.txt" && printf 'nested 42\n' > "$REGEN_OUT/b/c.txt"
EOF
printf '#!/bin/sh\nexit 7\n' > "$g/gen_fail.sh"
printf '#!/bin/sh\nexit 0\n' > "$g/gen_none.sh"
printf '#!/bin/sh\nprintf "one file\\n" > "$REGEN_OUT"\n' > "$g/gen_file.sh"
printf 'one file\n' > "$g/committed_file.txt"
chmod +x "$g"/*.sh
cp -R "$g/committed" "$g/changed"
printf 'hello, edited\n' > "$g/changed/a.txt"
cp -R "$g/committed" "$g/nested"
printf 'nested 43\n' > "$g/nested/b/c.txt"
ctl regen.same          0 '^SAME '                "$R" "$g/committed" -- "$g/gen_ok.sh"
ctl regen.single-file   0 '^SAME '                "$R" "$g/committed_file.txt" -- "$g/gen_file.sh"
ctl regen.changed       1 '^DIFFER '              "$R" "$g/changed" -- "$g/gen_ok.sh"
ctl regen.nested-only   1 '^DIFFER '              "$R" "$g/nested" -- "$g/gen_ok.sh"
ctl regen.gen-error     3 'GENERATOR-FAILED.*exit=7' "$R" "$g/committed" -- "$g/gen_fail.sh"
ctl regen.no-output     4 '^NO-OUTPUT '           "$R" "$g/committed" -- "$g/gen_none.sh"
ctl regen.nondet        5 '^NONDETERMINISTIC '    "$R" "$g/committed" -- "$g/gen_nondet.sh"
ctl regen.usage         2 'usage'                 "$R" "$g/committed" "$g/gen_ok.sh"

# ---------- stale_olean.py ----------
S="python3 -I $here/stale_olean.py"
s=$tmp/stale
mkdir -p "$s/src/A" "$s/build/A" "$s/empty"
touch -d '2026-01-01 00:00:00' "$s/src/A/B.lean"
touch -d '2026-01-02 00:00:00' "$s/build/A/B.olean" "$s/build/A/B.ilean"
t_mid=$(date -d '2026-01-01 12:00:00' +%s)
t_late=$(date -d '2026-01-03 00:00:00' +%s)
ctl stale.fresh         0 'flagged=0'             $S --src "$s/src" --build "$s/build"
ctl stale.since-before  0 'flagged=0'             $S --src "$s/src" --build "$s/build" --since "$t_late"
ctl stale.since-after   1 '^AFTER	A/B.olean'     $S --src "$s/src" --build "$s/build" --since "$t_mid"
touch -d '2026-01-03 00:00:00' "$s/marker"
ctl stale.marker-before 0 'flagged=0'             $S --src "$s/src" --build "$s/build" --marker "$s/marker"
ctl stale.no-artifacts  2 'no .olean'             $S --src "$s/src" --build "$s/empty"
ctl stale.missing-dir   2 'not a directory'       $S --src "$s/src" --build "$s/nope"
touch -d '2026-01-05 00:00:00' "$s/src/A/B.lean"
ctl stale.stale         1 '^STALE	A/B.olean'     $S --src "$s/src" --build "$s/build"
touch -d '2026-01-01 00:00:00' "$s/src/A/B.lean"
touch -d '2026-01-02 00:00:00' "$s/build/A/Gone.olean"
ctl stale.orphan        1 '^ORPHAN	A/Gone.olean' $S --src "$s/src" --build "$s/build"
# only the .ilean is stale: the .olean is newer than the source
mkdir -p "$s/build2/A"
touch -d '2026-01-02 00:00:00' "$s/build2/A/B.olean"
touch -d '2025-12-31 00:00:00' "$s/build2/A/B.ilean"
ctl stale.ilean-only    1 '^STALE	A/B.ilean'     $S --src "$s/src" --build "$s/build2"

# ---------- decl_drift.py (inputs that need no Lean) ----------
D="python3 -I $here/decl_drift.py"
d=$tmp/drift
mkdir -p "$d"
printf '# decl_dump v1 lean=X githash=Y roots=Fix\nFix.a\tdef\t01\t02\t-\n' > "$d/x.tsv"
printf 'Fix.a\tdef\t01\t02\t-\n' > "$d/nohdr.tsv"
printf '# decl_dump v1 lean=X githash=Y roots=Fix\n' > "$d/empty.tsv"
printf '# decl_dump v1 lean=X githash=Y roots=Fix\nFix.a\topaque\t01\t02\t-\n' > "$d/kind.tsv"
ctl drift.missing-file  2 'cannot read'           $D "$d/x.tsv" "$d/nope.tsv"
ctl drift.no-header     2 'missing'               $D "$d/x.tsv" "$d/nohdr.tsv"
ctl drift.empty-dump    2 'vacuous'               $D "$d/x.tsv" "$d/empty.tsv"
ctl drift.usage         2 'usage'                 $D "$d/x.tsv"
ctl drift.kind-only     1 '^CHANGED	Fix\.a	kind: def -> opaque$' $D "$d/x.tsv" "$d/kind.tsv"

# ---------- decl_dump.lean on compiled fixtures ----------
LEAN_CONTROLS="dump.base dump.no-match drift.identical drift.private-def drift.statement drift.axiom-grows \
drift.removed drift.added drift.allowlisted drift.unused-allow drift.allow-no-reason drift.toolchain-mismatch"
if [ $nolean -eq 1 ]; then
  for c in $LEAN_CONTROLS; do echo "SKIP $c (--no-lean)"; skip=$((skip + 1)); done
else
  if [ -n "${LEAN_TOOLCHAIN:-}" ]; then set -- lean "+$LEAN_TOOLCHAIN"; else set -- lean; fi
  F=$here/fixtures
  ok=1
  for v in base same privdef stmt axiom removed added; do
    mkdir -p "$tmp/lib/$v"
    if ! "$@" -R "$F/$v" -o "$tmp/lib/$v/Fix.olean" "$F/$v/Fix.lean" > "$tmp/compile.$v" 2>&1; then
      echo "FAIL compile.$v"; sed 's/^/    | /' "$tmp/compile.$v" | head -20
      fail=$((fail + 1)); ok=0; continue
    fi
    LEAN_PATH=$tmp/lib/$v "$@" --run "$here/decl_dump.lean" Fix > "$tmp/$v.tsv" 2> "$tmp/dump.$v.err"
    rc=$?
    if [ $rc -ne 0 ]; then
      echo "FAIL dump.$v (exit $rc)"; sed 's/^/    | /' "$tmp/dump.$v.err" | head -20
      fail=$((fail + 1)); ok=0
    fi
  done
  if [ $ok -eq 1 ]; then
    head -1 "$tmp/base.tsv" | sed 's/^/INFO /'
    # base dump: private helper is listed, em_dec uses no axiom, stmt is a theorem
    ctl dump.base 0 '' sh -c "grep -Eq '^_private\..*Fix\.helper	def	' '$tmp/base.tsv' && grep -Eq '^Fix\.em_dec	theorem	[0-9a-f]{16}	-	-$' '$tmp/base.tsv' && grep -Eq '^Fix\.stmt	theorem	' '$tmp/base.tsv'"
    ctl dump.no-match 2 'no declaration' env LEAN_PATH="$tmp/lib/base" "$@" --run "$here/decl_dump.lean" --root Nope Fix
    ctl drift.identical    0 'drift=0 allowed=0'                     $D "$tmp/base.tsv" "$tmp/same.tsv"
    ctl drift.private-def  1 '^CHANGED	_private\..*Fix\.helper	value' $D "$tmp/base.tsv" "$tmp/privdef.tsv"
    ctl drift.statement    1 '^CHANGED	Fix\.stmt	type'          $D "$tmp/base.tsv" "$tmp/stmt.tsv"
    ctl drift.axiom-grows  1 '^CHANGED	Fix\.em_dec	axioms: - -> .*Classical\.choice' $D "$tmp/base.tsv" "$tmp/axiom.tsv"
    ctl drift.removed      1 '^REMOVED	Fix\.gone'                   $D "$tmp/base.tsv" "$tmp/removed.tsv"
    ctl drift.added        1 '^ADDED	Fix\.extra'                    $D "$tmp/base.tsv" "$tmp/added.tsv"
    printf '# reviewed change\nFix.stmt  restated as 0 + n = n (fixture control)\n' > "$tmp/allow.txt"
    ctl drift.allowlisted  0 '^ALLOWED	CHANGED	Fix\.stmt	.*reason: restated' $D "$tmp/base.tsv" "$tmp/stmt.tsv" --allow "$tmp/allow.txt"
    ctl drift.unused-allow 1 '^UNUSED-ALLOW	Fix\.stmt'               $D "$tmp/base.tsv" "$tmp/same.tsv" --allow "$tmp/allow.txt"
    printf 'Fix.stmt\n' > "$tmp/allow-bad.txt"
    ctl drift.allow-no-reason 2 'needs'                              $D "$tmp/base.tsv" "$tmp/stmt.tsv" --allow "$tmp/allow-bad.txt"
    sed '1s/lean=[^ ]*/lean=0.0.0-other/' "$tmp/same.tsv" > "$tmp/other.tsv"
    ctl drift.toolchain-mismatch 2 'different Lean builds'           $D "$tmp/base.tsv" "$tmp/other.tsv"
  fi
fi

echo "TOTAL pass=$pass fail=$fail skip=$skip scratch=$tmp"
if [ $fail -ne 0 ]; then exit 1; fi
rm -r "$tmp"
if [ $skip -ne 0 ]; then exit 3; fi
exit 0
