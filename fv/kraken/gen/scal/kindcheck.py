#!/usr/bin/env python3
"""Reader-side check of the `_kind` lines of a generated scal file (review fix-r2 N2).

The `_kind` line is generator output. Lean checks it (`with_reducible rfl`), but Lean does not check WHICH
kind it names: a degenerate right-hand side (for example `type_of% (@t h)` itself, or `True`) also compiles.
This program is run by the evaluator on every generated file. It does not change the generator.

usage: kindcheck.py <generated.lean>...      exit 0 = every file passes, 1 = a file fails, 2 = usage
       kindcheck.py --selftest               crafted good and bad files; exit 0 = all controls behave

Checks, per file (text only):
 0. The file is not a partial generator output: no line contains `PARTIAL OUTPUT` (the header that
    `scalgen.py p2dec --partial-out` writes on exit 3; review sg1-r1 S2). Checked on the raw text,
    comments included.
 1. `lean/E2eScal/Kind.lean` has the frozen git blob id KIND_BLOB (method freeze of the hold-out).
 2. Top-level lines are only: import, open, variable, namespace, end, set_option … in, theorem, doc or
    plain comments, blank lines and indented continuation lines. No def / abbrev / notation / macro /
    axiom / instance / attribute etc. (a local definition could shadow the kind name).
 3. No `sorry`, `admit`, `native_decide`, `bv_decide`, `axiom` token anywhere.
 4. Every theorem `t` whose name does not end in `_kind` or `_same` is followed by exactly one theorem
    `t_kind` whose whole header is
        theorem t_kind : ∀ (h : Host), type_of% (@t h) = @E2eScal.u64DecAcceptKind h C := by
    or  theorem t_kind : ∀ (h : Host), type_of% (@t h) = @E2eScal.rootDecSegKind h C n1 … n9 := by
    or  theorem t_kind : ∀ (h : Host), type_of% (@t h) = @E2eScal.rootDecSegZKind h C n1 … n8 := by
        (SG-1 offset-0 kind; only when `lean/E2eScal/KindZ.lean` has the pinned blob KINDZ_BLOB)
    with C the code constant of `t`'s `hk : C.IsInfixAt Host.prog k` binder and n1..n9 natural literals,
    and the next line is exactly `  intro h; with_reducible rfl`.
 5. Every `_kind` theorem belongs to a theorem of the file; every `_same` theorem has the form
    `theorem t_same : @X = @t := rfl` for a kinded `t` of the file.

Limits (not checked here): that the kind parameters (C, indices, displacements, offsets) are the right
ones for the Go type (a wrong one fails the proof's code facts, not this check); name resolution (the
check reads `@E2eScal.<kind>` as text; an `open` of a namespace that declares another `E2eScal.<kind>`
would not be seen); that the file builds. A pass is not a non-vacuity witness.
"""
import re
import subprocess
import sys
import pathlib
import tempfile

HERE = pathlib.Path(__file__).resolve().parent
KR = HERE.parent.parent
KIND = KR / "lean" / "E2eScal" / "Kind.lean"
KIND_BLOB = "3c9b95b1b37036831527396975d4232cc20174f3"  # method freeze 56dfc27 (INBOX 019)
KINDZ = KR / "lean" / "E2eScal" / "KindZ.lean"
KINDZ_BLOB = "0c790fa1882cd2e91419c285f66de0810c2b85e2"  # SG-1 extension (after both hold-outs were opened)

PARTIAL = "PARTIAL OUTPUT"  # header of scalgen.py p2dec --partial-out (exit 3)
TOP_OK = re.compile(r"^(import |open |variable |namespace |end\b|set_option \S+ \S+ in$|theorem |/-|--|$|\s)")
BANNED = re.compile(r"\b(sorry|admit|native_decide|bv_decide|axiom)\b")
THM = re.compile(r"^theorem (\S+)")
HK = re.compile(r"\(hk : (\S+)\.IsInfixAt Host\.prog k\)")
NAT = r"(?:0|[1-9][0-9]*)"


def blob(path):
    return subprocess.run(["git", "hash-object", str(path)], capture_output=True, text=True, check=True).stdout.strip()


def check_text(text, kind_blob, kindz_blob=KINDZ_BLOB):
    errs = []
    if kind_blob != KIND_BLOB:
        errs.append(f"Kind.lean blob {kind_blob} != frozen {KIND_BLOB}")
    lines = text.split("\n")
    for i, l in enumerate(lines, 1):
        if PARTIAL in l:
            errs.append(f"line {i}: partial generator output (`{PARTIAL}` header): not a complete generated file")
    in_block = 0
    for i, l in enumerate(lines, 1):
        # skip block comments (doc and plain) for the top-level and banned-token checks
        if in_block or l.lstrip().startswith("/-"):
            in_block += l.count("/-") - l.count("-/")
            continue
        code = l.split("--", 1)[0]
        if BANNED.search(code):
            errs.append(f"line {i}: banned token: {l.strip()}")
        if not TOP_OK.match(l):
            errs.append(f"line {i}: top-level form not allowed: {l.strip()[:80]}")
    thms = [(i, m.group(1)) for i, l in enumerate(lines) if (m := THM.match(l))]
    names = [n for _, n in thms]
    if len(set(names)) != len(names):
        errs.append("duplicate theorem names")
    mains = [n for n in names if not n.endswith("_kind") and not n.endswith("_same")]
    if not mains:
        errs.append("no generated theorem found")
    pos = {n: i for i, n in thms}
    for t in mains:
        i = pos[t]
        # header of t up to ':=' ; code constant from its hk binder
        hdr = "\n".join(lines[i:i + 40]).split(":=", 1)[0]
        hk = HK.search(hdr)
        if not hk:
            errs.append(f"{t}: no `(hk : C.IsInfixAt Host.prog k)` binder")
            continue
        C = re.escape(hk.group(1))
        nxt = [n for _, n in thms if _ > i]
        if not nxt or nxt[0] != t + "_kind":
            errs.append(f"{t}: the next theorem is not {t}_kind")
            continue
        j = pos[t + "_kind"]
        want = (rf"theorem {re.escape(t)}_kind : ∀ \(h : Host\), type_of% \(@{re.escape(t)} h\) = "
                rf"@E2eScal\.(u64DecAcceptKind h {C}|rootDecSegKind h {C}(?: {NAT}){{9}}"
                rf"|rootDecSegZKind h {C}(?: {NAT}){{8}}) := by")
        if not re.fullmatch(want, lines[j]):
            errs.append(f"{t}_kind: header is not a frozen kind: {lines[j][:160]}")
        elif "@E2eScal.rootDecSegZKind " in lines[j] and kindz_blob != KINDZ_BLOB:
            errs.append(f"{t}_kind: KindZ.lean blob {kindz_blob} != pinned {KINDZ_BLOB}")
        if j + 1 >= len(lines) or lines[j + 1] != "  intro h; with_reducible rfl":
            errs.append(f"{t}_kind: proof line is not `  intro h; with_reducible rfl`")
    for n in names:
        if n.endswith("_kind") and n[:-5] not in mains:
            errs.append(f"{n}: no generated theorem {n[:-5]}")
        if n.endswith("_same"):
            t = n[:-5]
            if t not in mains or not re.fullmatch(rf"theorem {re.escape(n)} : @\S+ = @{re.escape(t)} := rfl", lines[pos[n]]):
                errs.append(f"{n}: not an identity `@X = @{t} := rfl` of a kinded theorem")
    return errs, mains


def main(files):
    kb = blob(KIND)
    kzb = blob(KINDZ) if KINDZ.exists() else "missing"
    bad = 0
    for f in files:
        errs, mains = check_text(pathlib.Path(f).read_text(), kb, kzb)
        print(("PASS" if not errs else "FAIL"), f, "theorems:", ",".join(mains))
        for e in errs:
            print("  ", e)
        bad |= bool(errs)
    print("Kind.lean blob", kb, "frozen" if kb == KIND_BLOB else "NOT FROZEN")
    print("KindZ.lean blob", kzb, "pinned" if kzb == KINDZ_BLOB else "NOT PINNED")
    return 1 if bad else 0


GOOD = """import E2eScal.P1
import E2eScal.Kind

/-! generated -/

open Fk E2eAd.Code
variable [Host]

namespace E2eScal.Gen

set_option maxRecDepth 100000 in
theorem t (k : Nat) (hk : VxUnmarshal.IsInfixAt Host.prog k)
    (hf : LabelsFresh VxUnmarshal k) : P := by
  with_reducible exact foo
theorem t_kind : ∀ (h : Host), type_of% (@t h) = @E2eScal.u64DecAcceptKind h VxUnmarshal := by
  intro h; with_reducible rfl

/-- doc -/
theorem s (k : Nat) (hk : BhUnmarshal.IsInfixAt Host.prog k) (hf : LabelsFresh BhUnmarshal k) :
    Q := by
  exact bar
theorem s_kind : ∀ (h : Host), type_of% (@s h) = @E2eScal.rootDecSegKind h BhUnmarshal 86 100 128 136 104 24 32 40 16 := by
  intro h; with_reducible rfl

theorem z (k : Nat) (hk : E1Unmarshal.IsInfixAt Host.prog k) (hf : LabelsFresh E1Unmarshal k) :
    Z := by
  with_reducible exact baz
theorem z_kind : ∀ (h : Host), type_of% (@z h) = @E2eScal.rootDecSegZKind h E1Unmarshal 13 26 48 56 24 8 16 24 := by
  intro h; with_reducible rfl

theorem t_same : @E2eAd.x = @t := rfl

end E2eScal.Gen
"""


def selftest():
    K = KIND_BLOB
    deg = GOOD.replace("= @E2eScal.u64DecAcceptKind h VxUnmarshal := by", "= type_of% (@t h) := by")
    cases = [
        ("good", GOOD, K, True),
        ("kind_blob_changed", GOOD, "0" * 40, False),
        ("degenerate_rhs_self", deg, K, False),
        ("degenerate_rhs_true", GOOD.replace("= @E2eScal.u64DecAcceptKind h VxUnmarshal := by", "= True := by"), K, False),
        ("other_kind_const", GOOD.replace("u64DecAcceptKind h VxUnmarshal", "u64DecAcceptKind h CiUnmarshal"), K, False),
        ("eight_params", GOOD.replace(" 128 136 104 24 32 40 16", " 128 136 104 24 32 40"), K, False),
        ("missing_kind", GOOD.replace("theorem t_kind", "theorem t_kinx"), K, False),
        ("kind_not_next", GOOD.replace("theorem t_kind :", "theorem zz (hk : VxUnmarshal.IsInfixAt Host.prog k) : True := trivial\ntheorem t_kind :"), K, False),
        ("proof_not_rfl", GOOD.replace("intro h; with_reducible rfl\n\n/--", "intro h; simp\n\n/--"), K, False),
        ("local_abbrev", GOOD.replace("namespace E2eScal.Gen\n", "namespace E2eScal.Gen\nabbrev E2eScal.u64DecAcceptKind := True\n"), K, False),
        ("sorry", GOOD.replace("with_reducible exact foo", "sorry"), K, False),
        ("same_not_identity", GOOD.replace("@E2eAd.x = @t := rfl", "True := trivial"), K, False),
        ("orphan_kind", GOOD + "theorem q_kind : True := trivial\n", K, False),
    ]
    # SG-1 offset-0 kind (rootDecSegZKind, 8 parameters, KindZ.lean pinned); the 5th field: KindZ blob pinned?
    zk = "= @E2eScal.rootDecSegZKind h E1Unmarshal 13 26 48 56 24 8 16 24 := by"
    assert zk in GOOD
    nz = GOOD.split("theorem z (k")[0] + "theorem t_same" + GOOD.split("theorem t_same")[1]
    cases = [c + (True,) for c in cases] + [
        ("z_degenerate_rhs_self", GOOD.replace(zk, "= type_of% (@z h) := by"), K, False, True),
        ("z_degenerate_rhs_true", GOOD.replace(zk, "= True := by"), K, False, True),
        ("z_nine_params", GOOD.replace(zk, zk.replace(" 16 24 :=", " 16 24 0 :=")), K, False, True),
        ("z_seven_params", GOOD.replace(zk, zk.replace(" 16 24 :=", " 16 :=")), K, False, True),
        ("z_other_const", GOOD.replace(zk, zk.replace("E1Unmarshal", "BhUnmarshal")), K, False, True),
        ("z_as_add_kind", GOOD.replace(zk, zk.replace("rootDecSegZKind", "rootDecSegKind")), K, False, True),
        ("z_kindz_blob_changed", GOOD, K, False, False),
        ("no_z_kindz_blob_not_needed", nz, K, True, False),
        # review sg1-r1 S2: a --partial-out file (header text as scalgen.py writes it) must fail, even if
        # every theorem it has is well kinded
        ("partial_output_header", GOOD.replace("/-! generated -/", "/-! PARTIAL OUTPUT (scalgen exit 3): 1 of 2 "
                                               "32-byte fields of `v1alpha1.Eth1Data`; missing: BlockHash -/"),
         K, False, True),
        ("partial_output_in_line_comment", GOOD + "-- PARTIAL OUTPUT\n", K, False, True),
    ]
    bad = []
    for name, text, kb, ok, zpin in cases:
        errs, _ = check_text(text, kb, KINDZ_BLOB if zpin else "0" * 40)
        if (not errs) != ok:
            bad.append((name, errs))
    print("selftest", "PASS" if not bad else f"FAIL {bad}", f"({len(cases)} cases)")
    return 1 if bad else 0


if __name__ == "__main__":
    if sys.argv[1:] == ["--selftest"]:
        sys.exit(selftest())
    if len(sys.argv) < 2:
        print(__doc__)
        sys.exit(2)
    sys.exit(main(sys.argv[1:]))
