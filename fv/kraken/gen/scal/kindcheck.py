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
    or  theorem t_kind : ∀ (h : Host), type_of% (@t h) = @E2eScal.bytesDecSegKind h n C n1 … n9 := by
    or  theorem t_kind : ∀ (h : Host), type_of% (@t h) = @E2eScal.bytesDecSegZKind h n C n1 … n8 := by
        (GEN2 size-parametric kinds, n = 32, 48 or 96; only when `KindN.lean` and the lemma module `SegN.lean`
        have the pinned blobs GEN2_PINS)
    or  theorem t_kind : ∀ (h : Host), type_of% (@t h) = @E2eScal.u64DecInlineSegKind h C n1 … n4 := by
        (GEN2 inline uint64 kind; only when `KindU64.lean` and `U64Inline.lean` have the pinned blobs GEN2_PINS)
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

# GEN2 (unit G2-G): the kind and lemma modules of the GEN2 L1 / L2 lemmas, pinned at the blobs of the lemma
# unit's head 6c62a49 (`gen2/L` hand-over, "Pins for kindcheck.py"). A new kind is accepted only with both
# its kind module and its lemma module at these blobs.
GEN2_PINS = {
    "KindN.lean": "8947c5757f522463a495ad585d3480b7c2f3830b",
    "SegN.lean": "4ef9c7494e421798c1766aedffa9a59066d32304",
    "KindU64.lean": "dda481f9c61fcbfc9646faef172a240a69a857d1",
    "U64Inline.lean": "712f4856eef48401cfdd48a216d538986a4087a9",
}
GEN2_NEEDS = {"bytesDecSegKind": ("KindN.lean", "SegN.lean"), "bytesDecSegZKind": ("KindN.lean", "SegN.lean"),
              "u64DecInlineSegKind": ("KindU64.lean", "U64Inline.lean")}
SIZE = r"(?:32|48|96)"  # the sizes of the hypothesis `hn` of bytesdec_seg / bytesdec_seg_z

PARTIAL = "PARTIAL OUTPUT"  # header of scalgen.py p2dec --partial-out (exit 3)
TOP_OK = re.compile(r"^(import |open |variable |namespace |end\b|set_option \S+ \S+ in$|theorem |/-|--|$|\s)")
BANNED = re.compile(r"\b(sorry|admit|native_decide|bv_decide|axiom)\b")
THM = re.compile(r"^theorem (\S+)")
HK = re.compile(r"\(hk : (\S+)\.IsInfixAt Host\.prog k\)")
NAT = r"(?:0|[1-9][0-9]*)"


def blob(path):
    return subprocess.run(["git", "hash-object", str(path)], capture_output=True, text=True, check=True).stdout.strip()


def check_text(text, kind_blob, kindz_blob=KINDZ_BLOB, gen2_blobs=None):
    gen2_blobs = dict(GEN2_PINS) if gen2_blobs is None else gen2_blobs
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
                rf"|rootDecSegZKind h {C}(?: {NAT}){{8}}"
                rf"|bytesDecSegKind h {SIZE} {C}(?: {NAT}){{9}}|bytesDecSegZKind h {SIZE} {C}(?: {NAT}){{8}}"
                rf"|u64DecInlineSegKind h {C}(?: {NAT}){{4}}) := by")
        if not re.fullmatch(want, lines[j]):
            errs.append(f"{t}_kind: header is not a frozen kind: {lines[j][:160]}")
        elif "@E2eScal.rootDecSegZKind " in lines[j] and kindz_blob != KINDZ_BLOB:
            errs.append(f"{t}_kind: KindZ.lean blob {kindz_blob} != pinned {KINDZ_BLOB}")
        else:
            for kn, mods in GEN2_NEEDS.items():
                if f"@E2eScal.{kn} " in lines[j]:
                    for m in mods:
                        if gen2_blobs.get(m) != GEN2_PINS[m]:
                            errs.append(f"{t}_kind: {m} blob {gen2_blobs.get(m)} != pinned {GEN2_PINS[m]}")
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
    g2b = {m: (blob(KIND.parent / m) if (KIND.parent / m).exists() else "missing") for m in GEN2_PINS}
    bad = 0
    for f in files:
        errs, mains = check_text(pathlib.Path(f).read_text(), kb, kzb, g2b)
        print(("PASS" if not errs else "FAIL"), f, "theorems:", ",".join(mains))
        for e in errs:
            print("  ", e)
        bad |= bool(errs)
    print("Kind.lean blob", kb, "frozen" if kb == KIND_BLOB else "NOT FROZEN")
    print("KindZ.lean blob", kzb, "pinned" if kzb == KINDZ_BLOB else "NOT PINNED")
    for m, b in g2b.items():
        print(m, "blob", b, "pinned" if b == GEN2_PINS[m] else "NOT PINNED")
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
    cases = [c + (None,) for c in cases] + gen2_cases(K)
    bad = []
    for name, text, kb, ok, zpin, g2 in cases:
        errs, _ = check_text(text, kb, KINDZ_BLOB if zpin else "0" * 40, g2)
        if (not errs) != ok:
            bad.append((name, errs))
    print("selftest", "PASS" if not bad else f"FAIL {bad}", f"({len(cases)} cases)")
    return 1 if bad else 0


# GEN2 controls: one generated-shape block per new kind (headers as `scalgen.py p2dec --gen2` writes them)
GOOD2 = """import E2eScal.SegN
import E2eScal.Kind
import E2eScal.KindN
import E2eScal.KindU64

/-! Generated by `gen/scal/scalgen.py p2dec`; GEN2 coverage (`p2dec --gen2`): 3 of 3 fields. -/

open Fk E2eScal.H3Code
variable [Host]

namespace E2eScal.Gen

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
/-- `PublicKey` (48 bytes, SSZ offset 0, Go offset 0): decode segment, directives 13–36. -/
theorem a (k : Nat) (hk : DmUnmarshal.IsInfixAt Host.prog k) (hf : LabelsFresh DmUnmarshal k) :
    A := by
  with_reducible exact E2eScal.bytesdec_seg_z 48 (Or.inr (Or.inl rfl)) _ _ _ _ _ _ _ _ (k + 13) (k + 26) hA hB hl
theorem a_kind : ∀ (h : Host), type_of% (@a h) = @E2eScal.bytesDecSegZKind h 48 DmUnmarshal 13 26 48 56 24 0 8 16 := by
  intro h; with_reducible rfl

theorem b (k : Nat) (hk : XyUnmarshal.IsInfixAt Host.prog k) (hf : LabelsFresh XyUnmarshal k) :
    B := by
  with_reducible exact E2eScal.bytesdec_seg 96 (Or.inr (Or.inr rfl)) _ _ _ _ _ _ _ _ _ (k + 47) (k + 61) hA hB hl
theorem b_kind : ∀ (h : Host), type_of% (@b h) = @E2eScal.bytesDecSegKind h 96 XyUnmarshal 47 61 48 56 24 24 32 40 48 := by
  intro h; with_reducible rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem c (k : Nat) (hk : DmUnmarshal.IsInfixAt Host.prog k) (hf : LabelsFresh DmUnmarshal k) :
    C := by
  have hX : E2eScal.U64InlineReg Reg64.rcx := by decide
  with_reducible exact E2eScal.u64dec_inline_seg Reg64.rcx hX _ _ _ (k + 83) hA
theorem c_kind : ∀ (h : Host), type_of% (@c h) = @E2eScal.u64DecInlineSegKind h DmUnmarshal 83 56 80 48 := by
  intro h; with_reducible rfl

end E2eScal.Gen
"""


def gen2_cases(K):
    za = "= @E2eScal.bytesDecSegZKind h 48 DmUnmarshal 13 26 48 56 24 0 8 16 := by"
    ab = "= @E2eScal.bytesDecSegKind h 96 XyUnmarshal 47 61 48 56 24 24 32 40 48 := by"
    uc = "= @E2eScal.u64DecInlineSegKind h DmUnmarshal 83 56 80 48 := by"
    for x in (za, ab, uc):
        assert GOOD2.count(x) == 1
    P = dict(GEN2_PINS)

    def pins(**chg):
        d = dict(P)
        d.update({k.replace("_", "."): v for k, v in chg.items()})
        return d
    z40 = "0" * 40
    return [
        ("g2_good", GOOD2, K, True, True, None),
        ("g2_kindN_blob_changed", GOOD2, K, False, True, pins(KindN_lean=z40)),
        ("g2_segN_blob_changed", GOOD2, K, False, True, pins(SegN_lean=z40)),
        ("g2_kindU64_blob_changed", GOOD2, K, False, True, pins(KindU64_lean=z40)),
        ("g2_u64inline_blob_changed", GOOD2, K, False, True, pins(U64Inline_lean=z40)),
        ("g2_no_u64_kindU64_not_needed", GOOD2.split("set_option maxHeartbeats 4000000")[0] + "end E2eScal.Gen\n",
         K, True, True, pins(KindU64_lean=z40, U64Inline_lean=z40)),
        ("g2_z_degenerate_self", GOOD2.replace(za, "= type_of% (@a h) := by"), K, False, True, None),
        ("g2_z_degenerate_true", GOOD2.replace(za, "= True := by"), K, False, True, None),
        ("g2_add_degenerate_self", GOOD2.replace(ab, "= type_of% (@b h) := by"), K, False, True, None),
        ("g2_u64_degenerate_self", GOOD2.replace(uc, "= type_of% (@c h) := by"), K, False, True, None),
        ("g2_u64_degenerate_true", GOOD2.replace(uc, "= True := by"), K, False, True, None),
        ("g2_z_size_64", GOOD2.replace(za, za.replace(" h 48 ", " h 64 ")), K, False, True, None),
        ("g2_add_size_symbolic", GOOD2.replace(ab, ab.replace(" h 96 ", " h n ")), K, False, True, None),
        ("g2_z_size_missing", GOOD2.replace(za, za.replace(" h 48 ", " h ")), K, False, True, None),
        ("g2_add_nine_params", GOOD2.replace(ab, ab.replace(" 40 48 :=", " 40 :=")), K, False, True, None),
        ("g2_z_nine_params", GOOD2.replace(za, za.replace(" 8 16 :=", " 8 16 0 :=")), K, False, True, None),
        ("g2_u64_three_params", GOOD2.replace(uc, uc.replace(" 80 48 :=", " 80 :=")), K, False, True, None),
        ("g2_u64_register_param", GOOD2.replace(uc, uc.replace(" h DmUnmarshal", " h Reg64.rcx DmUnmarshal")),
         K, False, True, None),
        ("g2_u64_other_const", GOOD2.replace(uc, uc.replace("DmUnmarshal", "BiUnmarshal")), K, False, True, None),
        ("g2_add_as_z_kind", GOOD2.replace(ab, ab.replace("bytesDecSegKind", "bytesDecSegZKind")), K, False, True, None),
        ("g2_partial_output", GOOD2.replace("/-! Generated", "/-! PARTIAL OUTPUT (scalgen exit 3): 2 of 3 fields "
                                            "of `v1alpha1.DepositMessage` (--gen2); NOT generated: Amount. -/\n/-! Generated"),
         K, False, True, None),
        ("g2_proof_not_rfl", GOOD2.replace(uc + "\n  intro h; with_reducible rfl", uc + "\n  intro h; rfl"),
         K, False, True, None),
    ]


if __name__ == "__main__":
    if sys.argv[1:] == ["--selftest"]:
        sys.exit(selftest())
    if len(sys.argv) < 2:
        print(__doc__)
        sys.exit(2)
    sys.exit(main(sys.argv[1:]))
