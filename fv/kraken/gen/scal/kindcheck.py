#!/usr/bin/env python3
"""Reader-side check of the `_kind` lines of a generated scal file (review fix-r2 N2).

The `_kind` line is generator output. Lean checks it (`with_reducible rfl`), but Lean does not check WHICH
kind it names: a degenerate right-hand side (for example `type_of% (@t h)` itself, or `True`) also compiles.
This program is run by the evaluator on every generated file. It does not change the generator.

usage: kindcheck.py <generated.lean>...      exit 0 = every file passes, 1 = a file fails, 2 = usage
       kindcheck.py --partial <partial.lean>  a `p2dec --gen2 --partial-out` file (unit G2-F): exit 3 = the
                                             kinds of the theorems that are present pass, printed together with
                                             `PARTIAL n/m fields: kinds of present theorems checked; NOT a
                                             full-coverage result`; 1 = the file fails; 2 = usage. Never 0.
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
 6. GEN2 composed accept theorems (`scalgen.py p2dec --gen2 --compose`): instead of `t_kind`, a theorem `t`
    may be followed by exactly
        theorem t_type : ∀ (h : Host),
            type_of% (@t h) = type_of% (@X h) := by
          intro h; with_reducible rfl
    with X a dotted name under `E2eScal.` that is not `t` and not declared in the file (a hand theorem), or
    (`--same-as-prop`, unit G2-F) the Prop form
        theorem t_type : ∀ (h : Host),
            type_of% (@t h) = @X h := by
          intro h; with_reducible rfl
    with X a Prop-valued `abbrev` written by hand. This is an identity, NOT a kind. Unit G2-F (review g2g-r1
    S1) restricts it:
     6a. `_type` is accepted ONLY for a composed theorem: its proof (the lines up to the next theorem) uses
         both `E2eScal.dechead_seg` and `E2eScal.decepi_seg`. A segment theorem needs its `_kind`; a `_type`
         in place of a `_kind` fails.
     6b. X must not be a generated name: not under a namespace `E2eScal.Gen…` (`Gen`, `Gen2Ex`, …) and not a
         name declared in a module `lean/E2eScal/Gen*.lean` (compared by the last name component). A
         generated theorem never vouches for a generated theorem.
     6c. A theorem line with the marker `UNCHECKED STATEMENT` (`--compose` without `--same-as`) fails.
    The PASS line names X: "identity against X — statement evidence only if X is an independent hand
    statement". Whether X is independent is NOT checked here (a human must confirm it). A composed theorem
    of a type without a hand statement (no `_type`) FAILS. There is no kind for a composed statement.
 7. `--partial` mode (unit G2-F): the file must carry exactly one `PARTIAL OUTPUT` header, after the imports,
    with `n of m fields`, and one line `UNCOVERED-JSON: [...]` (a JSON list of {field, reason}) whose length
    is m - n; the theorems present are checked by rules 1-6 as usual (no composed theorem allowed). The
    default mode rejects every partial file (rule 0, unchanged).
 8. GEN3 (unit G3-G, `scalgen.py p2dec --gen3`): further `_kind` right-hand sides, each only when its kind
    module and lemma module have the pinned blobs GEN3_PINS:
        @E2eScal.callDecSegKind h C "fn" "lok" j j2      fn one of the four callee labels with a proved accept
                                                         spec (CALLEES: Slot, CommitteeIndex, ValidatorIndex,
                                                         Epoch of consensus-types/primitives)
        @E2eScal.callArgFirstKind h C pad f j            pad = true | false
        @E2eScal.callArgReloadKind h C pad dB src dD c dR f j     (Int64 literals: n or (-n))
        @E2eScal.callArgLeaKind h C dB src dD c dR f j
        @E2eScal.callArgMovKind h C j
        @E2eScal.u64DecRRSegKind h C Reg64.rX src f j    rX one of the registers of `U64RRReg`
    (KindCall.lean + CallDec.lean, or KindCall.lean + U64RR.lean for the last). A `bytesDecSegKind` theorem
    whose proof uses `E2eScal.bytesdec_seg_p` needs SegNPad.lean pinned as well. A composed accept theorem
    (rule 6a) may instead carry the composed-statement kind (lemma unit L4, KindAccept.lean pinned):
        set_option maxHeartbeats 200000 in
        theorem t_kind : ∀ (h : Host), type_of% (@t h) = @E2eScal.decAcceptKind h C st [f, …] jret := by
          intro h; rfl
    with st = true | false, f = `.bytes 32|48|96` or `.u64`; `rfl` at default transparency (the recursive kind
    must unfold) under the default heartbeat limit written out (a timeout is a FAIL). An identity `t_type`
    (rule 6) may follow the `t_kind` of a composed theorem. A segment theorem cannot carry `decAcceptKind`.
 9. Hardening (review g2f-r1 S1-S3, unit G3-G): rule 6a is read on the proof text WITHOUT comments; a file
    with a coverage header `GEN2|GEN3 coverage (…): n of m fields` fails in the default mode when n != m;
    in both modes n must equal the number of fields with theorems present (theorem names
    `<prefix>_<field>_seg|_arg|_arg1|_arg2|_call`; a callee field needs `_call` and `_arg` or `_arg1` + `_arg2`),
    and no field of `UNCOVERED-JSON` may have a theorem.

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
GENNS = re.compile(r"^E2eScal\.Gen\w*\.")  # rule 6b: generated namespaces (E2eScal.Gen, E2eScal.Gen2Ex, ...)
DECL = re.compile(r"^(?:private |protected |noncomputable )*(?:theorem|lemma|def|abbrev) (\S+)")
COMPOSED = ("(E2eScal.dechead_seg ", "(E2eScal.decepi_seg ")  # rule 6a
UNCHECKED = "UNCHECKED STATEMENT"  # rule 6c

# GEN2 (unit G2-G): the kind and lemma modules of the GEN2 L1 / L2 lemmas, pinned at the blobs of the lemma
# unit's head 6c62a49 (the lemma unit's hand-over, "Pins for kindcheck.py"). A new kind is accepted only with both
# its kind module and its lemma module at these blobs.
GEN2_PINS = {
    "KindN.lean": "8947c5757f522463a495ad585d3480b7c2f3830b",
    "SegN.lean": "4ef9c7494e421798c1766aedffa9a59066d32304",
    "KindU64.lean": "dda481f9c61fcbfc9646faef172a240a69a857d1",
    "U64Inline.lean": "712f4856eef48401cfdd48a216d538986a4087a9",
}
GEN2_NEEDS = {"bytesDecSegKind": ("KindN.lean", "SegN.lean"), "bytesDecSegZKind": ("KindN.lean", "SegN.lean"),
              "u64DecInlineSegKind": ("KindU64.lean", "U64Inline.lean")}
# GEN3 (unit G3-G): kind and lemma modules of the GEN3 lemma unit, pinned at its head f5c5f52 (hand-over "Pins")
GEN3_PINS = {
    "KindCall.lean": "02b006726b77166dd07783aae20d6b4c02a3953e",
    "CallDec.lean": "1401e7bc860375c16240b34d80f00aba294f83f2",
    "U64RR.lean": "59d7b31e8b32fe6ffae52d194124adb12edf885c",
    "SegNPad.lean": "289199f2ab3fe19da34737ccd75d4e3b6f1d047f",
    "KindAccept.lean": "0752ed7f7e856bb766479e445e81eb06ac47d2e4",
}
GEN3_NEEDS = {"callDecSegKind": ("KindCall.lean", "CallDec.lean"), "callArgFirstKind": ("KindCall.lean", "CallDec.lean"),
              "callArgReloadKind": ("KindCall.lean", "CallDec.lean"), "callArgLeaKind": ("KindCall.lean", "CallDec.lean"),
              "callArgMovKind": ("KindCall.lean", "CallDec.lean"), "u64DecRRSegKind": ("KindCall.lean", "U64RR.lean"),
              "decAcceptKind": ("KindAccept.lean",)}
CALLEES = tuple(f'"github.com_OffchainLabs_prysm_v7_consensus_types_primitives.{n}.UnmarshalSSZ"'
                for n in ("Slot", "CommitteeIndex", "ValidatorIndex", "Epoch"))
INT = r"(?:0|[1-9][0-9]*|\(-[1-9][0-9]*\))"  # an Int64 literal as the generator writes it
BOOL = r"(?:true|false)"
LBL = r'"[^"\\\s]+"'
RRREG = r"Reg64\.(?:rcx|rdx|rsi|rdi|r8|r9|r10|r11|r12|r13|r15)"
DECF = r"\.(?:bytes (?:32|48|96)|u64)"
COVER = re.compile(r"GEN[23] coverage \(`p2dec --gen[23]`\): (\d+) of (\d+) fields")
STEM = re.compile(r"^(.*)_(seg|arg|arg1|arg2|call)$")
SIZE = r"(?:32|48|96)"  # the sizes of the hypothesis `hn` of bytesdec_seg / bytesdec_seg_z

PARTIAL = "PARTIAL OUTPUT"  # header of scalgen.py p2dec --partial-out (exit 3)
TOP_OK = re.compile(r"^(import |open |variable |namespace |end\b|set_option \S+ \S+ in$|theorem |/-|--|$|\s)")
BANNED = re.compile(r"\b(sorry|admit|native_decide|bv_decide|axiom)\b")
THM = re.compile(r"^theorem (\S+)")
HK = re.compile(r"\(hk : (\S+)\.IsInfixAt Host\.prog k\)")
NAT = r"(?:0|[1-9][0-9]*)"


def blob(path):
    return subprocess.run(["git", "hash-object", str(path)], capture_output=True, text=True, check=True).stdout.strip()


def gen_names(lean_dir=KIND.parent):
    """Rule 6b: last name components of every declaration in a module `Gen*.lean` (generated or example)."""
    out = set()
    for f in sorted(lean_dir.glob("Gen*.lean")):
        for l in f.read_text().split("\n"):
            if (m := DECL.match(l)):
                out.add(m.group(1).rsplit(".", 1)[-1])
    return out


def partial_header(lines):
    """Rule 7: (n, m, uncovered list) of a `--partial-out` file, or an error string."""
    import json
    hs = [i for i, l in enumerate(lines) if PARTIAL in l]
    if len(hs) != 1:
        return f"{len(hs)} `{PARTIAL}` headers (expected 1)"
    i = hs[0]
    imps = [j for j, l in enumerate(lines) if l.startswith("import ")]
    if not imps or i < max(imps):
        return "the PARTIAL header is not after the imports"
    m = re.search(r"\b(\d+) of (\d+) fields\b", lines[i])
    js = [l for l in lines if l.startswith("UNCOVERED-JSON: ")]
    if not m or len(js) != 1:
        return "no `n of m fields` in the PARTIAL header or not exactly one `UNCOVERED-JSON:` line"
    try:
        unc = json.loads(js[0][len("UNCOVERED-JSON: "):])
    except ValueError as e:
        return f"UNCOVERED-JSON does not parse: {e}"
    n, tot = int(m.group(1)), int(m.group(2))
    if not (isinstance(unc, list) and all(isinstance(u, dict) and set(u) == {"field", "reason"} for u in unc)):
        return "UNCOVERED-JSON is not a list of {field, reason}"
    if not 0 < n < tot or len(unc) != tot - n:
        return f"PARTIAL {n} of {tot} fields with {len(unc)} uncovered entries"
    return n, tot, unc


def strip_comments(s):
    """Rule 9 (review g2f-r1 S1): Lean text without `--` line comments and `/- … -/` block comments (nested)."""
    out, i, depth = [], 0, 0
    while i < len(s):
        if s.startswith("/-", i):
            depth, i = depth + 1, i + 2
        elif depth and s.startswith("-/", i):
            depth, i = depth - 1, i + 2
        elif depth:
            i += 1
        elif s.startswith("--", i):
            j = s.find("\n", i)
            i = len(s) if j < 0 else j
        else:
            out.append(s[i])
            i += 1
    return "".join(out)


def field_stems(mains):
    """Rule 9: {stem: set of suffixes} of the segment theorems (composed theorems excluded by the caller)."""
    st = {}
    for t in mains:
        m = STEM.match(t)
        st.setdefault(m.group(1) if m else t, set()).add(m.group(2) if m else "")
    return st


def check_text(text, kind_blob, kindz_blob=KINDZ_BLOB, gen2_blobs=None, gnames=None, partial=False, gen3_blobs=None):
    gen2_blobs = dict(GEN2_PINS) if gen2_blobs is None else gen2_blobs
    gen3_blobs = dict(GEN3_PINS) if gen3_blobs is None else gen3_blobs
    gnames = gen_names() if gnames is None else gnames
    errs = []
    if kind_blob != KIND_BLOB:
        errs.append(f"Kind.lean blob {kind_blob} != frozen {KIND_BLOB}")
    lines = text.split("\n")
    if partial:
        ph = partial_header(lines)
        if isinstance(ph, str):
            errs.append(f"--partial: {ph}")
    else:
        for i, l in enumerate(lines, 1):
            if PARTIAL in l:
                errs.append(f"line {i}: partial generator output (`{PARTIAL}` header): not a complete generated file")
    for i, l in enumerate(lines, 1):
        if UNCHECKED in l:
            errs.append(f"line {i}: `{UNCHECKED}` marker (composed statement without a hand statement)")
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
    mains = [n for n in names if not n.endswith("_kind") and not n.endswith("_same") and not n.endswith("_type")]
    ident = []
    if not mains:
        errs.append("no generated theorem found")
    pos = {n: i for i, n in thms}
    composed = set()

    def is_composed(t, j):
        body = strip_comments("\n".join(lines[pos[t]:j]))  # rule 9 (S1): comments do not count
        return all(c in body for c in COMPOSED)

    def type_line(t):
        j = pos[t + "_type"]
        nx = lines[j + 1] if j + 1 < len(lines) else ""
        m = (re.fullmatch(rf"    type_of% \(@{re.escape(t)} h\) = type_of% \(@(E2eScal(?:\.\w+)+) h\) := by", nx)
             or re.fullmatch(rf"    type_of% \(@{re.escape(t)} h\) = @(E2eScal(?:\.\w+)+) h := by", nx))
        if lines[j] != f"theorem {t}_type : ∀ (h : Host),":
            errs.append(f"{t}_type: header is not `theorem {t}_type : ∀ (h : Host),`")
        elif not m:
            errs.append(f"{t}_type: not an identity `type_of% (@{t} h) = type_of% (@E2eScal.… h)` "
                        f"or `= @E2eScal.… h`: {nx[:160]}")
        elif m.group(1).rsplit(".", 1)[-1] in names or m.group(1) == t:
            errs.append(f"{t}_type: right-hand side {m.group(1)} is declared in this file (degenerate identity)")
        elif GENNS.match(m.group(1)) or m.group(1).rsplit(".", 1)[-1] in gnames:
            errs.append(f"{t}_type: right-hand side {m.group(1)} is a generated name (namespace E2eScal.Gen… or "
                        f"declared in a Gen*.lean module): a generated theorem cannot vouch for a generated theorem")
        if j + 2 >= len(lines) or lines[j + 2] != "  intro h; with_reducible rfl":
            errs.append(f"{t}_type: proof line is not `  intro h; with_reducible rfl`")
        ident.append((t, m.group(1) if m else "?"))

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
        if nxt and nxt[0] == t + "_type":
            j = pos[t + "_type"]
            type_line(t)
            if not is_composed(t, j):
                errs.append(f"{t}_type: {t} is not a composed accept theorem (its proof does not use "
                            f"E2eScal.dechead_seg and E2eScal.decepi_seg): a segment theorem needs its `_kind`")
            elif partial:
                errs.append(f"{t}: composed theorem in a partial file")
            composed.add(t)
            continue
        if not nxt or nxt[0] != t + "_kind":
            errs.append(f"{t}: the next theorem is not {t}_kind")
            continue
        j = pos[t + "_kind"]
        acc = rf"theorem {re.escape(t)}_kind : ∀ \(h : Host\), type_of% \(@{re.escape(t)} h\) = " \
              rf"@E2eScal\.decAcceptKind h {C} {BOOL} \[{DECF}(?:, {DECF})*\] {NAT} := by"
        if re.fullmatch(acc, lines[j]):
            # GEN3 composed-statement kind (rule 8): composed theorems only, default heartbeats written out
            composed.add(t)
            if not is_composed(t, j):
                errs.append(f"{t}_kind: decAcceptKind on a theorem that is not a composed accept theorem")
            elif partial:
                errs.append(f"{t}: composed theorem in a partial file")
            if lines[j - 1] != "set_option maxHeartbeats 200000 in":
                errs.append(f"{t}_kind: the line before is not `set_option maxHeartbeats 200000 in`")
            if j + 1 >= len(lines) or lines[j + 1] != "  intro h; rfl":
                errs.append(f"{t}_kind: proof line is not `  intro h; rfl`")
            if gen3_blobs.get("KindAccept.lean") != GEN3_PINS["KindAccept.lean"]:
                errs.append(f"{t}_kind: KindAccept.lean blob {gen3_blobs.get('KindAccept.lean')} != pinned "
                            f"{GEN3_PINS['KindAccept.lean']}")
            nx2 = [n for _, n in thms if _ > j]
            if nx2 and nx2[0] == t + "_type":
                type_line(t)
            continue
        want = (rf"theorem {re.escape(t)}_kind : ∀ \(h : Host\), type_of% \(@{re.escape(t)} h\) = "
                rf"@E2eScal\.(u64DecAcceptKind h {C}|rootDecSegKind h {C}(?: {NAT}){{9}}"
                rf"|rootDecSegZKind h {C}(?: {NAT}){{8}}"
                rf"|bytesDecSegKind h {SIZE} {C}(?: {NAT}){{9}}|bytesDecSegZKind h {SIZE} {C}(?: {NAT}){{8}}"
                rf"|u64DecInlineSegKind h {C}(?: {NAT}){{4}}"
                rf"|callDecSegKind h {C} {LBL} {LBL} {NAT} {NAT}"
                rf"|callArgFirstKind h {C} {BOOL} {INT} {NAT}"
                rf"|callArgReloadKind h {C} {BOOL}(?: {INT}){{6}} {NAT}"
                rf"|callArgLeaKind h {C}(?: {INT}){{6}} {NAT}"
                rf"|callArgMovKind h {C} {NAT}"
                rf"|u64DecRRSegKind h {C} {RRREG}(?: {INT}){{2}} {NAT}) := by")
        if not re.fullmatch(want, lines[j]):
            errs.append(f"{t}_kind: header is not a frozen kind: {lines[j][:160]}")
        elif "@E2eScal.callDecSegKind " in lines[j] and lines[j].split(f" h {hk.group(1)} ", 1)[1].split(" ")[0] not in CALLEES:
            errs.append(f"{t}_kind: callee {lines[j].split(f' h {hk.group(1)} ', 1)[1].split(' ')[0]} has no proved "
                        f"accept spec (allowed: Slot, CommitteeIndex, ValidatorIndex, Epoch of consensus-types/primitives)")
        elif "@E2eScal.rootDecSegZKind " in lines[j] and kindz_blob != KINDZ_BLOB:
            errs.append(f"{t}_kind: KindZ.lean blob {kindz_blob} != pinned {KINDZ_BLOB}")
        else:
            for kn, mods in GEN2_NEEDS.items():
                if f"@E2eScal.{kn} " in lines[j]:
                    for m in mods:
                        if gen2_blobs.get(m) != GEN2_PINS[m]:
                            errs.append(f"{t}_kind: {m} blob {gen2_blobs.get(m)} != pinned {GEN2_PINS[m]}")
            needs = [mods for kn, mods in GEN3_NEEDS.items() if f"@E2eScal.{kn} " in lines[j]]
            if "@E2eScal.bytesDecSegKind " in lines[j] and "E2eScal.bytesdec_seg_p " in strip_comments("\n".join(lines[i:j])):
                needs.append(("SegNPad.lean",))
            for mods in needs:
                for m in mods:
                    if gen3_blobs.get(m) != GEN3_PINS[m]:
                        errs.append(f"{t}_kind: {m} blob {gen3_blobs.get(m)} != pinned {GEN3_PINS[m]}")
        if j + 1 >= len(lines) or lines[j + 1] != "  intro h; with_reducible rfl":
            errs.append(f"{t}_kind: proof line is not `  intro h; with_reducible rfl`")
    # rule 9 (review g2f-r1 S2, S3): the coverage numbers agree with the theorems present
    cov = [COVER.search(l) for l in lines]
    cov = [c for c in cov if c]
    stems = field_stems([t for t in mains if t not in composed])
    for s, sx in stems.items():
        if "call" in sx and not ("arg" in sx or {"arg1", "arg2"} <= sx):
            errs.append(f"{s}: call-block theorem without its argument set-up theorem(s)")
        if sx & {"arg", "arg1", "arg2"} and "call" not in sx:
            errs.append(f"{s}: argument set-up theorem(s) without the call-block theorem")
        if sx & {"seg"} and sx & {"arg", "arg1", "arg2", "call"}:
            errs.append(f"{s}: segment and call-field theorems for one field")
    if len(cov) > 1:
        errs.append(f"{len(cov)} coverage headers (expected at most 1)")
    elif cov:
        cn, cm = int(cov[0].group(1)), int(cov[0].group(2))
        if not partial and cn != cm:
            errs.append(f"coverage header `{cn} of {cm} fields` with n != m in the default mode (not a complete output)")
        if cn != len(stems):
            errs.append(f"coverage header says {cn} fields, theorems present for {len(stems)} fields")
    if partial and not isinstance(ph, str):
        pn = ph[0]
        if pn != len(stems):
            errs.append(f"--partial: header says {pn} fields, theorems present for {len(stems)} fields")
        for u in ph[2]:
            if any(s == u["field"] or s.endswith("_" + u["field"]) for s in stems):
                errs.append(f"--partial: uncovered field {u['field']} has theorems")
    for n in names:
        if n.endswith("_kind") and n[:-5] not in mains:
            errs.append(f"{n}: no generated theorem {n[:-5]}")
        if n.endswith("_type") and n[:-5] not in [x for x, _ in ident]:
            errs.append(f"{n}: not the identity line of a generated theorem {n[:-5]}")
        if n.endswith("_same"):
            t = n[:-5]
            if t not in mains or not re.fullmatch(rf"theorem {re.escape(n)} : @\S+ = @{re.escape(t)} := rfl", lines[pos[n]]):
                errs.append(f"{n}: not an identity `@X = @{t} := rfl` of a kinded theorem")
    idm = dict(ident)
    out = []
    for t in mains:
        acc = t in composed and t + "_kind" in pos
        if t in idm:
            t += (f" (decAcceptKind; also identity against {idm[t]})" if acc else
                  f" (identity against {idm[t]} — statement evidence only if {idm[t]} is an independent hand "
                  f"statement; no kind)")
        elif acc:
            t += " (composed-statement kind decAcceptKind)"
        out.append(t)
    return errs, out


def main(files, partial=False):
    kb = blob(KIND)
    kzb = blob(KINDZ) if KINDZ.exists() else "missing"
    g2b = {m: (blob(KIND.parent / m) if (KIND.parent / m).exists() else "missing") for m in GEN2_PINS}
    g3b = {m: (blob(KIND.parent / m) if (KIND.parent / m).exists() else "missing") for m in GEN3_PINS}
    gn = gen_names()
    bad = 0
    for f in files:
        text = pathlib.Path(f).read_text()
        errs, mains = check_text(text, kb, kzb, g2b, gn, partial, g3b)
        print(("PASS" if not errs else "FAIL"), f, "theorems:", ",".join(mains))
        for e in errs:
            print("  ", e)
        if partial and not errs:
            n, tot, unc = partial_header(text.split("\n"))
            print(f"PARTIAL {n}/{tot} fields: kinds of present theorems checked; NOT a full-coverage result "
                  f"(uncovered: {', '.join(u['field'] for u in unc)})")
        bad |= bool(errs)
    print("Kind.lean blob", kb, "frozen" if kb == KIND_BLOB else "NOT FROZEN")
    print("KindZ.lean blob", kzb, "pinned" if kzb == KINDZ_BLOB else "NOT PINNED")
    for m, b in g2b.items():
        print(m, "blob", b, "pinned" if b == GEN2_PINS[m] else "NOT PINNED")
    for m, b in g3b.items():
        print(m, "blob", b, "pinned" if b == GEN3_PINS[m] else "NOT PINNED")
    if partial:
        return 1 if bad else 3
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
    cases = [c + (False,) for c in cases] + g2f_cases(K)
    cases = [c + (None,) for c in cases] + g3_cases(K)
    for name, text, kb, ok, zpin, g2, part, g3 in cases:
        errs, _ = check_text(text, kb, KINDZ_BLOB if zpin else "0" * 40, g2, GNAMES, part, g3)
        if (not errs) != ok:
            bad.append((name, errs))
    # review g2f-r1 S4: the exit codes of main() (`--partial`: 3 on success, 1 on failure, never 0; default: 1)
    n_exit, bad_exit = s4_exit_cases()
    bad += bad_exit
    print("selftest", "PASS" if not bad else f"FAIL {bad}", f"({len(cases)} cases + {n_exit} exit-code cases)")
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


COMP = """import E2eScal.Compose
import E2eScal.Kind

/-! Generated by `gen/scal/scalgen.py p2dec`; composed accept theorem; statement check: identity. -/

open Fk E2eScal.H3Code
variable [Host]

namespace E2eScal.Gen

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem d (k : Nat) (hk : DmUnmarshal.IsInfixAt Host.prog k) (hf : LabelsFresh DmUnmarshal k)
    (x1 : List UInt8) :
    D := by
  refine eventually_trans _ _ _ _ (E2eScal.dechead_seg _ _ _ _ 88 (k + 0) hH) ?_
  refine eventually_trans _ _ _ _ (E2eScal.Gen.dm_g2dec_Amount_seg k hk hf) ?_
  refine eventually_trans _ _ _ _ (E2eScal.decepi_seg (k + 86) hE) ?_

/-- Statement check: the declared type is that of the hand theorem (definitional identity). -/
theorem d_type : ∀ (h : Host),
    type_of% (@d h) = type_of% (@E2eScal.Dm.dm_e2e_accept_main h) := by
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
        ("g2_no_u64_kindU64_not_needed", GOOD2.split("set_option maxHeartbeats 4000000")[0].replace(" 3 of 3 fields", " 2 of 2 fields") + "end E2eScal.Gen\n",
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
        ("g2c_good_identity", COMP, K, True, True, None),
        ("g2c_no_identity", COMP.split("\n/-- Statement check")[0] + "\nend E2eScal.Gen\n", K, False, True, None),
        ("g2c_degenerate_self", COMP.replace("type_of% (@E2eScal.Dm.dm_e2e_accept_main h)", "type_of% (@d h)"),
         K, False, True, None),
        ("g2c_rhs_declared_here", COMP.replace("@E2eScal.Dm.dm_e2e_accept_main h", "@E2eScal.Gen.d h"),
         K, False, True, None),
        ("g2c_rhs_true", COMP.replace("type_of% (@E2eScal.Dm.dm_e2e_accept_main h) := by", "True := by"),
         K, False, True, None),
        ("g2c_proof_not_rfl", COMP.replace("  intro h; with_reducible rfl", "  intro h; rfl"), K, False, True, None),
        ("g2c_orphan_type", GOOD2 + "theorem q_type : ∀ (h : Host),\n    type_of% (@q h) = type_of% (@E2eScal.X h) := by\n"
                                     "  intro h; with_reducible rfl\n", K, False, True, None),
    ]


# rule 6b in the selftest: a fixed set of "generated" names instead of the tree's Gen*.lean (the controls do
# not depend on the tree); `gen_seg_x` stands for a theorem of another generated module
GNAMES = {"gen_seg_x", "bi_e2e_accept_main_gc", "bi_e2e_accept_main_composed"}


def g2f_cases(K):
    """Unit G2-F controls: rules 6a-6c and 7 (review g2g-r1 S1, for_h4 items 2 and 4)."""
    ty = ("theorem {t}_type : ∀ (h : Host),\n    type_of% (@{t} h) = type_of% (@E2eScal.Dm.dm_e2e_accept_main h) := by\n"
          "  intro h; with_reducible rfl\n")
    uc = "theorem c_kind : ∀ (h : Host), type_of% (@c h) = @E2eScal.u64DecInlineSegKind h DmUnmarshal 83 56 80 48 := by\n  intro h; with_reducible rfl\n"
    assert GOOD2.count(uc) == 1
    seg_type = GOOD2.replace(uc, ty.format(t="c"))           # reviewer case (i): `_type` in place of a segment kind
    rhs = "type_of% (@E2eScal.Dm.dm_e2e_accept_main h)"
    assert COMP.count(rhs) == 1
    gen_rhs = COMP.replace(rhs, "type_of% (@E2eScal.Gen.bi_e2e_accept_main_gc h)")  # reviewer case (ii)
    prop = COMP.replace(rhs, "@E2eScal.Fx.dmStmt h")
    unc = json_line([("Slot", "delegated overlay field"), ("ProposerIndex", "delegated overlay field")])
    PH = ("/-! PARTIAL OUTPUT (scalgen exit 3): 3 of 5 fields of `v1alpha1.BeaconBlockHeader` (--gen2); NOT "
          "generated: Slot, ProposerIndex. Not a complete p2dec output.\n" + unc + "\n-/\n")
    part = GOOD2.replace("\n/-! Generated", "\n" + PH + "/-! Generated").replace(" 3 of 3 fields", " 3 of 5 fields")
    assert part.count(PARTIAL) == 1
    return [
        ("g2f_segment_type_instead_of_kind", seg_type, K, False, True, None, False),
        ("g2f_rhs_generated_namespace", gen_rhs, K, False, True, None, False),
        ("g2f_rhs_gen2ex_namespace", COMP.replace(rhs, "type_of% (@E2eScal.Gen2Ex.bi_e2e_accept_main_composed h)"),
         K, False, True, None, False),
        ("g2f_rhs_generated_namespace_fresh_name", COMP.replace(rhs, "type_of% (@E2eScal.Gen.zz_fresh h)"),
         K, False, True, None, False),
        ("g2f_unchecked_marker_with_identity", COMP.replace(
            "(hf : LabelsFresh DmUnmarshal k)\n", "(hf : LabelsFresh DmUnmarshal k) -- UNCHECKED STATEMENT\n"),
         K, False, True, None, False),
        ("g2f_rhs_declared_in_gen_module", COMP.replace(rhs, "type_of% (@E2eScal.Other.gen_seg_x h)"),
         K, False, True, None, False),
        ("g2f_composed_without_decepi", COMP.replace("E2eScal.decepi_seg", "E2eScal.decepi_sex"), K, False, True, None, False),
        ("g2f_prop_identity_good", prop, K, True, True, None, False),
        ("g2f_prop_identity_generated_rhs", COMP.replace(rhs, "@E2eScal.Gen.bi_e2e_accept_main_gc h"),
         K, False, True, None, False),
        ("g2f_prop_identity_on_segment", GOOD2.replace(uc, ty.format(t="c").replace(rhs, "@E2eScal.Fx.dmStmt h")),
         K, False, True, None, False),
        ("g2f_unchecked_marker", COMP.split("\n/-- Statement check")[0].replace(
            "(hf : LabelsFresh DmUnmarshal k)\n", "(hf : LabelsFresh DmUnmarshal k) -- UNCHECKED STATEMENT\n")
         + "\nend E2eScal.Gen\n", K, False, True, None, False),
        ("g2f_partial_default_rejects", part, K, False, True, None, False),
        ("g2f_partial_mode_good", part, K, True, True, None, True),
        ("g2f_partial_mode_complete_file", GOOD2, K, False, True, None, True),
        ("g2f_partial_mode_header_before_imports", PH + GOOD2.replace(" 3 of 3 fields", " 3 of 5 fields"),
         K, False, True, None, True),
        ("g2f_partial_mode_count_mismatch", part.replace(unc, json_line([("Slot", "x")])), K, False, True, None, True),
        ("g2f_partial_mode_bad_kind", part.replace(" 83 56 80 48 := by", " 83 56 80 := by"), K, False, True, None, True),
        ("g2f_partial_mode_composed", COMP.replace("\n/-! Generated", "\n" + PH + "/-! Generated"),
         K, False, True, None, True),
    ]


# GEN3 controls (unit G3-G): generated-shape blocks with the kind lines as `scalgen.py p2dec --gen3` writes them
FN_VI = '"github.com_OffchainLabs_prysm_v7_consensus_types_primitives.ValidatorIndex.UnmarshalSSZ"'
FN_EP = '"github.com_OffchainLabs_prysm_v7_consensus_types_primitives.Epoch.UnmarshalSSZ"'
G3K = {
    "pw_Index_arg": "@E2eScal.callArgFirstKind h PwUnmarshal false 8 15",
    "pw_Index_call": f'@E2eScal.callDecSegKind h PwUnmarshal {FN_VI} "L_pw_b9" 17 47',
    "pw_Amount_seg": "@E2eScal.u64DecRRSegKind h PwUnmarshal Reg64.r8 8 16 54",
    "pw_WithdrawableEpoch_arg1": "@E2eScal.callArgLeaKind h PwUnmarshal 96 16 112 (-16) 88 24 48",
    "pw_WithdrawableEpoch_arg2": "@E2eScal.callArgMovKind h PwUnmarshal 56",
    "pw_WithdrawableEpoch_call": f'@E2eScal.callDecSegKind h PwUnmarshal {FN_EP} "L_pw_159" 59 88',
    "bh_ProposerIndex_arg": "@E2eScal.callArgReloadKind h PwUnmarshal true 120 8 136 (-8) 112 16 47",
    "bh_ProposerIndex_call": f'@E2eScal.callDecSegKind h PwUnmarshal {FN_VI} "L_bh_154" 55 85',
    "dd_WithdrawalCredentials_seg": "@E2eScal.bytesDecSegKind h 32 PwUnmarshal 47 61 48 56 24 32 40 48 48",
}
G3PROOF = {"pw_Amount_seg": "  have hX : E2eScal.U64RRReg Reg64.r8 := by decide\n  with_reducible exact E2eScal.u64dec_rr_seg Reg64.r8 hX _ _ (k + 54) hA\n",
           "dd_WithdrawalCredentials_seg": "  with_reducible exact E2eScal.bytesdec_seg_p true 32 (Or.inl rfl) _ _ _ _ _ _ _ _ _ (k + 47) (k + 61) hA hB hl\n"}


def g3_block(t, kind):
    return ("set_option maxHeartbeats 4000000 in\nset_option maxRecDepth 100000 in\n"
            f"theorem {t} (k : Nat) (hk : PwUnmarshal.IsInfixAt Host.prog k) (hf : LabelsFresh PwUnmarshal k) :\n"
            f"    T := by\n" + G3PROOF.get(t, "  with_reducible exact foo\n")
            + f"theorem {t}_kind : ∀ (h : Host), type_of% (@{t} h) = {kind} := by\n  intro h; with_reducible rfl\n\n")


GOOD3 = ("import E2eScal.KindCall\nimport E2eScal.SegNPad\nimport E2eScal.Kind\nimport E2eScal.KindN\n\n"
         "/-! Generated by `gen/scal/scalgen.py p2dec`; GEN3 coverage (`p2dec --gen3`): 5 of 5 fields. -/\n\n"
         "open Fk E2eScal.H4Code\nvariable [Host]\n\nnamespace E2eScal.Gen\n\n"
         + "".join(g3_block(t, k) for t, k in G3K.items()) + "end E2eScal.Gen\n")

COMP3 = COMP.replace("composed accept theorem; statement check: identity", "composed accept theorem (`p2dec --gen3 --compose`)").replace(
    "\n/-- Statement check: the declared type is that of the hand theorem",
    "\n/-- Statement check: kind. -/\nset_option maxHeartbeats 200000 in\n"
    "theorem d_kind : ∀ (h : Host), type_of% (@d h) = @E2eScal.decAcceptKind h DmUnmarshal false [.bytes 48, .bytes 32, .u64] 68 := by\n"
    "  intro h; rfl\n\n/-- Statement check: the declared type is that of the hand theorem")


def g3_cases(K):
    """Unit G3-G controls: rule 8 (GEN3 kinds, pins, callee list, decAcceptKind) and rule 9 (g2f-r1 S1-S3)."""
    z40 = "0" * 40
    P3 = dict(GEN3_PINS)

    def pins(m):
        d = dict(P3)
        d[m] = z40
        return d

    def kchg(t, new):
        old = f"type_of% (@{t} h) = {G3K[t]} := by"
        assert GOOD3.count(old) == 1, t
        return GOOD3.replace(old, f"type_of% (@{t} h) = {new} := by")

    def drop(text, t):
        b = g3_block(t, G3K[t])
        assert text.count(b) == 1
        return text.replace(b, "")
    comp_kind = "@E2eScal.decAcceptKind h DmUnmarshal false [.bytes 48, .bytes 32, .u64] 68 := by"
    assert COMP3.count(comp_kind) == 1
    comp_only = COMP3.split("\n/-- Statement check: the declared type")[0] + "\nend E2eScal.Gen\n"
    # g2f-r1 k04: `_type` in place of a segment `_kind`, the two composed lemma names only in a comment
    uc = "theorem c_kind : ∀ (h : Host), type_of% (@c h) = @E2eScal.u64DecInlineSegKind h DmUnmarshal 83 56 80 48 := by\n  intro h; with_reducible rfl\n"
    ty = ("theorem c_type : ∀ (h : Host),\n    type_of% (@c h) = type_of% (@E2eScal.Dm.dm_e2e_accept_main h) := by\n"
          "  intro h; with_reducible rfl\n")
    k04 = GOOD2.replace(uc, ty).replace("  with_reducible exact E2eScal.u64dec_inline_seg Reg64.rcx hX _ _ _ (k + 83) hA\n",
                                        "  -- (E2eScal.dechead_seg x) (E2eScal.decepi_seg y)\n"
                                        "  with_reducible exact E2eScal.u64dec_inline_seg Reg64.rcx hX _ _ _ (k + 83) hA\n")
    k04b = k04.replace("  -- (E2eScal.dechead_seg x) (E2eScal.decepi_seg y)\n", "  /- (E2eScal.dechead_seg x) (E2eScal.decepi_seg y) -/\n")
    # g2f-r1 k22-k24 and S4 (partial / coverage counts)
    unc = json_line([("Slot", "delegated overlay field"), ("ProposerIndex", "delegated overlay field")])
    PH = ("/-! PARTIAL OUTPUT (scalgen exit 3): 3 of 5 fields of `v1alpha1.BeaconBlockHeader` (--gen2); NOT "
          "generated: Slot, ProposerIndex. Not a complete p2dec output.\n" + unc + "\n-/\n")
    part = GOOD2.replace("\n/-! Generated", "\n" + PH + "/-! Generated").replace(" 3 of 3 fields", " 3 of 5 fields")
    k22 = part.split("set_option maxHeartbeats 4000000")[0] + "end E2eScal.Gen\n"
    k24 = GOOD2.replace(" 3 of 3 fields", " 3 of 5 fields")
    unc1 = json_line([("ProposerIndex", "x")])
    nm = part.replace("3 of 5 fields of", "3 of 3 fields of").replace(unc, "UNCOVERED-JSON: []")
    n0 = part.replace("3 of 5 fields of", "0 of 5 fields of")
    unc_has_thm = part.replace(unc, json_line([("c", "x"), ("Slot", "y")]))
    return [
        ("g3_good", GOOD3, K, True, True, None, False, None),
        ("g3_kindcall_blob_changed", GOOD3, K, False, True, None, False, pins("KindCall.lean")),
        ("g3_calldec_blob_changed", GOOD3, K, False, True, None, False, pins("CallDec.lean")),
        ("g3_u64rr_blob_changed", GOOD3, K, False, True, None, False, pins("U64RR.lean")),
        ("g3_segnpad_blob_changed", GOOD3, K, False, True, None, False, pins("SegNPad.lean")),
        ("g3_segnpad_not_needed_without_pad", GOOD2, K, True, True, None, False, pins("SegNPad.lean")),
        ("g3_kindaccept_not_needed_for_segments", GOOD3, K, True, True, None, False, pins("KindAccept.lean")),
        ("g3_callee_without_spec", kchg("pw_Index_call", G3K["pw_Index_call"].replace(
            "consensus_types_primitives.ValidatorIndex", "proto_prysm_v1alpha1.Checkpoint")), K, False, True, None, False, None),
        ("g3_call_degenerate_self", kchg("pw_Index_call", "type_of% (@pw_Index_call h)"), K, False, True, None, False, None),
        ("g3_call_degenerate_true", kchg("pw_Index_call", "True"), K, False, True, None, False, None),
        ("g3_call_one_index", kchg("pw_Index_call", G3K["pw_Index_call"].replace(" 17 47", " 17")), K, False, True, None, False, None),
        ("g3_first_pad_not_bool", kchg("pw_Index_arg", G3K["pw_Index_arg"].replace(" false ", " 1 ")), K, False, True, None, False, None),
        ("g3_first_negative_index", kchg("pw_Index_arg", G3K["pw_Index_arg"].replace(" 15", " (-15)")), K, False, True, None, False, None),
        ("g3_reload_five_ints", kchg("bh_ProposerIndex_arg", G3K["bh_ProposerIndex_arg"].replace(" (-8)", "")), K, False, True, None, False, None),
        ("g3_lea_seven_ints", kchg("pw_WithdrawableEpoch_arg1", G3K["pw_WithdrawableEpoch_arg1"].replace(" 24 48", " 24 0 48")), K, False, True, None, False, None),
        ("g3_mov_extra_param", kchg("pw_WithdrawableEpoch_arg2", G3K["pw_WithdrawableEpoch_arg2"] + " 0"), K, False, True, None, False, None),
        ("g3_rr_register_rax", kchg("pw_Amount_seg", G3K["pw_Amount_seg"].replace("Reg64.r8", "Reg64.rax")), K, False, True, None, False, None),
        ("g3_rr_register_missing", kchg("pw_Amount_seg", G3K["pw_Amount_seg"].replace("Reg64.r8 ", "")), K, False, True, None, False, None),
        ("g3_rr_as_inline_kind", kchg("pw_Amount_seg", "@E2eScal.u64DecInlineSegKind h PwUnmarshal 54 8 8 16"), K, True, True, None, False, None),
        ("g3_call_without_arg", drop(GOOD3, "pw_Index_arg"), K, False, True, None, False, None),
        ("g3_lea_without_arg2", drop(GOOD3, "pw_WithdrawableEpoch_arg2"), K, False, True, None, False, None),
        ("g3_arg_without_call", drop(GOOD3, "pw_Index_call"), K, False, True, None, False, None),
        ("g3_decaccept_on_segment", kchg("pw_Amount_seg", "@E2eScal.decAcceptKind h PwUnmarshal true [.u64] 54"), K, False, True, None, False, None),
        ("g3c_good_kind_and_identity", COMP3, K, True, True, None, False, None),
        ("g3c_good_kind_only", comp_only, K, True, True, None, False, None),
        ("g3c_kindaccept_blob_changed", COMP3, K, False, True, None, False, pins("KindAccept.lean")),
        ("g3c_heartbeats_raised", COMP3.replace("set_option maxHeartbeats 200000 in\ntheorem d_kind", "set_option maxHeartbeats 2000000 in\ntheorem d_kind"), K, False, True, None, False, None),
        ("g3c_no_heartbeat_line", COMP3.replace("set_option maxHeartbeats 200000 in\ntheorem d_kind", "theorem d_kind"), K, False, True, None, False, None),
        ("g3c_with_reducible", COMP3.replace("  intro h; rfl\n", "  intro h; with_reducible rfl\n"), K, False, True, None, False, None),
        ("g3c_field_size_64", COMP3.replace(comp_kind, comp_kind.replace(".bytes 48", ".bytes 64")), K, False, True, None, False, None),
        ("g3c_empty_fields", COMP3.replace(comp_kind, comp_kind.replace("[.bytes 48, .bytes 32, .u64]", "[]")), K, False, True, None, False, None),
        ("g3c_st_not_bool", COMP3.replace(comp_kind, comp_kind.replace(" false [", " 0 [")), K, False, True, None, False, None),
        ("g3c_other_const", COMP3.replace(comp_kind, comp_kind.replace("DmUnmarshal", "BiUnmarshal")), K, False, True, None, False, None),
        ("g3c_not_composed_comment_only", comp_only.replace("(E2eScal.decepi_seg (k + 86) hE)", "foo -- (E2eScal.decepi_seg "),
         K, False, True, None, False, None),
        ("s1_k04_line_comment", k04, K, False, True, None, False, None),
        ("s1_k04_block_comment", k04b, K, False, True, None, False, None),
        ("s2_k22_theorem_removed_partial", k22, K, False, True, None, True, None),
        ("s2_k23_uncovered_entry_dropped", part.replace("3 of 5 fields of", "4 of 5 fields of").replace(unc, unc1), K, False, True, None, True, None),
        ("s2_uncovered_field_has_theorem", unc_has_thm, K, False, True, None, True, None),
        ("s3_k24_partial_block_deleted", k24, K, False, True, None, False, None),
        ("s3_header_count_mismatch_full", GOOD2.replace(" 3 of 3 fields", " 4 of 4 fields"), K, False, True, None, False, None),
        ("s4_partial_n_equals_m", nm, K, False, True, None, True, None),
        ("s4_partial_n_zero", n0, K, False, True, None, True, None),
        ("s4_partial_good_0_lt_n_lt_m", part, K, True, True, None, True, None),
    ]


def s4_exit_cases():
    """Review g2f-r1 S4: main() exit codes on a temporary partial file (pins read from the tree)."""
    import contextlib, io, os
    unc = json_line([("Slot", "delegated overlay field"), ("ProposerIndex", "delegated overlay field")])
    PH = ("/-! PARTIAL OUTPUT (scalgen exit 3): 3 of 5 fields of `v1alpha1.BeaconBlockHeader` (--gen2); NOT "
          "generated: Slot, ProposerIndex. Not a complete p2dec output.\n" + unc + "\n-/\n")
    part = GOOD2.replace("\n/-! Generated", "\n" + PH + "/-! Generated").replace(" 3 of 3 fields", " 3 of 5 fields")
    badp = part.replace(" 83 56 80 48 := by", " 83 56 80 := by")
    out = []
    for name, text, partial, want in [("s4_exit_partial_good", part, True, 3), ("s4_exit_partial_bad", badp, True, 1),
                                      ("s4_exit_default_on_partial", part, False, 1), ("s4_exit_default_good", GOOD2, False, 0)]:
        fd, path = tempfile.mkstemp(suffix=".lean")
        os.close(fd)
        pathlib.Path(path).write_text(text)
        with contextlib.redirect_stdout(io.StringIO()):
            rc = main([path], partial=partial)
        os.unlink(path)
        if rc != want:
            out.append((name, f"exit {rc}, expected {want}"))
    return 4, out


def json_line(pairs):
    import json
    return "UNCOVERED-JSON: " + json.dumps([dict(field=f, reason=r) for f, r in pairs])


if __name__ == "__main__":
    if sys.argv[1:] == ["--selftest"]:
        sys.exit(selftest())
    if len(sys.argv) < 2 or sys.argv[1:] == ["--partial"]:
        print(__doc__)
        sys.exit(2)
    if sys.argv[1] == "--partial":
        sys.exit(main(sys.argv[2:], partial=True))
    sys.exit(main(sys.argv[1:]))
