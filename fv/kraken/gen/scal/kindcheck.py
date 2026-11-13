#!/usr/bin/env python3
"""Reader-side check of the `_kind` lines of a generated scal file.

The `_kind` line is generator output. Lean checks it (`with_reducible rfl`), but Lean does not check WHICH
kind it names: a degenerate right-hand side (for example `type_of% (@t h)` itself, or `True`) also compiles.
This program is run by the evaluator on every generated file. It does not change the generator.

usage: kindcheck.py <generated.lean>...      exit 0 = every file passes, 1 = a file fails, 2 = usage
       kindcheck.py --partial <partial.lean>  a `p2dec --gen2 --partial-out` file: exit 3 = the
                                             kinds of the theorems that are present pass, printed together with
                                             `PARTIAL n/m fields: kinds of present theorems checked; NOT a
                                             full-coverage result`; 1 = the file fails; 2 = usage. Never 0.
       kindcheck.py --selftest               crafted good and bad files; exit 0 = all controls behave

Checks, per file (text only):
 0. The file is not a partial generator output: no line contains `PARTIAL OUTPUT` (the header that
    `scalgen.py p2dec --partial-out` writes on exit 3). Checked on the raw text,
    comments included.
 1. (Removed: git-blob pins of the kind and lemma modules. They were the method freeze of an experiment that ended.)
 2. Top-level lines are only: import, open, variable, namespace, end, set_option … in, theorem, doc or
    plain comments, blank lines and indented continuation lines. No def / abbrev / notation / macro /
    axiom / instance / attribute etc. (a local definition could shadow the kind name).
 3. No `sorry`, `admit`, `native_decide`, `bv_decide`, `axiom` token anywhere.
 4. Every theorem `t` whose name does not end in `_kind` or `_same` is followed by exactly one theorem
    `t_kind` whose whole header is
        theorem t_kind : ∀ (h : Host), type_of% (@t h) = @Codec.u64DecAcceptKind h C := by
    or  theorem t_kind : ∀ (h : Host), type_of% (@t h) = @Codec.rootDecSegKind h C n1 … n9 := by
    or  theorem t_kind : ∀ (h : Host), type_of% (@t h) = @Codec.rootDecSegZKind h C n1 … n8 := by
        (offset-0 kind of the generator extension, `lean/Codec/Kind/Bytes32DecodeOffsetZero.lean`)
    or  theorem t_kind : ∀ (h : Host), type_of% (@t h) = @Codec.bytesDecSegKind h n C n1 … n9 := by
    or  theorem t_kind : ∀ (h : Host), type_of% (@t h) = @Codec.bytesDecSegZKind h n C n1 … n8 := by
        (GEN2 size-parametric kinds, n = 32, 48 or 96)
    or  theorem t_kind : ∀ (h : Host), type_of% (@t h) = @Codec.u64DecInlineSegKind h C n1 … n4 := by
        (GEN2 inline uint64 kind)
    with C the code constant of `t`'s `hk : C.IsInfixAt Host.prog k` binder and n1..n9 natural literals,
    and the next line is exactly `  intro h; with_reducible rfl`.
 5. Every `_kind` theorem belongs to a theorem of the file; every `_same` theorem has the form
    `theorem t_same : @X = @t := rfl` for a kinded `t` of the file.
 6. GEN2 composed accept theorems (`scalgen.py p2dec --gen2 --compose`): instead of `t_kind`, a theorem `t`
    may be followed by exactly
        theorem t_type : ∀ (h : Host),
            type_of% (@t h) = type_of% (@X h) := by
          intro h; with_reducible rfl
    with X a dotted name under `Prysm.` that is not `t` and not declared in the file (a hand theorem), or
    (`--same-as-prop`) the Prop form
        theorem t_type : ∀ (h : Host),
            type_of% (@t h) = @X h := by
          intro h; with_reducible rfl
    with X a Prop-valued `abbrev` written by hand. This is an identity, NOT a kind. These rules
    restrict it:
     6a. `_type` is accepted ONLY for a composed theorem: its proof (the lines up to the next theorem) uses
         both `Codec.dechead_seg` and `Codec.decepi_seg`. A segment theorem needs its `_kind`; a `_type`
         in place of a `_kind` fails.
     6b. X must not be a generated name: not `Prysm.<T>.Decode.generated…` / `.example…` (or Encode) and not a
         name declared in a module `lean/Prysm/<T>/Generated*.lean` or `Decode*Example*.lean` (last name component). A
         generated theorem never vouches for a generated theorem.
     6c. A theorem line with the marker `UNCHECKED STATEMENT` (`--compose` without `--same-as`) fails.
    The PASS line names X: "identity against X — statement evidence only if X is an independent hand
    statement". Whether X is independent is NOT checked here (a human must confirm it). A composed theorem
    of a type without a hand statement (no `_type`) FAILS. There is no kind for a composed statement.
 7. `--partial` mode: the file must carry exactly one `PARTIAL OUTPUT` header, after the imports,
    with `n of m fields`, and one line `UNCOVERED-JSON: [...]` (a JSON list of {field, reason}) whose length
    is m - n; the theorems present are checked by rules 1-6 as usual (no composed theorem allowed). The
    default mode rejects every partial file (rule 0, unchanged).
 8. GEN3 (`scalgen.py p2dec --gen3`): further `_kind` right-hand sides:
        @Codec.callDecSegKind h C "fn" "lok" j j2      fn one of the four callee labels with a proved accept
                                                         spec (CALLEES: Slot, CommitteeIndex, ValidatorIndex,
                                                         Epoch of consensus-types/primitives)
        @Codec.callArgFirstKind h C pad f j            pad = true | false
        @Codec.callArgReloadKind h C pad dB src dD c dR f j     (Int64 literals: n or (-n))
        @Codec.callArgLeaKind h C dB src dD c dR f j
        @Codec.callArgMovKind h C j
        @Codec.u64DecRRSegKind h C Reg64.rX src f j    rX one of the registers of `U64RRReg`
    (kinds of `lean/Codec/Kind/CalleeDecode.lean`). A composed accept theorem
    (rule 6a) may instead carry the composed-statement kind of `lean/Codec/Kind/DecodeAcceptComposition.lean`:
        set_option maxHeartbeats 200000 in
        theorem t_kind : ∀ (h : Host), type_of% (@t h) = @Codec.decAcceptKind h C st [f, …] jret := by
          intro h; rfl
    with st = true | false, f = `.bytes 32|48|96` or `.u64`; `rfl` at default transparency (the recursive kind
    must unfold) under the default heartbeat limit written out (a timeout is a FAIL). An identity `t_type`
    (rule 6) may follow the `t_kind` of a composed theorem. A segment theorem cannot carry `decAcceptKind`.
 9. Hardening: rule 6a is read on the proof text WITHOUT comments; a file
    with a coverage header `GEN2|GEN3 coverage (…): n of m fields` fails in the default mode when n != m;
    in both modes n must equal the number of fields with theorems present (theorem names
    `<prefix>_<field>_seg|_arg|_arg1|_arg2|_call`; a callee field needs `_call` and `_arg` or `_arg1` + `_arg2`),
    and no field of `UNCOVERED-JSON` may have a theorem.

10. GEN4 (`scalgen.py p2dec --gen4`): further `_kind` right-hand sides:
        @Codec.stepMovRRKind h C Reg64.rD Reg64.rS j e          @Codec.stepAddKind h C Reg64.rD imm j e
        @Codec.stepLdvKind / stepLdbKind / stepStKind / stepLeaKind h C Reg64.r1 Reg64.r2 disp j e
        @Codec.stepMovIKind h C Reg64.rD imm j e                @Codec.stepJmpKind h C "l" j jl
        @Codec.stepLabelKind h C "l" j e                        @Codec.stepNopsKind h C j e
        @Codec.callDecSegKindG4 h C "fn" "lok" j jc j2         (fn in CALLEES)
        @Codec.bytesDecSegKindWindow h n C Reg64.rY j1 jm e dR dB dS fP fL fC src
        @Codec.bytesDecSegZKindWindow h n C Reg64.rY j1 jm e dR dB dS fP fL fC
    (n = 32 | 48 | 96; rY one of rax, rcx, rdx, rsi, rdi; registers `Reg64.<one of the 16>`).
    10b. The proof of `t` (comments and string literals removed) uses the lemma of its kind
         (`kstep_mov_rr`, `kstep_ldv`, …, `calldec_seg_w`, `bytesdec_seg_window`, `bytesdec_seg_z_window`) and no other
         GEN4 lemma: a theorem whose proof and kind name different lemmas fails.
    10c. A GEN4 file (header `GEN4 coverage (…): n of m fields`, or any GEN4 kind) carries exactly one line
         `FIELDS-JSON: [{"field": F, "theorems": [...]}, …]`: every theorem with a GEN4 kind is listed in exactly
         one field, every listed theorem is in the file, a field has at most one block theorem (`<p>_F_call` with
         `callDecSegKindG4`, or `<p>_F_seg` with a byte kind), n = the number of listed fields; in `--partial` mode
         no field of `UNCOVERED-JSON` is listed (its entries may carry a `miss_class`).
11. A file in which a non-composed theorem has a GEN2 / GEN3 / GEN4 kind must
    carry the coverage header (`GEN2|GEN3|GEN4 coverage (…): n of m fields`); rule 6a also ignores string literals.
    Exemption: the hand example modules listed in HAND_EXAMPLES (exact paths
    `lean/Prysm/DepositMessage/DecodeFieldSegmentExamples.lean`, `Prysm/PendingPartialWithdrawal/DecodeCallSegmentExamples.lean`) are not generator output and skip rule 11 only; every
    other rule applies to them. `Prysm/SyncCommitteeMessage/DecodeStepExamples.lean` is not listed: its hand field compositions fail rules 4 and 10c,
    and no recorded command runs `kindcheck.py` on it.
    6d. A composed accept theorem with only the kind `decAcceptKind` (no
    identity `_type` with an independent hand statement) FAILS; `scalgen.py --gen3 --compose` without `--same-as*`
    now also marks it `UNCHECKED STATEMENT` (rule 6c).
12. GEN5 (`scalgen.py p2dec --gen5`): a GEN5 file is checked in two parts. The text before the GEN5
    block (`/-! GEN5 (`p2dec --gen5`…`) by rules 1-11 as a GEN4 file; the GEN5 part by rule 12 (12a removed: it was
    a git-blob pin; 12b the exact theorem list with the kinds decHeadKindN / decFieldKindN / decEpiKindN /
    decAcceptKindN / decRejectKindN; 12c the kind parameters `L`, `fields`, boundary `pc` / `done` and the reject size
    RECOMPUTED from the `.S` and the IR named in the header (sha256 checked); 12d the accept proof chains every
    theorem; 12e the identity with a hand statement, if any, names no generated theorem). See the section `Rule 12`.
    A file with a GEN5 kind and no GEN5 block fails (rule 12: 0 GEN5 blocks). `--partial` never accepts a GEN5 file.
13. GEN6 (`scalgen.py p2enc --gen6`, encoder fast path): a file with `GEN6-JSON:` or an encoder kind
    (encHeadKindN / encFieldKindN / encEpiKindN / encFastKindN) is checked by rule 13 only: 13a removed (a git-blob pin); 13b
    structure (one layout def or a pinned hand layout; the exact theorem list, each with its kind; the code constant);
    13c every kind line equals, as whole text, the line rendered from an OWN recomputation (this file's interpreter,
    not the generator) of the fields, the layout and every boundary state from the `.S` and the IR named in GEN6-JSON
    (sha256 checked), and C is bound to that `.S` by `include_x64_rt` in an imported code module; 13d the fast-path
    proof chains every theorem once; 13e the identity `_stmt` names no generated theorem (implication lemma only from
    GEN6_VIA). See the section `rule 13`. `--partial` never accepts a GEN6 file.
    The hand example modules `Gen5Ex*.lean` of the lemma unit are not generator output; they fail rule 12 (no GEN5
    block) and no recorded command runs `kindcheck.py` on them.

Limits (not checked here): GEN4 label strings in `stepLabelKind`, `stepJmpKind` and `callDecSegKindG4` (`lok`) are
phantom kind parameters (they do not occur in the kind body; `stepLabelKind C l j e` is
`stepNopsKind C j e` by `rfl`), so a label name in a kind line is NOT checked by this program or by the `_kind`
line; the label is checked only by the proof's code fact (`he`, `hl`). Also not checked: that the kind parameters (C, indices, displacements, offsets) are the right
ones for the Go type (a wrong one fails the proof's code facts, not this check); name resolution (the
check reads `@Codec.<kind>` as text; an `open` of a namespace that declares another
`Codec.<kind>` would not be seen); that the kind and lemma modules are unchanged (the pins
were removed); that the file builds. A pass is not a non-vacuity witness.
"""
import re
import sys
import pathlib
import tempfile

HERE = pathlib.Path(__file__).resolve().parent
KR = HERE.parent.parent
PRYSM = KR / "lean" / "Prysm"   # rule 6b: the type directories with the generated and example modules
# Rule 11 exemption: hand-written example modules of the lemma units. They have GEN2+
# kinds but are not generator output, so they have no coverage header. Only these exact paths (relative to
# fv/kraken) skip rule 11; every other rule applies to them unchanged.
# `Prysm/SyncCommitteeMessage/DecodeStepExamples.lean` is not listed: it also fails rules 4 and 10c (hand field compositions `*_field` without a kind,
# no FIELDS-JSON line), so an exemption from rule 11 alone would not make it pass; kindcheck is not a check of it.
HAND_EXAMPLES = ("lean/Prysm/DepositMessage/DecodeFieldSegmentExamples.lean", "lean/Prysm/PendingPartialWithdrawal/DecodeCallSegmentExamples.lean")
GENNS = re.compile(r"^Prysm\.\w+\.(?:Decode|Encode)\.(?:generated|example|accept_generated_composition|accept_composed_example)")  # rule 6b: generated and example names
DECL = re.compile(r"^(?:private |protected |noncomputable )*(?:theorem|lemma|def|abbrev) (\S+)")
COMPOSED = ("(Codec.dechead_seg ", "(Codec.decepi_seg ")  # rule 6a
UNCHECKED = "UNCHECKED STATEMENT"  # rule 6c

# GEN2 kinds (`lean/Codec/Kind/FixedBytesDecode.lean`, `lean/Codec/Kind/InlineUint64.lean`)
GEN2_KINDS = ("bytesDecSegKind", "bytesDecSegZKind", "u64DecInlineSegKind")
# GEN3 kinds (`lean/Codec/Kind/CalleeDecode.lean`, `lean/Codec/Kind/DecodeAcceptComposition.lean`)
GEN3_KINDS = ("callDecSegKind", "callArgFirstKind", "callArgReloadKind", "callArgLeaKind", "callArgMovKind",
              "u64DecRRSegKind", "decAcceptKind")
CALLEES = tuple(f'"github.com_OffchainLabs_prysm_v7_consensus_types_primitives.{n}.UnmarshalSSZ"'
                for n in ("Slot", "CommitteeIndex", "ValidatorIndex", "Epoch"))
INT = r"(?:0|[1-9][0-9]*|\(-[1-9][0-9]*\))"  # an Int64 literal as the generator writes it
G4REG = r"Reg64\.(?:rax|rbx|rcx|rdx|rsi|rdi|rsp|rbp|r8|r9|r10|r11|r12|r13|r14|r15)"
G4RY = r"Reg64\.(?:rax|rcx|rdx|rsi|rdi)"
# kind -> (parameter regex after `h `, with {C} for the code constant; namespace of the kind and of its lemma; lemma
# of the proof). The step kinds and the fixed-bytes window kinds are in Codec (`lean/Codec/Kind/WindowSteps.lean`,
# `lean/Codec/Kind/FixedBytesDecodeWindow.lean`, lemma modules `lean/Codec/WindowSteps.lean`,
# `lean/Codec/FixedBytesDecodeWindow*.lean`); the call-block kind is in Codec (`lean/Codec/Kind/CalleeDecode.lean`,
# `lean/Codec/CalleeDecodeWindow.lean`).
GEN4_KINDS = {
    "stepMovRRKind": ("{C} G4REG G4REG NAT NAT", "Codec", "kstep_mov_rr"),
    "stepLdvKind": ("{C} G4REG G4REG INT NAT NAT", "Codec", "kstep_ldv"),
    "stepLdbKind": ("{C} G4REG G4REG INT NAT NAT", "Codec", "kstep_ldb"),
    "stepStKind": ("{C} G4REG G4REG INT NAT NAT", "Codec", "kstep_st"),
    "stepLeaKind": ("{C} G4REG G4REG INT NAT NAT", "Codec", "kstep_lea"),
    "stepAddKind": ("{C} G4REG INT NAT NAT", "Codec", "kstep_add"),
    "stepMovIKind": ("{C} G4REG INT NAT NAT", "Codec", "kstep_movi"),
    "stepJmpKind": ("{C} LBL NAT NAT", "Codec", "kstep_jmp"),
    "stepLabelKind": ("{C} LBL NAT NAT", "Codec", "kstep_label"),
    "stepNopsKind": ("{C} NAT NAT", "Codec", "kstep_nops"),
    "callDecSegKindG4": ("{C} LBL LBL NAT NAT NAT", "Codec", "calldec_seg_w"),
    "bytesDecSegKindWindow": ("SIZE {C} G4RY NAT NAT NAT INT INT INT INT INT INT INT", "Codec", "bytesdec_seg_window"),
    "bytesDecSegZKindWindow": ("SIZE {C} G4RY NAT NAT NAT INT INT INT INT INT INT", "Codec", "bytesdec_seg_z_window"),
}
G4_LEMMAS = {v[2]: v[1] for v in GEN4_KINDS.values()}   # lemma -> namespace
G4_BLOCK = {"callDecSegKindG4": "call", "bytesDecSegKindWindow": "seg", "bytesDecSegZKindWindow": "seg"}
BOOL = r"(?:true|false)"
LBL = r'"[^"\\\s]+"'
RRREG = r"Reg64\.(?:rcx|rdx|rsi|rdi|r8|r9|r10|r11|r12|r13|r15)"
DECF = r"\.(?:bytes (?:32|48|96)|u64)"
COVER = re.compile(r"GEN([234]) coverage \(`p2dec --gen[234]`\): (\d+) of (\d+) fields")
STEM = re.compile(r"^(.*)_(seg|arg|arg1|arg2|call)$")
SIZE = r"(?:32|48|96)"  # the sizes of the hypothesis `hn` of bytesdec_seg / bytesdec_seg_z

PARTIAL = "PARTIAL OUTPUT"  # header of scalgen.py p2dec --partial-out (exit 3)
TOP_OK = re.compile(r"^(import |open |variable |namespace |end\b|set_option \S+ \S+ in$|theorem |/-|--|$|\s)")
BANNED = re.compile(r"\b(sorry|admit|native_decide|bv_decide|axiom)\b")
THM = re.compile(r"^theorem (\S+)")
HK = re.compile(r"\(hk : (\S+)\.IsInfixAt Host\.prog k\)")
NAT = r"(?:0|[1-9][0-9]*)"


def gen_names(lean_dir=PRYSM):
    """Rule 6b: last name components of every declaration in a generated module `<Type>/Generated*.lean` or an example
    module `<Type>/Decode*Example*.lean`."""
    out = set()
    for f in sorted(list(lean_dir.glob("*/Generated*.lean")) + list(lean_dir.glob("*/Decode*Example*.lean"))):
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
    if not (isinstance(unc, list) and all(isinstance(u, dict) and set(u) in ({"field", "reason"},
                                                                         {"field", "reason", "miss_class"}) for u in unc)):
        return "UNCOVERED-JSON is not a list of {field, reason}"
    if not 0 < n < tot or len(unc) != tot - n:
        return f"PARTIAL {n} of {tot} fields with {len(unc)} uncovered entries"
    return n, tot, unc


def strip_comments(s):
    """Rule 9: Lean text without `--` line comments and `/- … -/` block comments (nested)."""
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


def strip_strings(s):
    """Rule 11: Lean text without the contents of string literals ("…", with escapes)."""
    return re.sub(r'"(?:[^"\\]|\\.)*"', '""', s)


def g4_param_rx(spec, C):
    rx = spec.replace("G4REG", G4REG).replace("G4RY", G4RY).replace("INT", INT).replace("NAT", NAT)
    return rx.replace("LBL", LBL).replace("SIZE", SIZE).replace("{C}", C)


def field_stems(mains):
    """Rule 9: {stem: set of suffixes} of the segment theorems (composed theorems excluded by the caller)."""
    st = {}
    for t in mains:
        m = STEM.match(t)
        st.setdefault(m.group(1) if m else t, set()).add(m.group(2) if m else "")
    return st


def check_text(text, gnames=None, partial=False, rule11=True):
    g4kind = {}      # theorem -> GEN4 kind name (rule 10)
    newkind = set()  # theorems with a GEN2 / GEN3 / GEN4 kind (rule 11)
    gnames = gen_names() if gnames is None else gnames
    errs = []
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
        body = strip_strings(strip_comments("\n".join(lines[pos[t]:j])))  # rules 9 / 11: comments, strings do not count
        return all(c in body for c in COMPOSED)

    def type_line(t):
        j = pos[t + "_type"]
        nx = lines[j + 1] if j + 1 < len(lines) else ""
        m = (re.fullmatch(rf"    type_of% \(@{re.escape(t)} h\) = type_of% \(@(Prysm(?:\.\w+)+) h\) := by", nx)
             or re.fullmatch(rf"    type_of% \(@{re.escape(t)} h\) = @(Prysm(?:\.\w+)+) h := by", nx))
        if lines[j] != f"theorem {t}_type : ∀ (h : Host),":
            errs.append(f"{t}_type: header is not `theorem {t}_type : ∀ (h : Host),`")
        elif not m:
            errs.append(f"{t}_type: not an identity `type_of% (@{t} h) = type_of% (@Prysm.… h)` "
                        f"or `= @Prysm.… h`: {nx[:160]}")
        elif m.group(1).rsplit(".", 1)[-1] in names or m.group(1) == t:
            errs.append(f"{t}_type: right-hand side {m.group(1)} is declared in this file (degenerate identity)")
        elif GENNS.match(m.group(1)) or m.group(1).rsplit(".", 1)[-1] in gnames:
            errs.append(f"{t}_type: right-hand side {m.group(1)} is a generated name (`Decode.generated…` or "
                        f"`Decode.example…`, or declared in a generated or example module): a generated theorem cannot vouch for a generated theorem")
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
                            f"Codec.dechead_seg and Codec.decepi_seg): a segment theorem needs its `_kind`")
            elif partial:
                errs.append(f"{t}: composed theorem in a partial file")
            composed.add(t)
            continue
        if not nxt or nxt[0] != t + "_kind":
            errs.append(f"{t}: the next theorem is not {t}_kind")
            continue
        j = pos[t + "_kind"]
        acc = rf"theorem {re.escape(t)}_kind : ∀ \(h : Host\), type_of% \(@{re.escape(t)} h\) = " \
              rf"@Codec\.decAcceptKind h {C} {BOOL} \[{DECF}(?:, {DECF})*\] {NAT} := by"
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
            nx2 = [n for _, n in thms if _ > j]
            if nx2 and nx2[0] == t + "_type":
                type_line(t)
            else:
                # rule 6d: the kind alone is no independent statement check
                errs.append(f"{t}: composed accept theorem without the identity `{t}_type` with an independent hand "
                            f"statement (`--same-as` / `--same-as-prop`): UNCHECKED STATEMENT")
            continue
        g4m = re.fullmatch(rf"theorem {re.escape(t)}_kind : ∀ \(h : Host\), type_of% \(@{re.escape(t)} h\) = "
                           rf"@(Codec)\.(\w+) h (.*) := by", lines[j])
        if g4m and g4m.group(2) in GEN4_KINDS:
            kn = g4m.group(2)
            spec, kns, lem = GEN4_KINDS[kn]
            g4kind[t] = kn
            newkind.add(t)
            if g4m.group(1) != kns or not re.fullmatch(g4_param_rx(spec, C), g4m.group(3)):
                errs.append(f"{t}_kind: header is not a frozen kind: {lines[j][:160]}")
            elif kn == "callDecSegKindG4" and g4m.group(3).split(" ")[1] not in CALLEES:
                errs.append(f"{t}_kind: callee {g4m.group(3).split(' ')[1]} has no proved accept spec (allowed: Slot, "
                            f"CommitteeIndex, ValidatorIndex, Epoch of consensus-types/primitives)")
            # rule 10b: the proof uses the lemma of the kind and no other GEN4 lemma
            proof = strip_strings(strip_comments("\n".join(lines[i:j]).split(":= by", 1)[-1]))
            used = {x for x, xns in G4_LEMMAS.items() if re.search(rf"\b{xns}\.{x}\b", proof)}
            if used != {lem}:
                errs.append(f"{t}: proof uses {sorted(used) or 'no GEN4 lemma'}, its kind {kn} is the statement of {lem}")
            if j + 1 >= len(lines) or lines[j + 1] != "  intro h; with_reducible rfl":
                errs.append(f"{t}_kind: proof line is not `  intro h; with_reducible rfl`")
            continue
        want = (rf"theorem {re.escape(t)}_kind : ∀ \(h : Host\), type_of% \(@{re.escape(t)} h\) = "
                rf"(?:@Codec\.(?:u64DecAcceptKind h {C}|rootDecSegKind h {C}(?: {NAT}){{9}}"
                rf"|rootDecSegZKind h {C}(?: {NAT}){{8}}"
                rf"|bytesDecSegKind h {SIZE} {C}(?: {NAT}){{9}}|bytesDecSegZKind h {SIZE} {C}(?: {NAT}){{8}}"
                rf"|u64DecInlineSegKind h {C}(?: {NAT}){{4}})"
                rf"|@Codec\.(?:callDecSegKind h {C} {LBL} {LBL} {NAT} {NAT}"
                rf"|callArgFirstKind h {C} {BOOL} {INT} {NAT}"
                rf"|callArgReloadKind h {C} {BOOL}(?: {INT}){{6}} {NAT}"
                rf"|callArgLeaKind h {C}(?: {INT}){{6}} {NAT}"
                rf"|callArgMovKind h {C} {NAT}"
                rf"|u64DecRRSegKind h {C} {RRREG}(?: {INT}){{2}} {NAT})) := by")
        if any(f"@Codec.{kn} " in lines[j] for kn in GEN2_KINDS) or any(f"@Codec.{kn} " in lines[j] for kn in GEN3_KINDS):
            newkind.add(t)
        if not re.fullmatch(want, lines[j]):
            errs.append(f"{t}_kind: header is not a frozen kind: {lines[j][:160]}")
        elif "@Codec.callDecSegKind " in lines[j] and lines[j].split(f" h {hk.group(1)} ", 1)[1].split(" ")[0] not in CALLEES:
            errs.append(f"{t}_kind: callee {lines[j].split(f' h {hk.group(1)} ', 1)[1].split(' ')[0]} has no proved "
                        f"accept spec (allowed: Slot, CommitteeIndex, ValidatorIndex, Epoch of consensus-types/primitives)")
        if j + 1 >= len(lines) or lines[j + 1] != "  intro h; with_reducible rfl":
            errs.append(f"{t}_kind: proof line is not `  intro h; with_reducible rfl`")
    # rule 9: the coverage numbers agree with the theorems present
    cov = [COVER.search(l) for l in lines]
    cov = [c for c in cov if c]
    fjs = [l for l in lines if l.startswith("FIELDS-JSON: ")]
    gen4 = bool(g4kind) or bool(fjs) or any(c.group(1) == "4" for c in cov)
    if newkind and not cov and rule11:
        # rule 11: a generated file with GEN2+ kinds keeps its coverage header
        errs.append("no coverage header `GEN2|GEN3|GEN4 coverage (…): n of m fields` in a file with GEN2 / GEN3 / GEN4 "
                    "kinds (a dropped header hides dropped fields)")
    if gen4:
        import json
        stems = {}
        if len(fjs) != 1:
            errs.append(f"GEN4 file: {len(fjs)} `FIELDS-JSON:` lines (expected 1)")
            fl = []
        else:
            try:
                fl = json.loads(fjs[0][len("FIELDS-JSON: "):])
                assert isinstance(fl, list) and all(isinstance(f, dict) and set(f) == {"field", "theorems"}
                                                    and isinstance(f["theorems"], list) for f in fl)
            except (ValueError, AssertionError):
                errs.append("GEN4 file: FIELDS-JSON is not a list of {field, theorems}")
                fl = []
        listed = [x for f in fl for x in f["theorems"]]
        if len(set(listed)) != len(listed):
            errs.append("GEN4 file: a theorem is listed in two fields of FIELDS-JSON")
        for x in listed:
            if x not in mains:
                errs.append(f"GEN4 file: FIELDS-JSON lists {x}, not a theorem of the file")
        for x in mains:
            if x not in composed and x not in listed:
                errs.append(f"GEN4 file: theorem {x} is in no field of FIELDS-JSON")
        if any(x not in g4kind for x in listed if x in mains):
            errs.append("GEN4 file: a listed theorem has no GEN4 kind")
        for f in fl:
            blocks = [x for x in f["theorems"] if g4kind.get(x) in G4_BLOCK]
            if len(blocks) > 1:
                errs.append(f"GEN4 field {f['field']}: {len(blocks)} block theorems (at most 1)")
            for x in blocks:
                if not x.endswith(f"_{f['field']}_{G4_BLOCK[g4kind[x]]}"):
                    errs.append(f"GEN4 field {f['field']}: block theorem {x} is not `<prefix>_{f['field']}_"
                                f"{G4_BLOCK[g4kind[x]]}`")
            if not f["theorems"]:
                errs.append(f"GEN4 field {f['field']}: no theorem")
            stems[f["field"]] = {"g4"}
    else:
        stems = field_stems([t for t in mains if t not in composed])
    for s, sx in ({} if gen4 else stems).items():
        if "call" in sx and not ("arg" in sx or {"arg1", "arg2"} <= sx):
            errs.append(f"{s}: call-block theorem without its argument set-up theorem(s)")
        if sx & {"arg", "arg1", "arg2"} and "call" not in sx:
            errs.append(f"{s}: argument set-up theorem(s) without the call-block theorem")
        if sx & {"seg"} and sx & {"arg", "arg1", "arg2", "call"}:
            errs.append(f"{s}: segment and call-field theorems for one field")
    if len(cov) > 1:
        errs.append(f"{len(cov)} coverage headers (expected at most 1)")
    elif cov:
        cn, cm = int(cov[0].group(2)), int(cov[0].group(3))
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
    gn = gen_names()
    bad = 0
    for f in files:
        text = pathlib.Path(f).read_text().replace("\ntheorem _root_.", "\ntheorem ")
        hand = pathlib.Path(f).resolve() in {(KR / x).resolve() for x in HAND_EXAMPLES}
        g5 = G5_MARK in text or "GEN5-JSON" in text or any(f"@Codec.{k} " in text for k in (
            "decHeadKindN", "decFieldKindN", "decEpiKindN", "decAcceptKindN", "decRejectKindN"))
        g6 = "GEN6-JSON" in text or any(f"@Codec.{k} " in text for k in GEN6_KINDS)
        if g6 and not partial:
            # rule 13: a GEN6 file is checked by rule 13 only; a GEN5 / older kind in it fails 13c
            errs, info6 = check_gen6(text, gn)
            if g5:
                errs.append("rule 13: a GEN6 file with a GEN5 kind or block")
            mains = [info6]
        elif g6:
            errs, mains = ["GEN6 output in --partial mode (a GEN6 file is never partial)"], []
        elif g5 and not partial:
            # rule 12: the GEN4 part by rules 1-11, the GEN5 part by rule 12
            part4 = text.split(G5_MARK, 1)[0] if text.count(G5_MARK) == 1 else text
            errs, mains = check_text(part4, gn, partial, rule11=not hand)
            e5, info5 = check_gen5(text, gn)
            errs = errs + e5
            mains = mains + [info5]
        elif g5:
            errs, mains = ["GEN5 output in --partial mode (a GEN5 file is never partial)"], []
        else:
            errs, mains = check_text(text, gn, partial, rule11=not hand)
        print(("PASS" if not errs else "FAIL"), f, "theorems:", ",".join(mains))
        if hand:
            print("   hand example module (HAND_EXAMPLES): rule 11 not applied")
        for e in errs:
            print("  ", e)
        if partial and not errs:
            n, tot, unc = partial_header(text.split("\n"))
            print(f"PARTIAL {n}/{tot} fields: kinds of present theorems checked; NOT a full-coverage result "
                  f"(uncovered: {', '.join(u['field'] for u in unc)})")
        bad |= bool(errs)
    if partial:
        return 1 if bad else 3
    return 1 if bad else 0


GOOD = """import Codec.Uint64Decoder
import Codec.Kind.FieldPatterns

/-! generated -/

open Machine Runtime Prysm.AttestationData.Code
variable [Host]

open Codec
namespace Prysm.Fixture

set_option maxRecDepth 100000 in
theorem t (k : Nat) (hk : VxUnmarshal.IsInfixAt Host.prog k)
    (hf : LabelsFresh VxUnmarshal k) : P := by
  with_reducible exact foo
theorem t_kind : ∀ (h : Host), type_of% (@t h) = @Codec.u64DecAcceptKind h VxUnmarshal := by
  intro h; with_reducible rfl

/-- doc -/
theorem s (k : Nat) (hk : Prysm.BeaconBlockHeader.Code.unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh Prysm.BeaconBlockHeader.Code.unmarshalSSZ k) :
    Q := by
  exact bar
theorem s_kind : ∀ (h : Host), type_of% (@s h) = @Codec.rootDecSegKind h Prysm.BeaconBlockHeader.Code.unmarshalSSZ 86 100 128 136 104 24 32 40 16 := by
  intro h; with_reducible rfl

theorem z (k : Nat) (hk : Prysm.Eth1Data.Code.unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh Prysm.Eth1Data.Code.unmarshalSSZ k) :
    Z := by
  with_reducible exact baz
theorem z_kind : ∀ (h : Host), type_of% (@z h) = @Codec.rootDecSegZKind h Prysm.Eth1Data.Code.unmarshalSSZ 13 26 48 56 24 8 16 24 := by
  intro h; with_reducible rfl

theorem t_same : @E2eAd.x = @t := rfl

end Prysm.Fixture
"""


def selftest():
    deg = GOOD.replace("= @Codec.u64DecAcceptKind h VxUnmarshal := by", "= type_of% (@t h) := by")
    cases = [
        ("good", GOOD, True),
        ("degenerate_rhs_self", deg, False),
        ("degenerate_rhs_true", GOOD.replace("= @Codec.u64DecAcceptKind h VxUnmarshal := by", "= True := by"), False),
        ("other_kind_const", GOOD.replace("u64DecAcceptKind h VxUnmarshal", "u64DecAcceptKind h Prysm.AttestationData.Code.committeeIndexUnmarshalSSZ"), False),
        ("eight_params", GOOD.replace(" 128 136 104 24 32 40 16", " 128 136 104 24 32 40"), False),
        ("missing_kind", GOOD.replace("theorem t_kind", "theorem t_kinx"), False),
        ("kind_not_next", GOOD.replace("theorem t_kind :", "theorem zz (hk : VxUnmarshal.IsInfixAt Host.prog k) : True := trivial\ntheorem t_kind :"), False),
        ("proof_not_rfl", GOOD.replace("intro h; with_reducible rfl\n\n/--", "intro h; simp\n\n/--"), False),
        ("local_abbrev", GOOD.replace("namespace Prysm.Fixture\n", "namespace Prysm.Fixture\nabbrev Codec.u64DecAcceptKind := True\n"), False),
        ("sorry", GOOD.replace("with_reducible exact foo", "sorry"), False),
        ("kind_other_namespace", GOOD.replace("@Codec.u64DecAcceptKind", "@Prysm.Fixture.u64DecAcceptKind"), False),
        ("same_not_identity", GOOD.replace("@E2eAd.x = @t := rfl", "True := trivial"), False),
        ("orphan_kind", GOOD + "theorem q_kind : True := trivial\n", False),
    ]
    # offset-0 kind of the generator extension (rootDecSegZKind, 8 parameters)
    zk = "= @Codec.rootDecSegZKind h Prysm.Eth1Data.Code.unmarshalSSZ 13 26 48 56 24 8 16 24 := by"
    assert zk in GOOD
    cases = cases + [
        ("z_degenerate_rhs_self", GOOD.replace(zk, "= type_of% (@z h) := by"), False),
        ("z_degenerate_rhs_true", GOOD.replace(zk, "= True := by"), False),
        ("z_nine_params", GOOD.replace(zk, zk.replace(" 16 24 :=", " 16 24 0 :=")), False),
        ("z_seven_params", GOOD.replace(zk, zk.replace(" 16 24 :=", " 16 :=")), False),
        ("z_other_const", GOOD.replace(zk, zk.replace("Prysm.Eth1Data.Code.unmarshalSSZ", "Prysm.BeaconBlockHeader.Code.unmarshalSSZ")), False),
        ("z_as_add_kind", GOOD.replace(zk, zk.replace("rootDecSegZKind", "rootDecSegKind")), False),
        # a --partial-out file (header text as scalgen.py writes it) must fail, even if
        # every theorem it has is well kinded
        ("partial_output_header", GOOD.replace("/-! generated -/", "/-! PARTIAL OUTPUT (scalgen exit 3): 1 of 2 "
                                               "32-byte fields of `v1alpha1.Eth1Data`; missing: BlockHash -/"), False),
        ("partial_output_in_line_comment", GOOD + "-- PARTIAL OUTPUT\n", False),
    ]
    cases = [c + (False,) for c in cases] + gen2_cases() + g2f_cases() + g3_cases() + g4_cases()
    bad = []
    for name, text, ok, part in cases:
        errs, _ = check_text(text, GNAMES, part)
        if (not errs) != ok:
            bad.append((name, errs))
    # the exit codes of main() (`--partial`: 3 on success, 1 on failure, never 0; default: 1)
    n_exit, bad_exit = s4_exit_cases()
    bad += bad_exit
    # the rule 11 exemption removes only the coverage-header error
    nh = GOOD2.replace("GEN2 coverage (`p2dec --gen2`): 3 of 3 fields", "generated")
    e_on, _ = check_text(nh, GNAMES, False)
    e_off, _ = check_text(nh, GNAMES, False, rule11=False)
    e_sorry, _ = check_text(nh.replace("with_reducible exact", "sorry --", 1), GNAMES, False, rule11=False)
    n_exit += 3
    if not e_on or e_off or not e_sorry:
        bad.append(("g4f_rule11_exemption", e_on, e_off, e_sorry))
    # rule 12
    n5, bad5 = g5_selftest()
    n_exit += n5
    bad += bad5
    # rule 13
    n6, bad6 = g6_selftest()
    n_exit += n6
    bad += bad6
    print("selftest", "PASS" if not bad else f"FAIL {bad}", f"({len(cases)} cases + {n_exit} exit-code / rule-12 / rule-13 cases)")
    return 1 if bad else 0


# GEN2 controls: one generated-shape block per new kind (headers as `scalgen.py p2dec --gen2` writes them)
GOOD2 = """import Codec.FixedBytesDecode
import Codec.Kind.FieldPatterns
import Codec.Kind.FixedBytesDecode
import Codec.Kind.InlineUint64

/-! Generated by `gen/scal/scalgen.py p2dec`; GEN2 coverage (`p2dec --gen2`): 3 of 3 fields. -/

open Machine Runtime Prysm.BlobIdentifier.Code
variable [Host]

open Codec
namespace Prysm.Fixture

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
/-- `PublicKey` (48 bytes, SSZ offset 0, Go offset 0): decode segment, directives 13–36. -/
theorem a (k : Nat) (hk : Prysm.DepositMessage.Code.unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh Prysm.DepositMessage.Code.unmarshalSSZ k) :
    A := by
  with_reducible exact Codec.bytesdec_seg_z 48 (Or.inr (Or.inl rfl)) _ _ _ _ _ _ _ _ (k + 13) (k + 26) hA hB hl
theorem a_kind : ∀ (h : Host), type_of% (@a h) = @Codec.bytesDecSegZKind h 48 Prysm.DepositMessage.Code.unmarshalSSZ 13 26 48 56 24 0 8 16 := by
  intro h; with_reducible rfl

theorem b (k : Nat) (hk : XyUnmarshal.IsInfixAt Host.prog k) (hf : LabelsFresh XyUnmarshal k) :
    B := by
  with_reducible exact Codec.bytesdec_seg 96 (Or.inr (Or.inr rfl)) _ _ _ _ _ _ _ _ _ (k + 47) (k + 61) hA hB hl
theorem b_kind : ∀ (h : Host), type_of% (@b h) = @Codec.bytesDecSegKind h 96 XyUnmarshal 47 61 48 56 24 24 32 40 48 := by
  intro h; with_reducible rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem c (k : Nat) (hk : Prysm.DepositMessage.Code.unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh Prysm.DepositMessage.Code.unmarshalSSZ k) :
    C := by
  have hX : Codec.U64InlineReg Reg64.rcx := by decide
  with_reducible exact Codec.u64dec_inline_seg Reg64.rcx hX _ _ _ (k + 83) hA
theorem c_kind : ∀ (h : Host), type_of% (@c h) = @Codec.u64DecInlineSegKind h Prysm.DepositMessage.Code.unmarshalSSZ 83 56 80 48 := by
  intro h; with_reducible rfl

end Prysm.Fixture
"""


COMP = """import Codec.DecoderHeadEpilogue
import Codec.Kind.FieldPatterns

/-! Generated by `gen/scal/scalgen.py p2dec`; composed accept theorem; statement check: identity. -/

open Machine Runtime Prysm.BlobIdentifier.Code
variable [Host]

open Codec
namespace Prysm.Fixture

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem d (k : Nat) (hk : Prysm.DepositMessage.Code.unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh Prysm.DepositMessage.Code.unmarshalSSZ k)
    (x1 : List UInt8) :
    D := by
  refine eventually_trans _ _ _ _ (Codec.dechead_seg _ _ _ _ 88 (k + 0) hH) ?_
  refine eventually_trans _ _ _ _ (Prysm.DepositMessage.Decode.generated_field_Amount_seg k hk hf) ?_
  refine eventually_trans _ _ _ _ (Codec.decepi_seg (k + 86) hE) ?_

/-- Statement check: the declared type is that of the hand theorem (definitional identity). -/
theorem d_type : ∀ (h : Host),
    type_of% (@d h) = type_of% (@Prysm.DepositMessage.Decode.accept h) := by
  intro h; with_reducible rfl

end Prysm.Fixture
"""


def gen2_cases():
    za = "= @Codec.bytesDecSegZKind h 48 Prysm.DepositMessage.Code.unmarshalSSZ 13 26 48 56 24 0 8 16 := by"
    ab = "= @Codec.bytesDecSegKind h 96 XyUnmarshal 47 61 48 56 24 24 32 40 48 := by"
    uc = "= @Codec.u64DecInlineSegKind h Prysm.DepositMessage.Code.unmarshalSSZ 83 56 80 48 := by"
    for x in (za, ab, uc):
        assert GOOD2.count(x) == 1
    return [
        ("g2_good", GOOD2, True, False),
        ("g2_z_degenerate_self", GOOD2.replace(za, "= type_of% (@a h) := by"), False, False),
        ("g2_z_degenerate_true", GOOD2.replace(za, "= True := by"), False, False),
        ("g2_add_degenerate_self", GOOD2.replace(ab, "= type_of% (@b h) := by"), False, False),
        ("g2_u64_degenerate_self", GOOD2.replace(uc, "= type_of% (@c h) := by"), False, False),
        ("g2_u64_degenerate_true", GOOD2.replace(uc, "= True := by"), False, False),
        ("g2_z_size_64", GOOD2.replace(za, za.replace(" h 48 ", " h 64 ")), False, False),
        ("g2_add_size_symbolic", GOOD2.replace(ab, ab.replace(" h 96 ", " h n ")), False, False),
        ("g2_z_size_missing", GOOD2.replace(za, za.replace(" h 48 ", " h ")), False, False),
        ("g2_add_nine_params", GOOD2.replace(ab, ab.replace(" 40 48 :=", " 40 :=")), False, False),
        ("g2_z_nine_params", GOOD2.replace(za, za.replace(" 8 16 :=", " 8 16 0 :=")), False, False),
        ("g2_u64_three_params", GOOD2.replace(uc, uc.replace(" 80 48 :=", " 80 :=")), False, False),
        ("g2_u64_register_param", GOOD2.replace(uc, uc.replace(" h Prysm.DepositMessage.Code.unmarshalSSZ", " h Reg64.rcx Prysm.DepositMessage.Code.unmarshalSSZ")), False, False),
        ("g2_u64_other_const", GOOD2.replace(uc, uc.replace("Prysm.DepositMessage.Code.unmarshalSSZ", "Prysm.BlobIdentifier.Code.unmarshalSSZ")), False, False),
        ("g2_add_as_z_kind", GOOD2.replace(ab, ab.replace("bytesDecSegKind", "bytesDecSegZKind")), False, False),
        ("g2_partial_output", GOOD2.replace("/-! Generated", "/-! PARTIAL OUTPUT (scalgen exit 3): 2 of 3 fields "
                                            "of `v1alpha1.DepositMessage` (--gen2); NOT generated: Amount. -/\n/-! Generated"), False, False),
        ("g2_proof_not_rfl", GOOD2.replace(uc + "\n  intro h; with_reducible rfl", uc + "\n  intro h; rfl"), False, False),
        ("g2c_good_identity", COMP, True, False),
        ("g2c_no_identity", COMP.split("\n/-- Statement check")[0] + "\nend Prysm.Fixture\n", False, False),
        ("g2c_degenerate_self", COMP.replace("type_of% (@Prysm.DepositMessage.Decode.accept h)", "type_of% (@d h)"), False, False),
        ("g2c_rhs_declared_here", COMP.replace("@Prysm.DepositMessage.Decode.accept h", "@Prysm.Fixture.d h"), False, False),
        ("g2c_rhs_true", COMP.replace("type_of% (@Prysm.DepositMessage.Decode.accept h) := by", "True := by"), False, False),
        ("g2c_proof_not_rfl", COMP.replace("  intro h; with_reducible rfl", "  intro h; rfl"), False, False),
        ("g2c_orphan_type", GOOD2 + "theorem q_type : ∀ (h : Host),\n    type_of% (@q h) = type_of% (@Prysm.X h) := by\n"
                                     "  intro h; with_reducible rfl\n", False, False),
    ]


# rule 6b in the selftest: a fixed set of "generated" names instead of the tree's Gen*.lean (the controls do
# not depend on the tree); `gen_seg_x` stands for a theorem of another generated module
GNAMES = {"gen_seg_x", "accept_generated_composition", "accept_composed_example"}


def g2f_cases():
    """Controls of rules 6a-6c and 7."""
    ty = ("theorem {t}_type : ∀ (h : Host),\n    type_of% (@{t} h) = type_of% (@Prysm.DepositMessage.Decode.accept h) := by\n"
          "  intro h; with_reducible rfl\n")
    uc = "theorem c_kind : ∀ (h : Host), type_of% (@c h) = @Codec.u64DecInlineSegKind h Prysm.DepositMessage.Code.unmarshalSSZ 83 56 80 48 := by\n  intro h; with_reducible rfl\n"
    assert GOOD2.count(uc) == 1
    seg_type = GOOD2.replace(uc, ty.format(t="c"))           # reviewer case (i): `_type` in place of a segment kind
    rhs = "type_of% (@Prysm.DepositMessage.Decode.accept h)"
    assert COMP.count(rhs) == 1
    gen_rhs = COMP.replace(rhs, "type_of% (@Prysm.BlobIdentifier.Decode.accept_generated_composition h)")  # reviewer case (ii)
    prop = COMP.replace(rhs, "@Prysm.DepositMessage.Decode.hand_statement h")
    unc = json_line([("Slot", "delegated overlay field"), ("ProposerIndex", "delegated overlay field")])
    PH = ("/-! PARTIAL OUTPUT (scalgen exit 3): 3 of 5 fields of `v1alpha1.BeaconBlockHeader` (--gen2); NOT "
          "generated: Slot, ProposerIndex. Not a complete p2dec output.\n" + unc + "\n-/\n")
    part = GOOD2.replace("\n/-! Generated", "\n" + PH + "/-! Generated").replace(" 3 of 3 fields", " 3 of 5 fields")
    assert part.count(PARTIAL) == 1
    return [
        ("g2f_segment_type_instead_of_kind", seg_type, False, False),
        ("g2f_rhs_generated_namespace", gen_rhs, False, False),
        ("g2f_rhs_gen2ex_namespace", COMP.replace(rhs, "type_of% (@Prysm.BlobIdentifier.Decode.accept_composed_example h)"), False, False),
        ("g2f_rhs_generated_namespace_fresh_name", COMP.replace(rhs, "type_of% (@Prysm.DepositMessage.Decode.generated_zz_fresh h)"), False, False),
        ("g2f_unchecked_marker_with_identity", COMP.replace(
            "(hf : LabelsFresh Prysm.DepositMessage.Code.unmarshalSSZ k)\n", "(hf : LabelsFresh Prysm.DepositMessage.Code.unmarshalSSZ k) -- UNCHECKED STATEMENT\n"), False, False),
        ("g2f_rhs_declared_in_gen_module", COMP.replace(rhs, "type_of% (@Prysm.Other.gen_seg_x h)"), False, False),
        ("g2f_composed_without_decepi", COMP.replace("Codec.decepi_seg", "Codec.decepi_sex"), False, False),
        ("g2f_prop_identity_good", prop, True, False),
        ("g2f_prop_identity_generated_rhs", COMP.replace(rhs, "@Prysm.BlobIdentifier.Decode.accept_generated_composition h"), False, False),
        ("g2f_prop_identity_on_segment", GOOD2.replace(uc, ty.format(t="c").replace(rhs, "@Prysm.DepositMessage.Decode.hand_statement h")), False, False),
        ("g2f_unchecked_marker", COMP.split("\n/-- Statement check")[0].replace(
            "(hf : LabelsFresh Prysm.DepositMessage.Code.unmarshalSSZ k)\n", "(hf : LabelsFresh Prysm.DepositMessage.Code.unmarshalSSZ k) -- UNCHECKED STATEMENT\n")
         + "\nend Prysm.Fixture\n", False, False),
        ("g2f_partial_default_rejects", part, False, False),
        ("g2f_partial_mode_good", part, True, True),
        ("g2f_partial_mode_complete_file", GOOD2, False, True),
        ("g2f_partial_mode_header_before_imports", PH + GOOD2.replace(" 3 of 3 fields", " 3 of 5 fields"), False, True),
        ("g2f_partial_mode_count_mismatch", part.replace(unc, json_line([("Slot", "x")])), False, True),
        ("g2f_partial_mode_bad_kind", part.replace(" 83 56 80 48 := by", " 83 56 80 := by"), False, True),
        ("g2f_partial_mode_composed", COMP.replace("\n/-! Generated", "\n" + PH + "/-! Generated"), False, True),
    ]


# GEN3 controls: generated-shape blocks with the kind lines as `scalgen.py p2dec --gen3` writes them
FN_VI = '"github.com_OffchainLabs_prysm_v7_consensus_types_primitives.ValidatorIndex.UnmarshalSSZ"'
FN_EP = '"github.com_OffchainLabs_prysm_v7_consensus_types_primitives.Epoch.UnmarshalSSZ"'
G3K = {
    "pw_Index_arg": "@Codec.callArgFirstKind h Prysm.PendingPartialWithdrawal.Code.unmarshalSSZ false 8 15",
    "pw_Index_call": f'@Codec.callDecSegKind h Prysm.PendingPartialWithdrawal.Code.unmarshalSSZ {FN_VI} "L_pw_b9" 17 47',
    "pw_Amount_seg": "@Codec.u64DecRRSegKind h Prysm.PendingPartialWithdrawal.Code.unmarshalSSZ Reg64.r8 8 16 54",
    "pw_WithdrawableEpoch_arg1": "@Codec.callArgLeaKind h Prysm.PendingPartialWithdrawal.Code.unmarshalSSZ 96 16 112 (-16) 88 24 48",
    "pw_WithdrawableEpoch_arg2": "@Codec.callArgMovKind h Prysm.PendingPartialWithdrawal.Code.unmarshalSSZ 56",
    "pw_WithdrawableEpoch_call": f'@Codec.callDecSegKind h Prysm.PendingPartialWithdrawal.Code.unmarshalSSZ {FN_EP} "L_pw_159" 59 88',
    "bh_ProposerIndex_arg": "@Codec.callArgReloadKind h Prysm.PendingPartialWithdrawal.Code.unmarshalSSZ true 120 8 136 (-8) 112 16 47",
    "bh_ProposerIndex_call": f'@Codec.callDecSegKind h Prysm.PendingPartialWithdrawal.Code.unmarshalSSZ {FN_VI} "L_bh_154" 55 85',
    "dd_WithdrawalCredentials_seg": "@Codec.bytesDecSegKind h 32 Prysm.PendingPartialWithdrawal.Code.unmarshalSSZ 47 61 48 56 24 32 40 48 48",
}
G3PROOF = {"pw_Amount_seg": "  have hX : Codec.U64RRReg Reg64.r8 := by decide\n  with_reducible exact Codec.u64dec_rr_seg Reg64.r8 hX _ _ (k + 54) hA\n",
           "dd_WithdrawalCredentials_seg": "  with_reducible exact Codec.bytesdec_seg_p true 32 (Or.inl rfl) _ _ _ _ _ _ _ _ _ (k + 47) (k + 61) hA hB hl\n"}


def g3_block(t, kind):
    return ("set_option maxHeartbeats 4000000 in\nset_option maxRecDepth 100000 in\n"
            f"theorem {t} (k : Nat) (hk : Prysm.PendingPartialWithdrawal.Code.unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh Prysm.PendingPartialWithdrawal.Code.unmarshalSSZ k) :\n"
            f"    T := by\n" + G3PROOF.get(t, "  with_reducible exact foo\n")
            + f"theorem {t}_kind : ∀ (h : Host), type_of% (@{t} h) = {kind} := by\n  intro h; with_reducible rfl\n\n")


GOOD3 = ("import Codec.Kind.CalleeDecode\nimport Codec.FixedBytesDecodePadding\nimport Codec.Kind.FieldPatterns\nimport Codec.Kind.FixedBytesDecode\n\n"
         "/-! Generated by `gen/scal/scalgen.py p2dec`; GEN3 coverage (`p2dec --gen3`): 5 of 5 fields. -/\n\n"
         "open Machine Runtime Prysm.Deposit_Data.Code\nvariable [Host]\n\nopen Codec\nnamespace Prysm.Fixture\n\n"
         + "".join(g3_block(t, k) for t, k in G3K.items()) + "end Prysm.Fixture\n")

COMP3 = COMP.replace("composed accept theorem; statement check: identity", "composed accept theorem (`p2dec --gen3 --compose`)").replace(
    "\n/-- Statement check: the declared type is that of the hand theorem",
    "\n-- Statement check: kind.\nset_option maxHeartbeats 200000 in\n"
    "theorem d_kind : ∀ (h : Host), type_of% (@d h) = @Codec.decAcceptKind h Prysm.DepositMessage.Code.unmarshalSSZ false [.bytes 48, .bytes 32, .u64] 68 := by\n"
    "  intro h; rfl\n\n/-- Statement check: the declared type is that of the hand theorem")


def g3_cases():
    """Controls of rule 8 (GEN3 kinds, callee list, decAcceptKind) and rule 9."""

    def kchg(t, new):
        old = f"type_of% (@{t} h) = {G3K[t]} := by"
        assert GOOD3.count(old) == 1, t
        return GOOD3.replace(old, f"type_of% (@{t} h) = {new} := by")

    def drop(text, t):
        b = g3_block(t, G3K[t])
        assert text.count(b) == 1
        return text.replace(b, "")
    comp_kind = "@Codec.decAcceptKind h Prysm.DepositMessage.Code.unmarshalSSZ false [.bytes 48, .bytes 32, .u64] 68 := by"
    assert COMP3.count(comp_kind) == 1
    comp_only = COMP3.split("\n/-- Statement check: the declared type")[0] + "\nend Prysm.Fixture\n"
    # k04: `_type` in place of a segment `_kind`, the two composed lemma names only in a comment
    uc = "theorem c_kind : ∀ (h : Host), type_of% (@c h) = @Codec.u64DecInlineSegKind h Prysm.DepositMessage.Code.unmarshalSSZ 83 56 80 48 := by\n  intro h; with_reducible rfl\n"
    ty = ("theorem c_type : ∀ (h : Host),\n    type_of% (@c h) = type_of% (@Prysm.DepositMessage.Decode.accept h) := by\n"
          "  intro h; with_reducible rfl\n")
    k04 = GOOD2.replace(uc, ty).replace("  with_reducible exact Codec.u64dec_inline_seg Reg64.rcx hX _ _ _ (k + 83) hA\n",
                                        "  -- (Codec.dechead_seg x) (Codec.decepi_seg y)\n"
                                        "  with_reducible exact Codec.u64dec_inline_seg Reg64.rcx hX _ _ _ (k + 83) hA\n")
    k04b = k04.replace("  -- (Codec.dechead_seg x) (Codec.decepi_seg y)\n", "  /- (Codec.dechead_seg x) (Codec.decepi_seg y) -/\n")
    # k22-k24 (partial / coverage counts)
    unc = json_line([("Slot", "delegated overlay field"), ("ProposerIndex", "delegated overlay field")])
    PH = ("/-! PARTIAL OUTPUT (scalgen exit 3): 3 of 5 fields of `v1alpha1.BeaconBlockHeader` (--gen2); NOT "
          "generated: Slot, ProposerIndex. Not a complete p2dec output.\n" + unc + "\n-/\n")
    part = GOOD2.replace("\n/-! Generated", "\n" + PH + "/-! Generated").replace(" 3 of 3 fields", " 3 of 5 fields")
    k22 = part.split("set_option maxHeartbeats 4000000")[0] + "end Prysm.Fixture\n"
    k24 = GOOD2.replace(" 3 of 3 fields", " 3 of 5 fields")
    unc1 = json_line([("ProposerIndex", "x")])
    nm = part.replace("3 of 5 fields of", "3 of 3 fields of").replace(unc, "UNCOVERED-JSON: []")
    n0 = part.replace("3 of 5 fields of", "0 of 5 fields of")
    unc_has_thm = part.replace(unc, json_line([("c", "x"), ("Slot", "y")]))
    return [
        ("g3_good", GOOD3, True, False),
        ("g3_callee_without_spec", kchg("pw_Index_call", G3K["pw_Index_call"].replace(
            "consensus_types_primitives.ValidatorIndex", "proto_prysm_v1alpha1.Checkpoint")), False, False),
        ("g3_call_degenerate_self", kchg("pw_Index_call", "type_of% (@pw_Index_call h)"), False, False),
        ("g3_call_degenerate_true", kchg("pw_Index_call", "True"), False, False),
        ("g3_call_one_index", kchg("pw_Index_call", G3K["pw_Index_call"].replace(" 17 47", " 17")), False, False),
        ("g3_first_pad_not_bool", kchg("pw_Index_arg", G3K["pw_Index_arg"].replace(" false ", " 1 ")), False, False),
        ("g3_first_negative_index", kchg("pw_Index_arg", G3K["pw_Index_arg"].replace(" 15", " (-15)")), False, False),
        ("g3_reload_five_ints", kchg("bh_ProposerIndex_arg", G3K["bh_ProposerIndex_arg"].replace(" (-8)", "")), False, False),
        ("g3_lea_seven_ints", kchg("pw_WithdrawableEpoch_arg1", G3K["pw_WithdrawableEpoch_arg1"].replace(" 24 48", " 24 0 48")), False, False),
        ("g3_mov_extra_param", kchg("pw_WithdrawableEpoch_arg2", G3K["pw_WithdrawableEpoch_arg2"] + " 0"), False, False),
        ("g3_rr_register_rax", kchg("pw_Amount_seg", G3K["pw_Amount_seg"].replace("Reg64.r8", "Reg64.rax")), False, False),
        ("g3_rr_register_missing", kchg("pw_Amount_seg", G3K["pw_Amount_seg"].replace("Reg64.r8 ", "")), False, False),
        ("g3_rr_as_inline_kind", kchg("pw_Amount_seg", "@Codec.u64DecInlineSegKind h Prysm.PendingPartialWithdrawal.Code.unmarshalSSZ 54 8 8 16"), True, False),
        ("g3_call_without_arg", drop(GOOD3, "pw_Index_arg"), False, False),
        ("g3_lea_without_arg2", drop(GOOD3, "pw_WithdrawableEpoch_arg2"), False, False),
        ("g3_arg_without_call", drop(GOOD3, "pw_Index_call"), False, False),
        ("g3_decaccept_on_segment", kchg("pw_Amount_seg", "@Codec.decAcceptKind h Prysm.PendingPartialWithdrawal.Code.unmarshalSSZ true [.u64] 54"), False, False),
        ("g3c_good_kind_and_identity", COMP3, True, False),
        # rule 6d: the kind alone is no independent statement check
        ("g3c_kind_only_rejected", comp_only, False, False),
        ("g3c_heartbeats_raised", COMP3.replace("set_option maxHeartbeats 200000 in\ntheorem d_kind", "set_option maxHeartbeats 2000000 in\ntheorem d_kind"), False, False),
        ("g3c_no_heartbeat_line", COMP3.replace("set_option maxHeartbeats 200000 in\ntheorem d_kind", "theorem d_kind"), False, False),
        ("g3c_with_reducible", COMP3.replace("  intro h; rfl\n", "  intro h; with_reducible rfl\n"), False, False),
        ("g3c_field_size_64", COMP3.replace(comp_kind, comp_kind.replace(".bytes 48", ".bytes 64")), False, False),
        ("g3c_empty_fields", COMP3.replace(comp_kind, comp_kind.replace("[.bytes 48, .bytes 32, .u64]", "[]")), False, False),
        ("g3c_st_not_bool", COMP3.replace(comp_kind, comp_kind.replace(" false [", " 0 [")), False, False),
        ("g3c_other_const", COMP3.replace(comp_kind, comp_kind.replace("Prysm.DepositMessage.Code.unmarshalSSZ", "Prysm.BlobIdentifier.Code.unmarshalSSZ")), False, False),
        ("g3c_not_composed_comment_only", comp_only.replace("(Codec.decepi_seg (k + 86) hE)", "foo -- (Codec.decepi_seg "), False, False),
        ("s1_k04_line_comment", k04, False, False),
        ("s1_k04_block_comment", k04b, False, False),
        # the two composed-lemma names in a string literal do not make a composed theorem
        ("s2_n26b_string_literal", k04.replace("  -- (Codec.dechead_seg x) (Codec.decepi_seg y)\n",
                                               '  have s := "(Codec.dechead_seg x) (Codec.decepi_seg y)"\n')
         .replace(" 3 of 3 fields", " 2 of 2 fields"), False, False),
        # rule 6d with the generator's new marker (`--gen3 --compose` without `--same-as*`)
        ("g3c_kind_only_marked", comp_only.replace("(hf : LabelsFresh Prysm.DepositMessage.Code.unmarshalSSZ k)\n",
                                                   "(hf : LabelsFresh Prysm.DepositMessage.Code.unmarshalSSZ k) -- UNCHECKED STATEMENT\n"), False, False),
        ("s2_k22_theorem_removed_partial", k22, False, True),
        ("s2_k23_uncovered_entry_dropped", part.replace("3 of 5 fields of", "4 of 5 fields of").replace(unc, unc1), False, True),
        ("s2_uncovered_field_has_theorem", unc_has_thm, False, True),
        ("s3_k24_partial_block_deleted", k24, False, False),
        ("s3_header_count_mismatch_full", GOOD2.replace(" 3 of 3 fields", " 4 of 4 fields"), False, False),
        ("s4_partial_n_equals_m", nm, False, True),
        ("s4_partial_n_zero", n0, False, True),
        ("s4_partial_good_0_lt_n_lt_m", part, True, True),
    ]


# GEN4 controls: kind lines and proof lemma as `scalgen.py p2dec --gen4` writes them
G4K = {
    "Prysm.PendingPartialWithdrawal.Decode.generated_step_s50": ("@Codec.stepLdbKind h Prysm.PendingPartialWithdrawal.Code.unmarshalSSZ Reg64.r8 Reg64.rbx 8 50 51", "kstep_ldb Reg64.r8 Reg64.rbx 8 _ (k + 50) (k + 51) hq he hend"),
    "Prysm.PendingPartialWithdrawal.Decode.generated_step_s51": ("@Codec.stepStKind h Prysm.PendingPartialWithdrawal.Code.unmarshalSSZ Reg64.r8 Reg64.rax 16 51 52", "kstep_st Reg64.r8 Reg64.rax 16 _ (k + 51) (k + 52) hq he hend"),
    "Prysm.PendingPartialWithdrawal.Decode.generated_step_s52": ("@Codec.stepAddKind h Prysm.PendingPartialWithdrawal.Code.unmarshalSSZ Reg64.rdi (-16) 52 53", "kstep_add Reg64.rdi (-16) _ (k + 52) (k + 53) hq he hend"),
    "Prysm.PendingPartialWithdrawal.Decode.generated_step_s53": ("@Codec.stepMovIKind h Prysm.PendingPartialWithdrawal.Code.unmarshalSSZ Reg64.rcx 8 53 55", "kstep_movi Reg64.rcx 8 _ (k + 53) (k + 55) hq he hend"),
    "Prysm.PendingPartialWithdrawal.Decode.generated_step_Index_call": (f'@Codec.callDecSegKindG4 h Prysm.PendingPartialWithdrawal.Code.unmarshalSSZ {FN_VI} "L_pw_b9" 55 56 88',
                            "calldec_seg_w _ _ _ (k + 55) (k + 56) (k + 88) hq he hjc hB hl"),
    "pw_g4dec_Root_seg": ("@Codec.bytesDecSegKindWindow h 32 Prysm.PendingPartialWithdrawal.Code.unmarshalSSZ Reg64.rax 89 108 114 112 120 56 24 32 40 16",
                          "bytesdec_seg_window 32 (Or.inl rfl) Reg64.rdx Reg64.rax (Or.inl rfl) (Or.inl rfl) _ _ _ _ _ _ _ _ _ _ _ (k + 89) (k + 102) (k + 102) (k + 108) (k + 114) hqA heA hqB heB hjl hl hjm hend"),
    "pw_g4dec_s115": ("@Codec.stepJmpKind h Prysm.PendingPartialWithdrawal.Code.unmarshalSSZ \"L_pw_200\" 115 130", 'kstep_jmp "L_pw_200" _ (k + 115) (k + 130) hq he hl'),
    "pw_g4dec_s130": ("@Codec.stepLabelKind h Prysm.PendingPartialWithdrawal.Code.unmarshalSSZ \"L_pw_200\" 130 131", 'kstep_label "L_pw_200" _ (k + 130) (k + 131) hq he hend'),
    "pw_g4dec_s131": ("@Codec.stepStKind h Prysm.PendingPartialWithdrawal.Code.unmarshalSSZ Reg64.rsi Reg64.rax 24 131 132", "kstep_st Reg64.rsi Reg64.rax 24 _ (k + 131) (k + 132) hq he hend"),
    "pw_g4dec_Sig_seg": ("@Codec.bytesDecSegZKindWindow h 96 Prysm.PendingPartialWithdrawal.Code.unmarshalSSZ Reg64.rdx 132 150 156 112 120 56 48 56 64",
                         "bytesdec_seg_z_window 96 (Or.inr (Or.inr rfl)) Reg64.rdx Reg64.rdx (Or.inl rfl) (Or.inr (Or.inr (Or.inl rfl))) _ _ _ _ _ _ _ _ _ _ (k + 132) (k + 145) (k + 145) (k + 150) (k + 156) hqA heA hqB heB hjl hl hjm hend"),
    "pw_g4dec_s156": ("@Codec.stepLdvKind h Prysm.PendingPartialWithdrawal.Code.unmarshalSSZ Reg64.rsi Reg64.rsp 56 156 157", "kstep_ldv Reg64.rsi Reg64.rsp 56 _ (k + 156) (k + 157) hq he hend"),
    "pw_g4dec_s157": ("@Codec.stepStKind h Prysm.PendingPartialWithdrawal.Code.unmarshalSSZ Reg64.rsi Reg64.rdx 48 157 158", "kstep_st Reg64.rsi Reg64.rdx 48 _ (k + 157) (k + 158) hq he hend"),
}
G4F = [("Amount", ["Prysm.PendingPartialWithdrawal.Decode.generated_step_s50", "Prysm.PendingPartialWithdrawal.Decode.generated_step_s51"]), ("Index", ["Prysm.PendingPartialWithdrawal.Decode.generated_step_s52", "Prysm.PendingPartialWithdrawal.Decode.generated_step_s53", "Prysm.PendingPartialWithdrawal.Decode.generated_step_Index_call"]),
       ("Root", ["pw_g4dec_Root_seg", "pw_g4dec_s115", "pw_g4dec_s130", "pw_g4dec_s131"]),
       ("Sig", ["pw_g4dec_Sig_seg", "pw_g4dec_s156", "pw_g4dec_s157"])]


def g4_block(t, kind, proof):
    return ("set_option maxHeartbeats 4000000 in\nset_option maxRecDepth 100000 in\n"
            f"/-- Directive `x`. -/\ntheorem {t} (k : Nat) (hk : Prysm.PendingPartialWithdrawal.Code.unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh Prysm.PendingPartialWithdrawal.Code.unmarshalSSZ k) :\n"
            f"    T := by\n  have hq := Codec.win hk 1 1\n  with_reducible exact {G4_LEMMAS[proof.split()[0]]}.{proof}\n"
            f"theorem {t}_kind : ∀ (h : Host), type_of% (@{t} h) = {kind} := by\n  intro h; with_reducible rfl\n\n")


def g4_text(fields=G4F, kinds=G4K, n=None, m=None, fj=None):
    import json
    n = len(fields) if n is None else n
    m = n if m is None else m
    fj = json.dumps([dict(field=f, theorems=ts) for f, ts in fields]) if fj is None else fj
    return ("import Codec.Kind.WindowSteps\nimport Codec.Kind.FixedBytesDecodeWindow\nimport Codec.CalleeDecodeWindow\nimport Codec.FixedBytesDecodeWindowOffsetZero\n\n"
            f"/-! Generated by `gen/scal/scalgen.py p2dec`; GEN4 coverage (`p2dec --gen4`): {n} of {m} fields. -/\n\n"
            f"/-! GEN4 fields (machine-readable, read by `kindcheck.py`):\nFIELDS-JSON: {fj}\n-/\n\n"
            "open Machine Runtime Prysm.Deposit_Data.Code\nvariable [Host]\n\nopen Codec\nnamespace Prysm.Fixture\n\n"
            + "".join(g4_block(t, *kinds[t]) for _, ts in fields for t in ts) + "end Prysm.Fixture\n")


GOOD4 = g4_text()


def g4_cases():
    """Controls of rules 10, 10b, 10c, 11, 6d."""

    def kchg(t, new):
        old = f"type_of% (@{t} h) = {G4K[t][0]} := by"
        assert GOOD4.count(old) == 1, t
        return GOOD4.replace(old, f"type_of% (@{t} h) = {new} := by")

    def pchg(t, new):
        old = f"  with_reducible exact {G4_LEMMAS[G4K[t][1].split()[0]]}.{G4K[t][1]}\n"
        assert GOOD4.count(old) == 1, t
        return GOOD4.replace(old, new)
    unc = json_line([("Tail", "x")])[:-1] + "]"
    unc = 'UNCOVERED-JSON: [{"field": "Tail", "reason": "walk stopped", "miss_class": "register"}]'
    PH = ("/-! PARTIAL OUTPUT (scalgen exit 3): 4 of 5 fields of `v1alpha1.X` (--gen4); NOT generated: Tail. "
          "Not a complete p2dec output.\n" + unc + "\n-/\n")
    part = g4_text(m=5).replace("\n\n/-! Generated", "\n\n" + PH + "/-! Generated", 1)
    assert part.count(PARTIAL) == 1
    st = G4K["Prysm.PendingPartialWithdrawal.Decode.generated_step_s51"][0]
    k2 = dict(G4K, pw_g4dec_Index_seg=G4K["pw_g4dec_Root_seg"])
    two_blocks = [G4F[0], ("Index", G4F[1][1] + ["pw_g4dec_Index_seg"]), G4F[2], G4F[3]]
    return [
        ("g4_good", GOOD4, True, False),
        ("g4_step_degenerate_self", kchg("Prysm.PendingPartialWithdrawal.Decode.generated_step_s51", "type_of% (@Prysm.PendingPartialWithdrawal.Decode.generated_step_s51 h)"), False, False),
        ("g4_step_kind_other_namespace", kchg("Prysm.PendingPartialWithdrawal.Decode.generated_step_s51", st.replace("@Codec.", "@Prysm.Fixture.")), False, False),
        ("g4_step_degenerate_true", kchg("Prysm.PendingPartialWithdrawal.Decode.generated_step_s51", "True"), False, False),
        ("g4_step_kind_missing", GOOD4.replace("theorem Prysm.PendingPartialWithdrawal.Decode.generated_step_s51_kind", "theorem pw_g4dec_s51_kinx"), False, False),
        ("g4_st_without_disp", kchg("Prysm.PendingPartialWithdrawal.Decode.generated_step_s51", st.replace(" 16 51 52", " 51 52")), False, False),
        ("g4_st_register_not_reg64", kchg("Prysm.PendingPartialWithdrawal.Decode.generated_step_s51", st.replace("Reg64.r8", "Reg64.xmm0")), False, False),
        ("g4_st_register_symbolic", kchg("Prysm.PendingPartialWithdrawal.Decode.generated_step_s51", st.replace("Reg64.r8", "r")), False, False),
        ("g4_st_other_const", kchg("Prysm.PendingPartialWithdrawal.Decode.generated_step_s51", st.replace("Prysm.PendingPartialWithdrawal.Code.unmarshalSSZ", "Prysm.PendingConsolidation.Code.unmarshalSSZ")), False, False),
        ("g4_add_extra_param", kchg("Prysm.PendingPartialWithdrawal.Decode.generated_step_s52", G4K["Prysm.PendingPartialWithdrawal.Decode.generated_step_s52"][0] + " 0"), False, False),
        ("g4_call_two_indices", kchg("Prysm.PendingPartialWithdrawal.Decode.generated_step_Index_call", G4K["Prysm.PendingPartialWithdrawal.Decode.generated_step_Index_call"][0].replace(" 56 88", " 88")), False, False),
        ("g4_call_callee_without_spec", kchg("Prysm.PendingPartialWithdrawal.Decode.generated_step_Index_call", G4K["Prysm.PendingPartialWithdrawal.Decode.generated_step_Index_call"][0].replace(
            "consensus_types_primitives.ValidatorIndex", "proto_prysm_v1alpha1.Checkpoint")), False, False),
        ("g4_seg_ry_rbx", kchg("pw_g4dec_Root_seg", G4K["pw_g4dec_Root_seg"][0].replace("Reg64.rax", "Reg64.rbx")), False, False),
        ("g4_seg_size_64", kchg("pw_g4dec_Root_seg", G4K["pw_g4dec_Root_seg"][0].replace(" h 32 ", " h 64 ")), False, False),
        ("g4_seg_missing_src", kchg("pw_g4dec_Root_seg", G4K["pw_g4dec_Root_seg"][0].replace(" 40 16", " 40")), False, False),
        ("g4_segz_with_src", kchg("pw_g4dec_Sig_seg", G4K["pw_g4dec_Sig_seg"][0] + " 0"), False, False),
        ("g4_lemma_kind_mismatch", pchg("Prysm.PendingPartialWithdrawal.Decode.generated_step_s50", "  with_reducible exact Codec.kstep_ldv Reg64.r8 Reg64.rbx 8 _ (k + 50) (k + 51) hq he hend\n"), False, False),
        ("g4_lemma_only_in_string", pchg("Prysm.PendingPartialWithdrawal.Decode.generated_step_s50", '  have x := "Codec.kstep_ldb "\n  with_reducible exact foo\n'), False, False),
        ("g4_lemma_only_in_comment", pchg("Prysm.PendingPartialWithdrawal.Decode.generated_step_s50", "  -- Codec.kstep_ldb\n  with_reducible exact foo\n"), False, False),
        ("g4_two_lemmas", pchg("Prysm.PendingPartialWithdrawal.Decode.generated_step_s50", "  with_reducible exact Codec.kstep_ldb (Codec.kstep_st x)\n"), False, False),
        ("g4_fields_json_missing", GOOD4.replace("FIELDS-JSON: ", "FIELDS: "), False, False),
        ("g4_fields_json_two_lines", GOOD4.replace("FIELDS-JSON: ", "FIELDS-JSON: []\nFIELDS-JSON: "), False, False),
        ("g4_theorem_not_listed", g4_text(fj='[{"field": "Amount", "theorems": ["Prysm.PendingPartialWithdrawal.Decode.generated_step_s50"]}, {"field": "Index", "theorems": ["Prysm.PendingPartialWithdrawal.Decode.generated_step_s52", "Prysm.PendingPartialWithdrawal.Decode.generated_step_s53", "Prysm.PendingPartialWithdrawal.Decode.generated_step_Index_call"]}, {"field": "Root", "theorems": ["pw_g4dec_Root_seg", "pw_g4dec_s115", "pw_g4dec_s130", "pw_g4dec_s131"]}, {"field": "Sig", "theorems": ["pw_g4dec_Sig_seg", "pw_g4dec_s156", "pw_g4dec_s157"]}]'), False, False),
        ("g4_listed_theorem_absent", g4_text(fj='[{"field": "Amount", "theorems": ["Prysm.PendingPartialWithdrawal.Decode.generated_step_s50", "Prysm.PendingPartialWithdrawal.Decode.generated_step_s51", "Prysm.PendingPartialWithdrawal.Decode.generated_step_s49"]}, {"field": "Index", "theorems": ["Prysm.PendingPartialWithdrawal.Decode.generated_step_s52", "Prysm.PendingPartialWithdrawal.Decode.generated_step_s53", "Prysm.PendingPartialWithdrawal.Decode.generated_step_Index_call"]}, {"field": "Root", "theorems": ["pw_g4dec_Root_seg", "pw_g4dec_s115", "pw_g4dec_s130", "pw_g4dec_s131"]}, {"field": "Sig", "theorems": ["pw_g4dec_Sig_seg", "pw_g4dec_s156", "pw_g4dec_s157"]}]'), False, False),
        ("g4_theorem_in_two_fields", g4_text(fj='[{"field": "Amount", "theorems": ["Prysm.PendingPartialWithdrawal.Decode.generated_step_s50", "Prysm.PendingPartialWithdrawal.Decode.generated_step_s51"]}, {"field": "Index", "theorems": ["Prysm.PendingPartialWithdrawal.Decode.generated_step_s51", "Prysm.PendingPartialWithdrawal.Decode.generated_step_s52", "Prysm.PendingPartialWithdrawal.Decode.generated_step_s53", "Prysm.PendingPartialWithdrawal.Decode.generated_step_Index_call"]}, {"field": "Root", "theorems": ["pw_g4dec_Root_seg", "pw_g4dec_s115", "pw_g4dec_s130", "pw_g4dec_s131"]}, {"field": "Sig", "theorems": ["pw_g4dec_Sig_seg", "pw_g4dec_s156", "pw_g4dec_s157"]}]'), False, False),
        ("g4_two_blocks_one_field", g4_text(fields=two_blocks, kinds=k2), False, False),
        ("g4_block_name_other_field", g4_text(fields=[("Amount", G4F[0][1]), ("Idx", G4F[1][1]), G4F[2], G4F[3]]), False, False),
        ("g4_count_edited_dropped_field", g4_text(fields=G4F[:3], n=4), False, False),
        ("g4_n_ne_m_default", g4_text(m=5), False, False),
        ("s2_n29_header_removed_field_dropped", g4_text(fields=G4F[:3]).replace("GEN4 coverage (`p2dec --gen4`): 3 of 3 fields", "generated"), False, False),
        ("s2_n29_gen2_header_removed", GOOD2.replace("GEN2 coverage (`p2dec --gen2`): 3 of 3 fields", "generated"), False, False),
        ("g4_partial_good", part, True, True),
        ("g4_partial_default_rejects", part, False, False),
        ("g4_partial_uncovered_listed", part.replace('"Tail"', '"Sig"').replace("NOT generated: Tail", "NOT generated: Sig"), False, True),
        ("g4_partial_bad_miss_key", part.replace('"miss_class"', '"class"'), False, True),
    ]


def s4_exit_cases():
    """main() exit codes on a temporary partial file (pins read from the tree)."""
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


# ------------------------------------------------------------------------------------------------------------------
# Rule 12 (`scalgen.py p2dec --gen5`). A GEN5 file is a GEN4 file (checked by rules 1-11 up to the GEN5
# block) followed by one block `/-! GEN5 (`p2dec --gen5` … GEN5-JSON: {…} -/` and the GEN5 theorems:
#  12a. (removed: a git-blob pin of the kind and lemma modules);
#  12b. the GEN5 theorems are exactly, in this order: P_head, P_f1 … P_fn, P_epi, P_accept, [P_accept_stmt |
#       P_accept_same], P_reject (P = the GEN5-JSON prefix, n = the IR field count), each but the identity followed by
#       its `_kind` theorem `theorem T_kind : ∀ (h : Host), type_of% (@T h)` / `    = @Codec.K h C …` with
#       K = decHeadKindN / decFieldKindN / decEpiKindN / decAcceptKindN / decRejectKindN and the proof line
#       `  intro h; rfl` (`  intro h; with_reducible rfl` for the reject kind); every `hk` binder names C;
#  12c. the kind parameters are RECOMPUTED here, independently of the generator, from the `.S` file and the IR JSON
#       named (with sha256) in the file header: the field list (`.bytes n` / `.u64`, IR order, IR SSZ / Go offsets
#       equal to the kind's running sums), the layout `L` (callees in order of first `callq`, stack chunks, lengths,
#       runtime configuration, guard addend, state word, post-state slots and existentials, frame) by the rules of the
#       GEN5 lemma unit's hand-over, the `pc` and `done` of every boundary state (head end, the end of each field event along the
#       accept path), and the reject size; a file whose kind parameters differ FAILS. This is the statement check of
#       a generated accept theorem when no hand statement exists;
#  12d. the accept proof chains P_head, every P_f<i> and P_epi;
#  12e. an identity `P_accept_stmt : X := P_accept` or `P_accept_same : … type_of% (@P_accept h) = type_of% (@X h)`
#       names a hand statement X (not generated, rule 6b); without it the PASS line says "kind instance only".
# Not checked here: the register facts, stack slots and existentials of the boundary states (the kernel checks that
# they chain); that the file builds; that X is independent of the generator (a human confirms it).
G5_MARK = "/-! GEN5 (`p2dec --gen5`"
G5_PRIM = "github.com_OffchainLabs_prysm_v7_consensus_types_primitives."
G5_CONST = {"Slot": "Prysm.AttestationData.Code.slotUnmarshalSSZ", "CommitteeIndex": "Prysm.AttestationData.Code.committeeIndexUnmarshalSSZ",
            "ValidatorIndex": "Prysm.ValidatorIndex.Code.unmarshalSSZ", "Epoch": "Prysm.Epoch.Code.unmarshalSSZ"}
G5_HDR = re.compile(r"Generated by `gen/scal/scalgen\.py p2dec` from `([^`]+)`\n\(sha256 `([0-9a-f]{64})`\) and `([^`]+)` "
                    r"\(sha256 `([0-9a-f]{64})`, type `([^`]+)`\)")


class G5Mismatch(Exception):
    pass


def g5_ir(ir_text, tname):
    """(fields, ssz size) from the IR JSON: fields = [(name, '.bytes n' | '.u64', callee or None, ssz off, go off)]."""
    import json
    pkg, name = tname.rsplit(".", 1)
    ts = [t for c in json.loads(ir_text)["configs"] for t in c.get("types", [])
          if t.get("name") == name and t.get("package", "").endswith("/" + pkg)]
    if len(ts) != 1:
        raise G5Mismatch(f"type {tname}: {len(ts)} IR entries")
    t = ts[0]
    goff = {f["name"]: f["offset_gc_amd64"] for f in t["go_fields"]}
    out, so = [], 0
    for f in t["ir"]["fields"]:
        v = f["v"]
        if v.get("k") == "vector" and v.get("elem", {}).get("k") == "byte" and v.get("go_type") == "[]byte" \
                and v.get("size") in (32, 48, 96) and v.get("fixed_size") == v.get("size") and not v.get("variable"):
            kd, cal = f".bytes {v['size']}", None
        elif v.get("k") == "uint" and v.get("bits") == 64 and v.get("go_type") == "uint64" and v.get("fixed_size") == 8:
            kd, cal = ".u64", None
        elif v.get("k") == "overlay" and v.get("fixed_size") == 8 and (v.get("deleg") or {}).get("unmarshaler") \
                and v.get("name") in G5_CONST and v.get("pkg", "").endswith("/consensus-types/primitives") \
                and (v.get("underlying") or {}).get("k") == "uint" and (v.get("underlying") or {}).get("bits") == 64:
            kd, cal = ".u64", v["name"]
        else:
            raise G5Mismatch(f"field {f['key']}: IR kind {v.get('k')} ({v.get('go_type')}) is not a GEN5 field kind")
        out.append((f["key"], kd, cal, so, goff.get(f["key"])))
        so += v["fixed_size"]
    if t["ir"].get("fixed_size") != so:
        raise G5Mismatch(f"IR fixed size {t['ir'].get('fixed_size')} != sum of field sizes {so}")
    return out, so


def g5_expect(dirs, fields, sz):
    """Independent recomputation of the GEN5 kind parameters from the directives (`.S`, nonblank lines stripped)
    and the IR fields. Returns dict(L=text, fields=text, pcs=[pc_0 … pc_n], sz)."""
    lab = lambda d: d[:-1] if d.endswith(":") and " " not in d else None
    idx = {lab(d): i for i, d in enumerate(dirs) if lab(d)}
    m = re.fullmatch(r"sub \$(0x[0-9a-f]+),%rsp", dirs[6]) if len(dirs) > 11 else None
    if not m or dirs[9] != f"cmp ${sz:#x},%rcx" or not dirs[10].startswith("jne "):
        raise G5Mismatch("head: directive 6 is not `sub $F,%rsp` or directive 9 is not `cmp $size,%rcx`")
    F = int(m.group(1), 16)
    frame = F + 8
    st = fields[0][4] == 8
    so, go = 0, 8 if st else 0
    for (n_, kd, cal, s_, g_) in fields:
        if s_ != so or g_ != go:
            raise G5Mismatch(f"field {n_}: IR SSZ / Go offsets {s_} / {g_}, kind running sums {so} / {go}")
        so += int(kd.split()[1]) if kd.startswith(".bytes") else 8
        go += 24 if kd.startswith(".bytes") else 8
    home = {"rax": 8, "rbx": 16, "rdi": 32}
    spills = {16: "rbx"}
    i = 11
    while (mm := re.fullmatch(r"mov %(rax|rbx|rdi),(0x[0-9a-f]+)\(%rsp\)", dirs[i])):
        if int(mm.group(2), 16) - frame != home[mm.group(1)]:
            raise G5Mismatch(f"head: spill `{dirs[i]}` not to the home slot")
        spills[home[mm.group(1)]] = mm.group(1)
        i += 1
    if dirs[i] == "test %al,(%rax)":
        i += 1
    pcs = [i]
    # the accept path
    R = {}
    written, callees, events = {}, [], {}
    n_ms = n_mm = 0
    last_call = None
    has_rt = has_call = False
    prev = None
    seen = set()
    r32 = {"eax": "rax", "ebx": "rbx", "ecx": "rcx", "edx": "rdx", "esi": "rsi", "edi": "rdi"}
    while True:
        if i >= len(dirs) or i in seen:
            raise G5Mismatch("accept path: end of file or loop before the epilogue")
        seen.add(i)
        d = dirs[i]
        if d == "nop" or lab(d):
            i += 1
            continue
        if d == f"add ${F:#x},%rsp":
            break
        if (mm := re.fullmatch(r"jmp (\S+)", d)):
            i = idx[mm.group(1)]
            continue
        if (mm := re.fullmatch(r"j(e|ne) (\S+)", d)):
            if prev == "cmpl $0x0,runtime.writeBarrier(%rip)":
                i = idx[mm.group(2)] if mm.group(1) == "e" else i + 1
            elif prev == "test %rax,%rax" and mm.group(1) == "e":
                i = idx[mm.group(2)]
                # a callee call's continuation label: the event of the call field
                if pend_call is None:
                    raise G5Mismatch("accept path: `je` after `test %rax,%rax` without a callee call")
                events[pend_call] = i + 1
            else:
                raise G5Mismatch(f"accept path: branch `{d}` after `{prev}`")
            prev = d
            continue
        if (mm := re.fullmatch(r"callq (\S+)", d)):
            fn = mm.group(1)
            last_call = i
            R = {}
            pend_call = None
            if fn == "runtime.makeslice":
                has_rt = True
                R["rax"] = ("ptr", n_ms)
                n_ms += 1
            elif fn == "runtime.memmove":
                n_mm += 1
            elif fn.startswith(G5_PRIM) and fn.endswith(".UnmarshalSSZ") and fn[len(G5_PRIM):-13] in G5_CONST:
                has_call = True
                c = G5_CONST[fn[len(G5_PRIM):-13]]
                if c not in callees:
                    callees.append(c)
                R["rax"] = R["rbx"] = ("zero",)
                todo = [k for k, f in enumerate(fields) if f[2] == fn[len(G5_PRIM):-13] and k not in events]
                if not todo:
                    raise G5Mismatch(f"accept path: call {fn} without an open IR field of that callee")
                pend_call = todo[0]
            else:
                raise G5Mismatch(f"accept path: call of {fn}")
            prev = d
            i += 1
            continue
        if (mm := re.fullmatch(r"mov %(\w+),(0x[0-9a-f]+)\(%rsp\)", d)):
            o = int(mm.group(2), 16)
            if 0x18 <= o < F:
                v = R.get(mm.group(1))
                if v is None:
                    raise G5Mismatch(f"accept path: store `{d}` of a value this check does not model")
                written[o] = v
            elif not (o < 0x18 and False):
                raise G5Mismatch(f"accept path: stack store `{d}` outside the frame slots [0x18, F)")
        elif (mm := re.fullmatch(r"mov %(\w+),(?:(0x[0-9a-f]+))?\(%(\w+)\)", d)) and mm.group(3) not in ("rsp", "r11"):
            o = int(mm.group(2), 16) if mm.group(2) else 0
            bi = 0
            for k, (n_, kd, cal, s_, g_) in enumerate(fields):
                if kd.startswith(".bytes"):
                    if g_ == o and k not in events and n_mm >= bi + 1:
                        events[k] = i + 1
                    bi += 1
                elif cal is None and g_ == o and k not in events:
                    events[k] = i + 1
        # a register written by this directive is no longer known
        if not d.startswith(("test ", "cmp ", "cmpl ")) and (mm := re.search(r",%(\w+)$", d)):
            r = r32.get(mm.group(1), mm.group(1))
            src = re.fullmatch(r"mov %(\w+),%(\w+)", d)
            R.pop(r, None)
            if src and src.group(1) in R:
                R[r] = R[src.group(1)]
        prev = d
        i += 1
    if sorted(events) != list(range(len(fields))):
        raise G5Mismatch(f"accept path: field events for {sorted(events)} of {len(fields)} fields")
    pcs += [events[k] for k in range(len(fields))]
    if pcs != sorted(pcs) or len(set(pcs)) != len(pcs):
        raise G5Mismatch(f"field events not in IR order: {pcs}")
    if last_call is None:
        raise G5Mismatch("no call on the accept path")
    # the layout by the rules of the GEN5 lemma unit's hand-over
    stack = [("at", -8)] + [("at", o) for o in sorted(spills)]
    area = [0] if has_rt and not has_call else ([0, 8, 16] if has_rt else [8])
    stack += [("at", -frame + a) for a in area] + [("at", -frame + o) for o in sorted(written)]
    stack += [("at", -(frame + 8)), ("lo",) if has_rt else ("at", -(frame + 16))]
    sl = lambda c, v: (".lo " + v) if c[0] == "lo" else f".at ({'.up' if c[1] > 0 else '.dn'} {abs(c[1])}) {v}"
    pre = [sl(c, f"(.orig {k})") for k, c in enumerate(stack)]
    lens = [f"({k}, {24 if (has_rt and not has_call and c == ('at', -frame)) else 8})"
            for k, c in enumerate(stack) if c != ("lo",)]
    rt = (f"some ⟨{'true' if has_call else 'false'}, {8 if has_call else 0}, {len(stack) - 1}, "
          f"{frame + 8 + (8 if has_call else 0)}⟩") if has_rt else "none"
    post = [sl(("at", -8), "(.reg .rbp)")] + [sl(("at", o), f"(.reg .{spills[o]})") for o in sorted(spills)]
    post.append(sl(("at", -frame if has_rt else -frame + 8), "(.ex 0)"))
    for o in sorted(written):
        v = written[o]
        post.append(sl(("at", -frame + o), ".zero" if v == ("zero",) else f"(.ptr {v[1]})"))
    post += [sl(("at", -(frame + 8)), f"(.ret {last_call + 1})"), sl(stack[-1], "(.ex 1)")]
    exs = "[.n 24, .lo]" if has_rt else "[.n 8, .n 8]"
    L = (f"(Codec.DecLayout.mk [{', '.join(callees)}] {len(stack)} [{', '.join(lens)}] [{', '.join(pre)}] ({rt}) "
         f"{frame + 8 if has_call else 0} {'true' if st else 'false'} {exs} [{', '.join(post)}] {frame})")
    return dict(L=L, fields="[" + ", ".join(f[1] for f in fields) + "]", pcs=pcs, sz=sz)


def g5_split_kind(lines, j):
    """The `_kind` theorem at line j: (theorem name, kind name, parameter text, proof line) or an error string."""
    m = re.fullmatch(r"theorem (\S+)_kind : ∀ \(h : Host\), type_of% \(@(\S+) h\)", lines[j])
    if not m or m.group(1) != m.group(2):
        return f"line {j + 1}: `_kind` header is not `theorem T_kind : ∀ (h : Host), type_of% (@T h)`"
    k = j + 1
    body = []
    while k < len(lines) and not lines[k].endswith(" := by"):
        body.append(lines[k])
        k += 1
    if k >= len(lines):
        return f"{m.group(1)}_kind: no `:= by`"
    body.append(lines[k][:-len(" := by")])
    txt = " ".join(x.strip() for x in body)
    mk = re.fullmatch(r"= @Codec\.(\w+) h (\S+) ?(.*)", txt)
    if not mk:
        return f"{m.group(1)}_kind: right-hand side is not `= @Codec.K h C …`"
    return m.group(1), mk.group(1), mk.group(2), mk.group(3), (lines[k + 1] if k + 1 < len(lines) else ""), k + 1


def g5_balanced(s, open_, close):
    """Split `s` (starting with `open_`) into the balanced prefix and the rest."""
    depth = 0
    for i, ch in enumerate(s):
        depth += ch == open_
        depth -= ch == close
        if depth == 0:
            return s[:i + 1], s[i + 1:].strip()
    return None, s


def check_gen5(text, gnames=frozenset(), kr=None, expect=None):
    """Rule 12 on the GEN5 part of `text`. `expect` (for the selftest) replaces the recomputation from the files."""
    import hashlib
    import json
    kr = KR if kr is None else kr
    errs, info = [], ""
    if text.count(G5_MARK) != 1:
        return errs + [f"rule 12: {text.count(G5_MARK)} GEN5 blocks (expected 1)"], info
    head, g5 = text.split(G5_MARK, 1)
    lines = (G5_MARK + g5).split("\n")
    gj = [l for l in lines if l.startswith("GEN5-JSON: ")]
    try:
        assert len(gj) == 1
        J = json.loads(gj[0][len("GEN5-JSON: "):])
        P = J["accept"][:-len("_accept")]
        assert J["accept"] == P + "_accept" and P
    except Exception:
        return errs + ["rule 12: no single valid `GEN5-JSON:` line with the accept theorem name"], info
    # the inputs named in the header; the kind parameters recomputed from them
    if expect is None:
        hm = G5_HDR.search(head)
        if not hm:
            return errs + ["rule 12c: no `Generated … from `S` (sha256 …) and `IR` (sha256 …, type …)` header"], info
        try:
            sraw, iraw = (kr / hm.group(1)).read_bytes(), (kr / hm.group(3)).read_bytes()
        except OSError as e:
            return errs + [f"rule 12c: input file not readable: {e}"], info
        if hashlib.sha256(sraw).hexdigest() != hm.group(2) or hashlib.sha256(iraw).hexdigest() != hm.group(4):
            return errs + ["rule 12c: sha256 of the .S or IR file differs from the header"], info
        try:
            fields, sz = g5_ir(iraw.decode(), hm.group(5))
            dirs = [l.strip() for l in sraw.decode("ascii").split("\n") if l.strip()]
            expect = g5_expect(dirs, fields, sz)
        except (G5Mismatch, KeyError, IndexError, ValueError) as e:
            return errs + [f"rule 12c: recomputation refused: {type(e).__name__}: {e}"], info
    n = len(expect["pcs"]) - 1
    # rules 2 / 3 on the GEN5 part
    in_block = 0
    for i, l in enumerate(lines, 1):
        if in_block or l.lstrip().startswith("/-"):
            in_block += l.count("/-") - l.count("-/")
            continue
        if BANNED.search(l.split("--", 1)[0]):
            errs.append(f"GEN5 line {i}: banned token: {l.strip()}")
        if not TOP_OK.match(l):
            errs.append(f"GEN5 line {i}: top-level form not allowed: {l.strip()[:80]}")
    thms = [(i, m.group(1)) for i, l in enumerate(lines) if (m := THM.match(l))]
    names = [t for _, t in thms]
    kinds = [(f"{P}_head", "decHeadKindN", 1), *[(f"{P}_f{k + 1}", "decFieldKindN", 2) for k in range(n)],
             (f"{P}_epi", "decEpiKindN", 1), (f"{P}_accept", "decAcceptKindN", 0), (f"{P}_reject", "decRejectKindN", None)]
    ident = [x for x in names if x in (f"{P}_accept_stmt", f"{P}_accept_same")]
    want = []
    for t, _, _ in kinds:
        want += [t, t + "_kind"]
        if t == f"{P}_accept":
            want += ident[:1]
    if names != want or len(ident) > 1:
        return errs + [f"rule 12b: GEN5 theorems {names}, expected {want}"], info
    pos = {t: i for i, t in thms}
    C = None
    for t, kn, nd in kinds:
        hk = HK.search(lines[pos[t]])
        if not hk:
            errs.append(f"rule 12b: {t}: no `(hk : C.IsInfixAt Host.prog k)` binder on its first line")
            continue
        C = C or hk.group(1)
        if hk.group(1) != C:
            errs.append(f"rule 12b: {t}: code constant {hk.group(1)} != {C}")
        r = g5_split_kind(lines, pos[t + "_kind"])
        if isinstance(r, str):
            errs.append("rule 12b: " + r)
            continue
        _, kname, c2, rest, pl, _ = r
        if kname != kn:
            errs.append(f"rule 12b: {t}_kind names {kname}, expected {kn}")
            continue
        if c2 != C:
            errs.append(f"rule 12b: {t}_kind: code constant {c2} != {C}")
        if pl != ("  intro h; with_reducible rfl" if nd is None else "  intro h; rfl"):
            errs.append(f"rule 12b: {t}_kind: proof line `{pl}`")
        if nd is None:
            if rest != str(expect["sz"]):
                errs.append(f"rule 12c: {t}_kind: size {rest}, recomputed {expect['sz']}")
            continue
        Lt, rest = g5_balanced(rest, "(", ")")
        if Lt is None or " ".join(Lt.split()) != " ".join(expect["L"].split()):
            errs.append(f"rule 12c: {t}_kind: layout parameter differs from the recomputation\n      file:       "
                        f"{' '.join((Lt or '').split())}\n      recomputed: {expect['L']}")
        Ft, rest = g5_balanced(rest, "[", "]")
        if Ft != expect["fields"]:
            errs.append(f"rule 12c: {t}_kind: fields {Ft}, recomputed {expect['fields']}")
        ds = []
        for _ in range(nd):
            Dt, rest = g5_balanced(rest, "⟨", "⟩")
            dm = re.match(r"⟨(\d+), (\d+), ", Dt or "")
            ds.append((int(dm.group(1)), int(dm.group(2))) if dm else None)
        if rest:
            errs.append(f"rule 12b: {t}_kind: extra parameters `{rest[:60]}`")
        k = int(t.rsplit("_f", 1)[1]) if kn == "decFieldKindN" else None
        exp = {"decHeadKindN": [0], "decFieldKindN": [k - 1, k] if k else [], "decEpiKindN": [n], "decAcceptKindN": []}[kn]
        for dd, b in zip(ds, exp):
            if dd != (expect["pcs"][b], b):
                errs.append(f"rule 12c: {t}_kind: boundary state (pc, done) = {dd}, recomputed {(expect['pcs'][b], b)}")
    # 12d: the accept proof is the chain
    acc = "\n".join(lines[pos[f"{P}_accept"]:pos[f"{P}_accept_kind"]])
    for t in [f"({P}_head "] + [f"({P}_f{k + 1} " for k in range(n)] + [f"exact {P}_epi "]:
        if acc.count(t) != 1:
            errs.append(f"rule 12d: the accept proof does not use `{t.strip('( ')}` exactly once")
    # 12e: the statement identity
    if ident:
        l = lines[pos[ident[0]]]
        if ident[0].endswith("_stmt"):
            m = re.fullmatch(rf"theorem {P}_accept_stmt : (Prysm(?:\.\w+)+) := {P}_accept", l)
        else:
            m = re.fullmatch(rf"theorem {P}_accept_same : ∀ \(h : Host\), type_of% \(@{P}_accept h\) = "
                             rf"type_of% \(@(Prysm(?:\.\w+)+) h\) := by", l)
            if m and lines[pos[ident[0]] + 1] != "  intro h; rfl":
                m = None
        if not m:
            errs.append(f"rule 12e: {ident[0]}: not the identity form")
        elif GENNS.match(m.group(1)) or m.group(1).rsplit(".", 1)[-1] in gnames or m.group(1).rsplit(".", 1)[-1] in names:
            errs.append(f"rule 12e: {ident[0]}: {m.group(1)} is a generated name")
        else:
            info = f"statement check: kind (parameters recomputed) + identity against {m.group(1)}"
    else:
        info = "statement check: kind instance only, parameters recomputed from the IR and the .S"
    return errs, info


# ---- rule 12 selftest controls
G5_VE = ("prysm/go1.26.10/e2e/h6/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.VoluntaryExit.UnmarshalSSZ.S",
         "v1alpha1.VoluntaryExit")
# the layouts of the GEN5 lemma unit's hand-over (`Codec/Kind/DecodeAcceptAnyFrameInstances.lean`: layCal, layMix40, layRt, layMix60), transcribed by hand as
# constructor text; the recomputation from the real `.S` / IR must give exactly these
G5_HAND = {
    "VoluntaryExit": ("h6", "(Codec.DecLayout.mk [Prysm.Epoch.Code.unmarshalSSZ, Prysm.ValidatorIndex.Code.unmarshalSSZ] 7 [(0, 8), (1, 8), (2, 8), "
                      "(3, 8), (4, 8), (5, 8), (6, 8)] [.at (.dn 8) (.orig 0), .at (.up 8) (.orig 1), .at (.up 16) (.orig 2), "
                      ".at (.up 32) (.orig 3), .at (.dn 72) (.orig 4), .at (.dn 88) (.orig 5), .at (.dn 96) (.orig 6)] (none) 88 "
                      "true [.n 8, .n 8] [.at (.dn 8) (.reg .rbp), .at (.up 8) (.reg .rax), .at (.up 16) (.reg .rbx), .at (.up 32) "
                      "(.reg .rdi), .at (.dn 72) (.ex 0), .at (.dn 88) (.ret 56), .at (.dn 96) (.ex 1)] 80)"),
    "PendingDeposit": ("h6", "(Codec.DecLayout.mk [Prysm.AttestationData.Code.slotUnmarshalSSZ] 10 [(0, 8), (1, 8), (2, 8), (3, 8), (4, 8), (5, 8), "
                       "(6, 8), (7, 8), (8, 8)] [.at (.dn 8) (.orig 0), .at (.up 8) (.orig 1), .at (.up 16) (.orig 2), .at (.up 32) "
                       "(.orig 3), .at (.dn 72) (.orig 4), .at (.dn 64) (.orig 5), .at (.dn 56) (.orig 6), .at (.dn 32) (.orig 7), "
                       ".at (.dn 80) (.orig 8), .lo (.orig 9)] (some ⟨true, 8, 9, 88⟩) 80 true [.n 24, .lo] [.at (.dn 8) (.reg "
                       ".rbp), .at (.up 8) (.reg .rax), .at (.up 16) (.reg .rbx), .at (.up 32) (.reg .rdi), .at (.dn 72) (.ex 0), "
                       ".at (.dn 32) (.ptr 2), .at (.dn 80) (.ret 131), .lo (.ex 1)] 72)"),
    "PowBlock": ("h6", "(Codec.DecLayout.mk [] 7 [(0, 8), (1, 8), (2, 8), (3, 24), (4, 8), (5, 8)] [.at (.dn 8) (.orig 0), "
                 ".at (.up 8) (.orig 1), .at (.up 16) (.orig 2), .at (.dn 40) (.orig 3), .at (.dn 16) (.orig 4), .at (.dn 48) "
                 "(.orig 5), .lo (.orig 6)] (some ⟨false, 0, 6, 48⟩) 0 false [.n 24, .lo] [.at (.dn 8) (.reg .rbp), .at (.up 8) "
                 "(.reg .rax), .at (.up 16) (.reg .rbx), .at (.dn 40) (.ex 0), .at (.dn 16) (.ptr 2), .at (.dn 48) (.ret 104), "
                 ".lo (.ex 1)] 40)"),
    "SyncCommitteeMessage": ("h5", "(Codec.DecLayout.mk [Prysm.AttestationData.Code.slotUnmarshalSSZ, Prysm.ValidatorIndex.Code.unmarshalSSZ] 12 [(0, 8), (1, 8), "
                             "(2, 8), (3, 8), (4, 8), (5, 8), (6, 8), (7, 8), (8, 8), (9, 8), (10, 8)] [.at (.dn 8) (.orig 0), .at "
                             "(.up 8) (.orig 1), .at (.up 16) (.orig 2), .at (.up 32) (.orig 3), .at (.dn 104) (.orig 4), .at (.dn "
                             "96) (.orig 5), .at (.dn 88) (.orig 6), .at (.dn 64) (.orig 7), .at (.dn 56) (.orig 8), .at (.dn 48) "
                             "(.orig 9), .at (.dn 112) (.orig 10), .lo (.orig 11)] (some ⟨true, 8, 11, 120⟩) 112 true [.n 24, .lo] "
                             "[.at (.dn 8) (.reg .rbp), .at (.up 8) (.reg .rax), .at (.up 16) (.reg .rbx), .at (.up 32) (.reg .rdi), "
                             ".at (.dn 104) (.ex 0), .at (.dn 64) .zero, .at (.dn 56) .zero, .at (.dn 48) (.ptr 1), .at (.dn 112) "
                             "(.ret 141), .lo (.ex 1)] 104)"),
}


def g5_inputs(tname, sdir):
    sp = f"prysm/go1.26.10/e2e/{sdir}/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.{tname}.UnmarshalSSZ.S"
    sraw, iraw = (KR / sp).read_bytes(), (KR / "prysm/ir/ir-mainnet.json").read_bytes()
    return sp, sraw, iraw


def g5_good_text():
    """A GEN5 file for VoluntaryExit in the generator's layout (theorem bodies abbreviated), with the kind
    parameters from the recomputation; header with the real input paths and sha256."""
    import hashlib
    sp, sraw, iraw = g5_inputs("VoluntaryExit", "h6")
    fields, sz = g5_ir(iraw.decode(), "v1alpha1.VoluntaryExit")
    E = g5_expect([l.strip() for l in sraw.decode("ascii").split("\n") if l.strip()], fields, sz)
    C, P, L, F = "Prysm.VoluntaryExit.Code.unmarshalSSZ", "Decode.generated", E["L"], E["fields"]

    def thm(t, body):
        return (f"set_option maxRecDepth 100000 in\ntheorem {t} : ∀ (k : Nat) (hk : {C}.IsInfixAt Host.prog k) "
                f"(hf : LabelsFresh {C} k),\n    T := by\n{body}\n")

    def kd(t, k, ds, proof="  intro h; rfl"):
        return (f"theorem {t}_kind : ∀ (h : Host), type_of% (@{t} h)\n    = @Codec.{k} h {C} {L} {F}"
                + "".join(f"\n    ⟨{E['pcs'][d]}, {d}, [], [], []⟩" for d in ds) + f" := by\n{proof}\n\n")
    n = len(E["pcs"]) - 1
    out = (f"import Prysm.PendingDeposit.Code\n\n/-! Generated by `gen/scal/scalgen.py p2dec` from `{sp}`\n(sha256 "
           f"`{hashlib.sha256(sraw).hexdigest()}`) and `prysm/ir/ir-mainnet.json` (sha256 `{hashlib.sha256(iraw).hexdigest()}`"
           f", type `v1alpha1.VoluntaryExit`); GEN4 coverage. -/\n\nnamespace Prysm.Fixture\nend Prysm.Fixture\n\n"
           f"{G5_MARK}, unit G5-G): text.\nGEN5-JSON: {{\"accept\": \"{P}_accept\"}}\n-/\n\nopen Codec\n\n"
           f"namespace Prysm.Fixture\n\n")
    out += thm(f"{P}_head", "  exact x") + kd(f"{P}_head", "decHeadKindN", [0])
    for i in range(n):
        out += thm(f"{P}_f{i + 1}", "  exact x") + kd(f"{P}_f{i + 1}", "decFieldKindN", [i, i + 1])
    out += thm(f"{P}_epi", "  exact x") + kd(f"{P}_epi", "decEpiKindN", [n])
    chain = (f"  refine eventually_trans _ _ _ _ ({P}_head a) ?_\n"
             + "".join(f"  refine eventually_trans _ _ _ _ ({P}_f{i + 1} a) ?_\n" for i in range(n)) + f"  exact {P}_epi a")
    out += thm(f"{P}_accept", chain) + kd(f"{P}_accept", "decAcceptKindN", [])
    out += (f"set_option maxRecDepth 100000 in\ntheorem {P}_reject : ∀ (k : Nat) (hk : {C}.IsInfixAt Host.prog k) (hf : "
            f"LabelsFresh {C} k),\n    T := by\n  exact y\ntheorem {P}_reject_kind : ∀ (h : Host), type_of% (@{P}_reject h)\n"
            f"    = @Codec.decRejectKindN h {C} {E['sz']} := by\n  intro h; with_reducible rfl\n\n")
    return out + "end Prysm.Fixture\n"


def g5_cases():
    """Rule 12 controls: (id, text, expect PASS)."""
    G = g5_good_text()
    P = "Decode.generated"
    stmt = G.replace(f"intro h; rfl\n\nset_option maxRecDepth 100000 in\ntheorem {P}_reject ",
                     f"intro h; rfl\n\ntheorem {P}_accept_stmt : Prysm.VoluntaryExit.Decode.hand_statement := {P}_accept\n\n"
                     f"set_option maxRecDepth 100000 in\ntheorem {P}_reject ", 1)
    same = G.replace(f"intro h; rfl\n\nset_option maxRecDepth 100000 in\ntheorem {P}_reject ",
                     f"intro h; rfl\n\ntheorem {P}_accept_same : ∀ (h : Host), type_of% (@{P}_accept h) = type_of% "
                     f"(@Prysm.VoluntaryExit.Decode.hand_accept h) := by\n  intro h; rfl\n\nset_option maxRecDepth 100000 in\ntheorem "
                     f"{P}_reject ", 1)
    assert stmt != G and same != G
    acc_k = f"theorem {P}_accept_kind : ∀ (h : Host), type_of% (@{P}_accept h)"
    return [
        ("g5_good", G, True),
        ("g5_good_stmt", stmt, True),
        ("g5_good_same", same, True),
        ("g5_accept_kind_missing", G.replace(acc_k, acc_k.replace("_accept_kind", "_accept_kinx")), False),
        ("g5_field_kind_missing", G.replace(f"theorem {P}_f2_kind ", f"theorem {P}_f2_kinx "), False),
        ("g5_reject_missing", G.split("set_option maxRecDepth 100000 in\ntheorem Decode.generated_reject ")[0] + "end Prysm.Fixture\n",
         False),
        ("g5_extra_theorem", G.replace("end Prysm.Fixture\n", "theorem extra : True := trivial\n\nend Prysm.Fixture\n")[::-1].replace(
            "end Prysm.Fixture\n"[::-1], "", 0)[::-1], False),
        ("g5_kind_name_swapped", G.replace("= @Codec.decEpiKindN h", "= @Codec.decFieldKindN h", 1), False),
        ("g5_kind_proof_not_rfl", G.replace("intro h; rfl\n\nset_option maxRecDepth 100000 in\ntheorem Decode.generated_f1 ",
                                            "intro h; simp\n\nset_option maxRecDepth 100000 in\ntheorem Decode.generated_f1 ", 1), False),
        ("g5_L_frame_wrong", G.replace("(.ex 1)] 80)", "(.ex 1)] 88)"), False),
        ("g5_L_gd_wrong", G.replace("(none) 88 true", "(none) 80 true"), False),
        ("g5_L_callee_order", G.replace("[Prysm.Epoch.Code.unmarshalSSZ, Prysm.ValidatorIndex.Code.unmarshalSSZ]", "[Prysm.ValidatorIndex.Code.unmarshalSSZ, "
                                        "Prysm.Epoch.Code.unmarshalSSZ]"), False),
        ("g5_L_post_ret", G.replace("(.ret 56)", "(.ret 55)"), False),
        ("g5_L_slot_dropped", G.replace(".at (.up 32) (.orig 3), ", ""), False),
        ("g5_fields_kind", G.replace("[.u64, .u64]", "[.u64, .bytes 32]"), False),
        ("g5_fields_extra", G.replace("[.u64, .u64]", "[.u64, .u64, .u64]"), False),
        ("g5_pc_wrong", G.replace("⟨48, 1, ", "⟨47, 1, "), False),
        ("g5_done_wrong", G.replace("⟨48, 1, ", "⟨48, 2, "), False),
        ("g5_reject_size", G.replace("decRejectKindN h Prysm.VoluntaryExit.Code.unmarshalSSZ 16 ", "decRejectKindN h Prysm.VoluntaryExit.Code.unmarshalSSZ 24 "), False),
        ("g5_reject_proof", G.replace("intro h; with_reducible rfl", "intro h; rfl"), False),
        ("g5_const_other", G.replace("decAcceptKindN h Prysm.VoluntaryExit.Code.unmarshalSSZ", "decAcceptKindN h Prysm.PendingConsolidation.Code.unmarshalSSZ"), False),
        ("g5_hk_other", G.replace(f"theorem {P}_epi : ∀ (k : Nat) (hk : Prysm.VoluntaryExit.Code.unmarshalSSZ", f"theorem {P}_epi : ∀ (k : Nat) (hk : Prysm.PendingConsolidation.Code.unmarshalSSZ"),
         False),
        ("g5_chain_skips_field", G.replace(f"  refine eventually_trans _ _ _ _ ({P}_f1 a) ?_\n", ""), False),
        ("g5_stmt_generated", stmt.replace("Prysm.VoluntaryExit.Decode.hand_statement", "Prysm.VoluntaryExit.Decode.generated_step_s15"), False),
        ("g5_same_self", same.replace("(@Prysm.VoluntaryExit.Decode.hand_accept h)", "(@Prysm.VoluntaryExit.Decode.example_accept h)"), False),
        ("g5_sorry", G.replace("  exact y\n", "  sorry\n"), False),
        ("g5_local_def", G.replace("namespace Prysm.Fixture\n\nset_option", "namespace Prysm.Fixture\n\ndef q := 1\n\nset_option"),
         False),
        ("g5_sha_wrong", G.replace("(sha256 `" + G.split("(sha256 `")[1][:64], "(sha256 `" + (
            "0" if G.split("(sha256 `")[1][0] != "0" else "1") + G.split("(sha256 `")[1][1:64], 1), False),
        ("g5_two_blocks", G.replace("end Prysm.Fixture\n\n" + G5_MARK, "end Prysm.Fixture\n\n" + G5_MARK + " x -/\n" + G5_MARK, 1),
         False),
    ]


def g5_selftest():
    """Rule 12 controls + the recomputation against the hand layouts + an IR mutant. Returns (n, bad)."""
    import json
    bad = []
    cs = g5_cases()
    for name, text, ok in cs:
        errs, _ = check_gen5(text, GNAMES | {"Prysm.VoluntaryExit.Decode.example_accept"})
        if (not errs) != ok:
            bad.append((name, errs[:3]))
    n = len(cs)
    for tname, (sdir, Lh) in G5_HAND.items():
        sp, sraw, iraw = g5_inputs(tname, sdir)
        fields, sz = g5_ir(iraw.decode(), "v1alpha1." + tname)
        E = g5_expect([l.strip() for l in sraw.decode("ascii").split("\n") if l.strip()], fields, sz)
        n += 1
        if " ".join(E["L"].split()) != " ".join(Lh.split()):
            bad.append((f"g5_recompute_{tname}", E["L"], Lh))
    # an IR mutant: VoluntaryExit ValidatorIndex Go offset 24 (code 16) -> the recomputation refuses
    sp, sraw, iraw = g5_inputs("VoluntaryExit", "h6")
    d = json.loads(iraw)
    for c in d["configs"]:
        for t in c.get("types", []):
            if t.get("name") == "VoluntaryExit":
                for f in t["go_fields"]:
                    if f["name"] == "ValidatorIndex":
                        f["offset_gc_amd64"] = 24
    n += 1
    try:
        fields, sz = g5_ir(json.dumps(d), "v1alpha1.VoluntaryExit")
        g5_expect([l.strip() for l in sraw.decode("ascii").split("\n") if l.strip()], fields, sz)
        bad.append(("g5_ir_goff_mutant", "not refused"))
    except G5Mismatch:
        pass
    # the code mutated: the Epoch call replaced by a ValidatorIndex call -> the recomputation refuses (no open field)
    n += 1
    try:
        dirs = [l.strip().replace("Epoch.UnmarshalSSZ", "ValidatorIndex.UnmarshalSSZ") for l in sraw.decode("ascii").split("\n")
                if l.strip()]
        fields, sz = g5_ir(iraw.decode(), "v1alpha1.VoluntaryExit")
        E = g5_expect(dirs, fields, sz)
        if E["L"] == G5_HAND["VoluntaryExit"][1]:
            bad.append(("g5_code_callee_mutant", "same layout"))
    except G5Mismatch:
        pass
    return n, bad


# ---------------------------------------------------------------- rule 13: GEN6 (`scalgen.py p2enc --gen6`)
# A GEN6 file (header `GEN6-JSON:`, or any of the four encoder kinds) is checked by rule 13 ONLY (it has a `def` of its
# layout, which rule 2 forbids for the older files):
#  13a. (Removed: a git-blob pin of the kind and lemma modules of the encoder lemma unit's hand-over.)
#  13b. Structure: top-level lines as rule 2 plus exactly one `def <P>_layout : EncLayout where` (none when a hand
#       layout of GEN6_HAND is named); no banned token (rule 3, comments and strings removed); the theorems are exactly
#       P_head, P_f0 … P_f(n-1), P_epi, P_fast, each followed by its `_kind` (encHeadKindN / encFieldKindN /
#       encEpiKindN / encFastKindN), and optionally P_stmt; every theorem's `hk` binder names the same code constant C;
#       `set_option` only `maxHeartbeats 4000000` / `maxRecDepth 100000`; every kind proof is `  intro h; rfl`.
#  13c. RECOMPUTATION (an own interpreter, it does not import the generator): from the `.S` and the IR named in
#       GEN6-JSON (sha256 checked) this program recomputes the fields list, the layout (st, frame, gd, rt, nstk, lens,
#       pre, exs, post) and every boundary state (pc, done, live registers, stack slots, existential sizes); every
#       kind line must equal, as whole normalised text, the line rendered from the recomputation. A hand layout name
#       (GEN6_HAND, in `Prysm/BeaconBlockHeader/EncodeFastPathKindInstances.lean`) is accepted only if its def equals the recomputation in its own
#       chunk order. C is bound to the `.S`: an imported code module of the file must define
#       `def C : Program := include_x64_rt "../<S of GEN6-JSON>"`.
#  13d. P_fast's proof uses P_head, every P_fi and P_epi exactly once.
#  13e. P_stmt, if present, is `theorem P_stmt : type_of% (@X ‹Host›) :=` + `  [V ]P_fast` with X not generated and V
#       empty or in GEN6_VIA, or `theorem P_stmt : X :=` + `  P_fast` (hand Prop).
# Limits: the kind fixes the statement only up to what the kind reads (`hcap63` is a fixed premise; an extra
# chunk in L.pre would be a stronger premise, and the recomputation would reject it); that the code walk is the
# function's whole fast path is the generator's claim, checked by the proofs, not here.
import hashlib as _g6hash
import json as _g6json

GEN6_KINDS = ("encHeadKindN", "encFieldKindN", "encEpiKindN", "encFastKindN")
GEN6_HAND = ("Prysm.BeaconBlockHeader.encodeLayout", "Prysm.Eth1Data.encodeLayout", "Prysm.Checkpoint.encodeLayout")
GEN6_VIA = ("Prysm.Checkpoint.Encode.fast_path_of_kind",)
G6_R64 = "rax rbx rcx rdx rsi rdi rsp rbp r8 r9 r10 r11 r12 r13 r14 r15".split()
G6_R32 = dict(eax="rax", ebx="rbx", ecx="rcx", edx="rdx", esi="rsi", edi="rdi")
G6_LAYF = ("st", "frame", "gd", "rt", "nstk", "lens", "pre", "exs", "post")


class G6Mismatch(Exception):
    pass


def g6_ir(ir_text, tname):
    """(fields [('u'|'b', size)], go offsets, ssz size) from the Go field list of the IR (exported fields)."""
    pkg, name = tname.rsplit(".", 1)
    hits = []
    for c in _g6json.loads(ir_text)["configs"]:
        for t in c.get("types", []):
            if t.get("name") == name and t.get("package", "").endswith("/" + pkg):
                hits.append(t)
    if len(hits) != 1:
        raise G6Mismatch(f"{len(hits)} IR entries for {tname}")
    fs, goffs = [], []
    for f in hits[0]["go_fields"]:
        if not f["exported"]:
            continue
        m = re.search(r'ssz-size:"(\d+)"', f["tag"])
        if m and f["type"] == "[]byte":
            fs.append(("b", int(m.group(1))))
        elif not m and f["size_gc_amd64"] == 8:
            fs.append(("u", 8))
        else:
            raise G6Mismatch(f"field {f['name']}: not a byte vector or an 8-byte scalar")
        goffs.append(f["offset_gc_amd64"])
    want = 8 if goffs and goffs[0] == 8 else 0
    for (k, n), g in zip(fs, goffs):
        if g != want:
            raise G6Mismatch(f"Go offset {g}, running sum {want}")
        want += 24 if k == "b" else 8
    return fs, goffs, sum(n for _, n in fs)


def g6_regs_of(text):
    """64-bit register names in an operand text (32-bit names mapped)."""
    out = []
    for r in re.findall(r"%([a-z0-9]+)", text):
        r = G6_R32.get(r, r)
        if r in G6_R64:
            out.append(r)
    return out


def g6_usedef(d):
    """(uses, defs, end) of one directive by operand position (AT&T: `op src, dst`)."""
    if d.endswith(":") or d == "nop":
        return [], [], False
    if d.startswith("callq "):
        return ["rax", "rbx", "rcx"], [], True
    if d == "pop %rbp":
        return ["rax", "rbx", "rcx", "rdi", "rsi"], [], True
    op, _, args = d.partition(" ")
    if op.startswith("j"):
        return [], [], False
    # split at the top-level comma
    depth, cut = 0, -1
    for i, ch in enumerate(args):
        depth += ch == "("
        depth -= ch == ")"
        if ch == "," and depth == 0:
            cut = i
    src, dst = (args[:cut], args[cut + 1:]) if cut >= 0 else (args, "")
    sr, dr = g6_regs_of(src), g6_regs_of(dst)
    dst_is_reg = dst.startswith("%")
    if op == "xor" and src == dst:
        return [], dr, False
    if op in ("mov", "lea") and dst_is_reg:
        return sr, dr, False
    if op in ("add", "sub") and dst_is_reg:
        return sr + dr, dr, False
    if op in ("mov", "cmp", "cmpq", "movups"):
        return sr + dr, [], False
    raise G6Mismatch(f"no use / def rule for `{d}`")


def g6_expect(dirs, fs, goffs, size, hand_pre=None):
    """Own interpreter of the fast path. Returns dict(L={field: text}, fields=text, states=[EncSt text], pcs=[...])."""
    lab = {d[:-1]: i for i, d in enumerate(dirs) if d.endswith(":")}
    st = bool(goffs) and goffs[0] == 8
    soffs = [sum(n for _, n in fs[:i]) for i in range(len(fs))]
    if dirs[2] == "cmp 0x10(%r14),%rsp":
        gd, j = 0, 3
    else:
        m = re.fullmatch(r"lea -0x([0-9a-f]+)\(%rsp\),%r12", dirs[2])
        if not m or dirs[3] != "cmp 0x10(%r14),%r12":
            raise G6Mismatch("prologue")
        gd, j = int(m.group(1), 16), 4
    if not (dirs[j].startswith("jbe ") and dirs[j + 1] == "push %rbp" and dirs[j + 2] == "mov %rsp,%rbp"):
        raise G6Mismatch("prologue")
    a = dirs[j + 3]
    m1, m2 = re.fullmatch(r"sub \$0x([0-9a-f]+),%rsp", a), re.fullmatch(r"add \$-0x([0-9a-f]+),%rsp", a)
    if not (m1 or m2):
        raise G6Mismatch("frame")
    F = int((m1 or m2).group(1), 16)
    SP = -(F + 8)
    RS = -(F + 16)
    pc = j + 4
    R = {"rax": "rcv", "rbx": "ptr", "rcx": ("len", 0), "rdi": "cap", "rsp": ("stk", SP)}
    # stack: off -> [size, value]; values: "rbp", ("e", reg), ("len", n), ("fld", i), ("z", seq, part), ("ret", n)
    M = {-8: [8, "rbp"]}
    first = [-8]
    firstsz = {-8: 8}
    seq = [0]
    scratch = ["scr"]   # "scr" (before any call) or ("z", seq, "lo")
    done = [0]
    states = []
    regsets = []

    def disp(x):
        return int(x, 16) if x else 0

    def addr(base, dsp):
        v = R.get(base)
        if isinstance(v, tuple) and v[0] == "stk":
            return ("stk", v[1] + dsp)
        if v == "rcv":
            return ("rcv", dsp)
        raise G6Mismatch(f"address base {base}={v}")

    def region(off, n):
        for o in list(M):
            if o <= off and off + n <= o + M[o][0]:
                return o
            if not (off + n <= o or o + M[o][0] <= off):
                raise G6Mismatch("overlap")
        M[off] = [n, "orig"]
        first.append(off)
        firstsz[off] = n
        return off

    def live(p):
        need, wr = [], set()
        for _ in range(3000):
            d = dirs[p]
            u, df, end = g6_usedef(d)
            for r in u:
                if r not in wr and r not in need and r not in ("rsp", "rbp", "r14"):
                    need.append(r)
            if end:
                return [r for r in G6_R64 if r in need]
            wr.update(df)
            if d.startswith("jae ") or d.startswith("jmp "):
                p = lab[d.split()[1]]
            else:
                p += 1
        raise G6Mismatch("liveness")

    def snap(p):
        regs = []
        for r in live(p):
            v = R.get(r)
            if v in ("rcv", "ptr", "cap"):
                regs.append((r, "." + v))
            elif isinstance(v, tuple) and v[0] == "len":
                regs.append((r, f".len {v[1]}"))
            else:
                raise G6Mismatch(f"live {r}={v}")
        return p, done[0], regs, {o: list(v) for o, v in M.items()}, scratch[0]

    # head spills
    while True:
        m = re.fullmatch(r"mov %(r\w+),(0x[0-9a-f]+)\(%rsp\)", dirs[pc])
        if not (m and int(m.group(2), 16) > F + 8):
            break
        off = SP + int(m.group(2), 16)
        region(off, 8)
        v = R[m.group(1)]
        M[off][1] = ("e", {"rcv": "rax", "ptr": "rbx", "cap": "rdi"}[v]) if v in ("rcv", "ptr", "cap") else \
            (("e", "rcx") if v == ("len", 0) else None)
        if M[off][1] is None:
            raise G6Mismatch("spill value")
        pc += 1
    states.append(snap(pc))
    for _ in range(3000):
        d = dirs[pc]
        if d == "nop" or d.endswith(":"):
            pc += 1
            continue
        if d == "pop %rbp":
            break
        m = re.fullmatch(r"(mov|lea) (-?0x[0-9a-f]+)?\(%(\w+)\),%(\w+)", d)
        if m:
            op, dsp, b, dst = m.group(1), disp(m.group(2)), m.group(3), m.group(4)
            if op == "lea":
                v = R.get(b)
                R[dst] = ("len", v[1] + dsp) if isinstance(v, tuple) and v[0] == "len" else \
                    ("stk", v[1] + dsp) if isinstance(v, tuple) and v[0] == "stk" else None
                if R[dst] is None:
                    raise G6Mismatch("lea")
            else:
                ad = addr(b, dsp)
                if ad[0] == "rcv":
                    i = goffs.index(ad[1])
                    R[dst] = ("fv", i) if fs[i][0] == "u" else ("fp", i)
                else:
                    sv = M[ad[1]][1]
                    R[dst] = {"rax": "rcv", "rbx": "ptr", "rdi": "cap", "rcx": ("len", 0)}[sv[1]] if sv[0] == "e" else \
                        ("len", sv[1]) if sv[0] == "len" else ("fv", sv[1]) if sv[0] == "fld" else None
                    if R[dst] is None:
                        raise G6Mismatch("stack load")
            pc += 1
            continue
        m = re.fullmatch(r"mov %(\w+),(-?0x[0-9a-f]+)?\(%(\w+)\)", d)
        if m:
            v, ad = R[m.group(1)], addr(m.group(3), disp(m.group(2)))
            off = ad[1]
            if ad[0] != "stk":
                raise G6Mismatch("store base")
            if off not in M or M[off][0] != 8:
                o = region(off, 8)
                if o != off:   # 8-byte store into the low half of a 16-byte zeroed chunk: split in place
                    raise G6Mismatch("store inside a chunk not at its start")
                if M[off][0] == 16:
                    z = M[off][1]
                    M[off] = [8, ("z", z[1], "lo")]
                    M[off + 8] = [8, ("z", z[1], "hi")]
            M[off][1] = ("e", {"rcv": "rax", "ptr": "rbx", "cap": "rdi"}[v]) if v in ("rcv", "ptr", "cap") else \
                ("e", "rcx") if v == ("len", 0) else ("len", v[1]) if v[0] == "len" else ("fld", v[1]) if v[0] == "fv" else None
            if M[off][1] is None:
                raise G6Mismatch("stored value")
            pc += 1
            continue
        m = re.fullmatch(r"movups %xmm15,(-?0x[0-9a-f]+)?\(%(\w+)\)", d)
        if m:
            off = addr(m.group(2), disp(m.group(1)))[1]
            region(off, 16)
            seq[0] += 1
            M[off][1] = ("z", seq[0], "full")
            pc += 1
            continue
        m = re.fullmatch(r"mov %(r\w+),%(r\w+)", d)
        if m:
            R[m.group(2)] = R[m.group(1)]
            pc += 1
            continue
        m = re.fullmatch(r"mov \$0x([0-9a-f]+),%(e\w+)", d)
        if m:
            R[G6_R32[m.group(2)]] = ("imm", int(m.group(1), 16))
            pc += 1
            continue
        m = re.fullmatch(r"xor %(e\w+),%\1", d)
        if m:
            R[G6_R32[m.group(1)]] = ("imm", 0)
            pc += 1
            continue
        m = re.fullmatch(r"(add|sub) \$(-?0x[0-9a-f]+),%(\w+)", d)
        if m:
            v, k = R[m.group(3)], disp(m.group(2)) * (1 if m.group(1) == "add" else -1)
            R[m.group(3)] = (v[0], v[1] + k)
            pc += 1
            continue
        m = re.fullmatch(r"(?:lea \(%(\w+),%(\w+),1\),%(\w+)|add %(\w+),%(\w+))", d)
        if m:
            x, y, dst = (m.group(1), m.group(2), m.group(3)) if m.group(3) else (m.group(4), m.group(5), m.group(5))
            vs = [R[x], R[y]]
            ln = [v for v in vs if isinstance(v, tuple) and v[0] == "len"]
            if not ("ptr" in vs and len(ln) == 1):
                raise G6Mismatch("dst address")
            R[dst] = ("dst", ln[0][1])
            pc += 1
            continue
        m = re.fullmatch(r"sub %rsp,%(\w+)", d)
        if m:
            v = R[m.group(1)]
            R[m.group(1)] = ("pfr",) if v == "ptr" else ("imm", v[1] - SP)
            pc += 1
            continue
        m = re.fullmatch(r"mov %(\w+),(-?0x[0-9a-f]+)?\(%(\w+),%(\w+),1\)", d)
        if m:
            i = done[0]
            vs = [R[m.group(3)], R[m.group(4)]]
            ln = [v for v in vs if isinstance(v, tuple) and v[0] == "len"]
            if not ("ptr" in vs and ln and ln[0][1] + disp(m.group(2)) == soffs[i] and R[m.group(1)] == ("fv", i)):
                raise G6Mismatch("output store")
            done[0] += 1
            pc += 1
            states.append(snap(pc))
            continue
        m = re.fullmatch(r"cmpq \$0x[0-9a-f]+,(-?0x[0-9a-f]+)?\(%\w+\)", d)
        if m:
            q = pc + 1
            while dirs[q] == "nop":
                q += 1
            if not dirs[q].startswith("jne "):
                raise G6Mismatch("length test")
            pc = q + 1
            continue
        m = re.fullmatch(r"cmp %(\w+),%(\w+)", d)
        if m:
            q = pc + 1
            while dirs[q] == "nop":
                q += 1
            jop, tgt = dirs[q].split()
            if jop == "jae":
                pc = lab[tgt]
            elif jop == "jb":
                pc = q + 1
            else:
                raise G6Mismatch("compare")
            continue
        m = re.fullmatch(r"jmp (\S+)", d)
        if m:
            pc = lab[m.group(1)]
            continue
        if d == "callq runtime.memmove":
            i = done[0]
            if not (R.get("rax") == ("dst", soffs[i]) and R.get("rbx") == ("fp", i) and R.get("rcx") == ("imm", fs[i][1])):
                raise G6Mismatch("memmove arguments")
            region(RS, 8)
            M[RS][1] = ("ret", pc + 1)
            if scratch[0] == "scr":
                seq[0] += 1
                scratch[0] = ("z", seq[0], "lo")
            R.clear()
            R["rsp"] = ("stk", SP)
            done[0] += 1
            pc += 1
            states.append(snap(pc))
            continue
        raise G6Mismatch(f"directive {pc} `{d}`")
    else:
        raise G6Mismatch("no return")
    if done[0] != len(fs):
        raise G6Mismatch("fields")
    rt = RS in M
    if hand_pre is not None:
        mem = [o for o, _ in hand_pre]
        if sorted(mem) != sorted(first) or sorted(b for _, b in hand_pre) != list(range(len(mem))):
            raise G6Mismatch("hand layout chunks differ from the recomputed regions")
        bindex = dict(hand_pre)
    else:
        mem = [-8] + sorted(o for o in first if o > 0) + [o for o in first if o < 0 and o not in (-8, RS)] + \
            ([RS] if rt else [])
        bindex = {o: i for i, o in enumerate(mem)}

    def exnum(Ms, scr):
        keys = []
        for o, (n, v) in Ms.items():
            if isinstance(v, tuple) and v[0] == "z":
                keys.append((v[1], o, 16 if v[2] == "full" else 8))
        if isinstance(scr, tuple):
            keys.append((scr[1], 10 ** 9, "S"))
        keys.sort()
        return {(k[0], k[1]): i for i, k in enumerate(keys)}, [k[2] for k in keys]

    def vk(o, v, num):
        if v == "orig":
            return f".orig {bindex[o]}"
        if v == "rbp":
            return ".reg .rbp"
        if v[0] == "e":
            return f".reg .{v[1]}"
        if v[0] in ("len", "fld", "ret"):
            return f".{v[0]} {v[1]}"
        if v[0] == "z":
            return f".ex {num[(v[1], o)]}"
        raise G6Mismatch(f"slot value {v}")

    def slots(Ms, scr):
        num, ex = exnum(Ms, scr)
        out = []
        for o in mem:
            if o not in Ms:
                out.append(f".at (.{'up' if o > 0 else 'dn'} {abs(o)}) (.orig {bindex[o]})")
                continue
            parts = [o] if Ms[o][0] == firstsz[o] else [o, o + 8]
            for p in parts:
                out.append(f".at (.{'up' if p > 0 else 'dn'} {abs(p)}) ({vk(p, Ms[p][1], num)})")
        if rt:
            out.append(".lo .scr" if scr == "scr" else f".lo (.ex {num[(scr[1], 10 ** 9)]})")
        return "[" + ", ".join(out) + "]", "[" + ", ".join(".lo" if e == "S" else f".n {e}" for e in ex) + "]"

    def norm_pre():
        out = [f".at (.{'up' if o > 0 else 'dn'} {abs(o)}) (.orig {bindex[o]})" for o in mem]
        return "[" + ", ".join(out + ([".lo .scr"] if rt else [])) + "]"
    post, exs = slots(M, scratch[0])
    L = dict(st=str(st).lower(), frame=str(F), gd=str(gd), rt=str(rt).lower(), nstk=str(len(mem)),
             lens="[" + ", ".join(f"({i}, {firstsz[o]})" for i, o in sorted((bindex[o], o) for o in mem)) + "]",
             pre=norm_pre(), exs=exs, post=post)
    sts = []
    for p, dn, regs, Ms, scr in states:
        sl, ex = slots(Ms, scr)
        rg = "[" + ", ".join(f"(.{r}, {k})" for r, k in regs) + "]"
        sts.append(f"⟨{p}, {dn}, {rg}, {sl}, {ex}⟩")
    fields = "[" + ", ".join(".u64" if k == "u" else f".bytes {n}" for k, n in fs) + "]"
    return dict(L=L, fields=fields, states=sts, pcs=[x[0] for x in states], size=size)


def g6_layout_def(text, short, full=None):
    """{field: normalised value} of `def <short> : EncLayout where` in a Lean text, or None. With `full`, a declaring line
    `def _root_.<full>` (a layout of another type than the namespace block of the module) comes first, then the
    name relative to the type namespace `Prysm.<T>`."""
    m = None
    for d in ([f"_root_.{full}", full.split(".", 2)[2]] if full and full.count(".") >= 2 else []) + [short]:
        m = m or re.search(rf"(?m)^def {re.escape(d)} : EncLayout where\n((?:  .*\n?)+)", text)
    if not m:
        return None
    flds, cur = {}, None
    for l in m.group(1).split("\n"):
        mm = re.match(r"  (\w+) := (.*)", l)
        if mm:
            cur = mm.group(1)
            flds[cur] = mm.group(2)
        elif l.startswith("    ") and cur:
            flds[cur] += " " + l.strip()
    return {k: " ".join(v.split()) for k, v in flds.items()}


def g6_norm(s):
    return " ".join(s.split())


def check_gen6(text, gnames=frozenset(), kr=None):
    """Rule 13. Returns (errors, info)."""
    kr = kr or KR
    errs, info = [], "gen6"
    lines = text.split("\n")
    gj = [l for l in lines if l.startswith("GEN6-JSON: ")]
    try:
        if len(gj) != 1:
            raise ValueError(f"{len(gj)} GEN6-JSON lines")
        J = _g6json.loads(gj[0][len("GEN6-JSON: "):])
        P, C, S, IR, TY, LAY = (J["prefix"], J["const"], J["S"], J["ir"], J["ir_type"], J["layout"])
        if not (re.fullmatch(r"(?:[A-Z][A-Za-z0-9]*\.)?[a-z][a-z0-9_]*", P) and re.fullmatch(r"[A-Za-z][A-Za-z0-9]*", C)):
            raise ValueError("prefix / const")
    except Exception as e:
        return errs + [f"rule 13: no single valid GEN6-JSON line ({e})"], info
    info = f"{P}_fast"
    # 13b structure
    body = strip_strings(strip_comments(text))
    if BANNED.search(body):
        errs.append("rule 13b: banned token")
    hand = LAY in GEN6_HAND
    if not hand and LAY != f"Prysm.{J['type']}.{P}_layout":
        errs.append(f"rule 13b: layout name {LAY} is neither a pinned hand layout nor {P}_layout of this file")
    ndef = 0
    in_def = False
    for l in body.split("\n"):
        if re.match(r"^def ", l):
            ndef += 1
            in_def = True
            if l != f"def {P}_layout : EncLayout where" or hand:
                errs.append(f"rule 13b: top-level `{l[:60]}`")
            continue
        if in_def and l.startswith("  "):
            if not re.match(r"  (st|frame|gd|rt|nstk|lens|pre|exs|post) := |    \S", l):
                errs.append(f"rule 13b: layout line `{l[:60]}`")
            continue
        in_def = False
        if l and not l[0].isspace():
            if not TOP_OK.match(l):
                errs.append(f"rule 13b: top-level `{l[:60]}`")
            if l.startswith("set_option ") and l not in ("set_option maxHeartbeats 4000000 in",
                                                       "set_option maxRecDepth 100000 in"):
                errs.append(f"rule 13b: `{l}`")
            if l.startswith("namespace ") and l != f"namespace Prysm.{J['type']}":
                errs.append(f"rule 13b: `{l}`")
    if ndef != (0 if hand else 1):
        errs.append(f"rule 13b: {ndef} layout defs (expected {0 if hand else 1})")
    thms = [m.group(1) for m in re.finditer(r"(?m)^theorem (\S+)", body)]
    n = None
    try:
        tsha = lambda p: _g6hash.sha256((kr / p).read_bytes()).hexdigest()
        if tsha(S) != J["S_sha256"] or tsha(IR) != J["ir_sha256"]:
            raise G6Mismatch("sha256 of the .S or the IR differs from GEN6-JSON")
        fs, goffs, size = g6_ir((kr / IR).read_text(), TY)
        n = len(fs)
        hand_pre, handdef = None, None
        if hand:
            ht = (kr / "lean/Prysm/BeaconBlockHeader/EncodeFastPathKindInstances.lean").read_text()
            handdef = g6_layout_def(ht, LAY.split(".")[-1], LAY)
            if handdef is None:
                raise G6Mismatch(f"hand layout {LAY} not in EncTies.lean")
            hand_pre = [(int(k) * (1 if d == "up" else -1), int(i)) for d, k, i in
                        re.findall(r"\.at \(\.(up|dn) (\d+)\) \(\.orig (\d+)\)", handdef["pre"])]
        dirs = [l.strip() for l in (kr / S).read_text().split("\n") if l.strip()]
        X = g6_expect(dirs, fs, goffs, size, hand_pre)
    except Exception as e:
        return errs + [f"rule 13c: recomputation refused: {type(e).__name__}: {e}"], info
    want = [f"{P}_head", f"{P}_head_kind"] + [x for i in range(n) for x in (f"{P}_f{i}", f"{P}_f{i}_kind")] + \
        [f"{P}_epi", f"{P}_epi_kind", f"{P}_fast", f"{P}_fast_kind"]
    if thms not in (want, want + [f"{P}_stmt"]):
        return errs + [f"rule 13b: theorems {thms}, expected {want} [+ {P}_stmt]"], info
    # 13c: layout
    fileL = handdef if hand else g6_layout_def(body, f"{P}_layout")
    if fileL is None:
        errs.append("rule 13c: no layout def")
    else:
        for k in G6_LAYF:
            if fileL.get(k) != X["L"][k]:
                errs.append(f"rule 13c: layout {k} = {fileL.get(k)!r}, recomputed {X['L'][k]!r}")
        if set(fileL) != set(G6_LAYF):
            errs.append(f"rule 13c: layout fields {sorted(fileL)}")
    # 13b / 13c: kind lines, as whole normalised text
    starts = {m.group(1): m.start() for m in re.finditer(r"(?m)^theorem (\S+)", body)}
    order = sorted(starts.items(), key=lambda kv: kv[1])
    chunk = {}
    for i, (nm, st_) in enumerate(order):
        chunk[nm] = body[st_: order[i + 1][1] if i + 1 < len(order) else len(body)]
    S0 = X["states"]
    if len(S0) != n + 1:
        errs.append(f"rule 13c: {len(S0)} boundary states for {n} fields")
        return errs, info
    exp = {f"{P}_head": ("encHeadKindN", " " + S0[0])}
    for i in range(n):
        exp[f"{P}_f{i}"] = ("encFieldKindN", " " + S0[i] + " " + S0[i + 1])
    exp[f"{P}_epi"] = ("encEpiKindN", " " + S0[n])
    exp[f"{P}_fast"] = ("encFastKindN", "")
    for t, (kind, sts) in exp.items():
        k = chunk[f"{t}_kind"]
        hdr, sep, rest = k.partition(":= by\n")
        line = (f"theorem {t}_kind : ∀ (h : Host), type_of% (@{t} h) = @Codec.{kind} h {C} {LAY} {X['fields']}{sts}")
        rl = rest.split("\n")
        tail_ok = all(x.strip() in ("", f"end Prysm.{J['type']}") or x.startswith("set_option ") for x in rl[1:])
        if g6_norm(hdr) != g6_norm(line) or rl[0] != "  intro h; rfl" or not tail_ok or not sep:
            errs.append(f"rule 13c: {t}_kind differs from the recomputation\n      file:       {g6_norm(hdr)}\n"
                        f"      recomputed: {g6_norm(line)}")
        hk = HK.search(chunk[t].split("\n")[0])
        if not hk or hk.group(1) != C:
            errs.append(f"rule 13b: {t}: `hk` binder does not name {C}")
        if t != f"{P}_fast" and not chunk[t].startswith(f"theorem {t} : ∀ (k : Nat) (hk : {C}.IsInfixAt Host.prog k)"):
            errs.append(f"rule 13b: {t}: first binder line")
    # 13c: C is the code of the .S
    bound = False
    for imp in re.findall(r"(?m)^import (\S+)$", text):
        f = kr / "lean" / (imp.replace(".", "/") + ".lean")
        # the code module of several types declares the constants of the other types root-qualified
        if f.exists() and any(f'def {d} : Program := include_x64_rt "../{S}"' in f.read_text()
                              for d in (C, f"Code.{C}", f"_root_.Prysm.{J['type']}.Code.{C}")):
            bound = True
    if not bound:
        errs.append(f"rule 13c: no imported code module defines `{C}` from `{S}`")
    # 13d: chaining
    fp = chunk[f"{P}_fast"]
    for t in [f"({P}_head ", *[f"({P}_f{i} " for i in range(n)], f"exact {P}_epi "]:
        if fp.count(t) != 1:
            errs.append(f"rule 13d: the fast-path proof does not use `{t.strip('( ')}` exactly once")
    # 13e: identity
    if f"{P}_stmt" in chunk:
        c = chunk[f"{P}_stmt"].rstrip()
        if c.endswith(f"\nend Prysm.{J['type']}"):
            c = c[: -len(f"\nend Prysm.{J['type']}")].rstrip()
        m = re.fullmatch(rf"theorem {P}_stmt : type_of% \(@(\S+) ‹Host›\) :=\n  (?:(\S+) )?{P}_fast", c) or \
            re.fullmatch(rf"theorem {P}_stmt : (\S+) :=\n  {P}_fast()", c)
        if not m:
            errs.append(f"rule 13e: {P}_stmt: not the identity form")
        else:
            x, via = m.group(1), m.group(2)
            if GENNS.match(x) or x.split(".")[-1] in gnames:
                errs.append(f"rule 13e: {x} is a generated name")
            if via and via not in GEN6_VIA:
                errs.append(f"rule 13e: implication lemma {via} not in GEN6_VIA")
        info += f", identity {P}_stmt"
    return errs, info


# ---- rule 13 selftest controls: mutants of the committed raw GEN6 outputs (a missing file is a FAIL)
G6_SELFTEST = {"vb": "lean/Prysm/ValidatorBalance/GeneratedEncodeFastPath.lean", "cp": "lean/Prysm/Checkpoint/GeneratedEncodeFastPath.lean",
               "hs": "lean/Prysm/HistoricalSummary/GeneratedEncodeFastPath.lean", "bh": "lean/Prysm/BeaconBlockHeader/GeneratedEncodeFastPath.lean"}
# the lemma unit's own layouts (`Enc2Ex*.lean`, scratch emitter of the encoder lemma unit): the recomputation must give them too
G6_L_LAYOUTS = {"ValidatorBalance": ("lean/Prysm/ValidatorBalance/EncodeFastPathExample.lean", "Prysm.ValidatorBalance.Encode.example_layout"),
                "DepositMessage": ("lean/Prysm/DepositMessage/EncodeFastPathExample.lean", "Prysm.DepositMessage.Encode.example_layout"),
                "HistoricalSummary": ("lean/Prysm/HistoricalSummary/EncodeFastPathExample.lean", "Prysm.HistoricalSummary.Encode.example_layout")}


def g6_cases(T):
    """(name, text, ok) on the committed files T = {key: text}."""
    V, Cp, H, B = T["vb"], T["cp"], T["hs"], T["bh"]

    def r(t, a, b, n=1):
        if t.count(a) < n:
            raise G6Mismatch(f"selftest setup: `{a[:50]}` not found")
        return t.replace(a, b, n)
    sha = V.split('"S_sha256": "')[1][:64]
    return [
        ("g6_good_vb", V, True), ("g6_good_cp_hand_via", Cp, True), ("g6_good_hs_frametest", H, True),
        ("g6_good_bh_hand", B, True),
        ("g6_layout_frame", r(V, "  frame := 104\n", "  frame := 112\n"), False),
        ("g6_layout_gd", r(V, "  gd := 0\n", "  gd := 8\n"), False),
        ("g6_layout_pre_order", r(V, ".at (.dn 40) (.orig 2), .at (.dn 24) (.orig 3)]\n  exs",
                                  ".at (.dn 24) (.orig 3), .at (.dn 40) (.orig 2)]\n  exs"), False),
        ("g6_layout_exs", r(V, "  exs := [.n 8, .n 16]\n", "  exs := [.n 16, .n 8]\n"), False),
        ("g6_layout_post_fld", r(V, "(.fld 0), .at (.dn 32) (.ex 0), .at (.dn 24) (.ex 1)]\n\n",
                                 "(.fld 1), .at (.dn 32) (.ex 0), .at (.dn 24) (.ex 1)]\n\n"), False),
        ("g6_layout_lens", r(V, "(2, 16), (3, 16)]", "(2, 8), (3, 16)]"), False),
        ("g6_fields_param", r(V, "Encode.generated_f0 h)\n    = @Codec.encFieldKindN h marshalSSZTo Prysm.ValidatorBalance.Encode.generated_layout [.u64, .u64]",
                              "Encode.generated_f0 h)\n    = @Codec.encFieldKindN h marshalSSZTo Prysm.ValidatorBalance.Encode.generated_layout [.u64, .bytes 32]"),
         False),
        ("g6_boundary_pc", r(V, "[.u64, .u64]\n    ⟨8, 0,", "[.u64, .u64]\n    ⟨9, 0,"), False),
        ("g6_boundary_done", r(V, "[.u64, .u64]\n    ⟨8, 0,", "[.u64, .u64]\n    ⟨8, 1,"), False),
        ("g6_boundary_reg_dropped", r(V, "[.u64, .u64]\n    ⟨8, 0, [(.rax, .rcv), ", "[.u64, .u64]\n    ⟨8, 0, ["), False),
        ("g6_kind_name_swapped", r(V, "= @Codec.encEpiKindN h", "= @Codec.encHeadKindN h"), False),
        ("g6_kind_line_missing", r(V, "theorem Encode.generated_f1_kind :", "theorem Encode.generated_f1_kinx :"), False),
        ("g6_kind_const", r(V, "= @Codec.encFastKindN h marshalSSZTo", "= @Codec.encFastKindN h Prysm.SyncAggregatorSelectionData.Code.marshalSSZTo"), False),
        ("g6_kind_proof", r(V, "  intro h; rfl\n", "  intro h; exact rfl\n"), False),
        ("g6_hk_const", r(V, "theorem Encode.generated_f1 : ∀ (k : Nat) (hk : marshalSSZTo.IsInfixAt",
                          "theorem Encode.generated_f1 : ∀ (k : Nat) (hk : Prysm.SyncAggregatorSelectionData.Code.marshalSSZTo.IsInfixAt"), False),
        ("g6_extra_def", r(V, "namespace Prysm.ValidatorBalance\n", "namespace Prysm.ValidatorBalance\n\ndef foo : Nat := 1\n"), False),
        ("g6_sorry", r(V, "  apply Eventually.done\n", "  sorry\n"), False),
        ("g6_heartbeats", r(V, "set_option maxHeartbeats 4000000 in", "set_option maxHeartbeats 8000000 in"), False),
        ("g6_fast_skips_f0", r(V, "(Encode.generated_f0 k hk", "(Encode.generated_f1 k hk"), False),
        ("g6_extra_theorem", r(V, "\nend Prysm.ValidatorBalance", "\ntheorem extra : True := trivial\n\nend Prysm.ValidatorBalance"),
         False),
        ("g6_json_sha", r(V, sha, ("0" if sha[0] != "0" else "1") + sha[1:]), False),
        ("g6_json_missing", r(V, "GEN6-JSON: ", "GEN6-JSOX: "), False),
        ("g6_layout_named_hand", V.replace("Prysm.ValidatorBalance.Encode.generated_layout", "Prysm.BeaconBlockHeader.encodeLayout"), False),
        ("g6_const_unbound", V.replace("marshalSSZTo", "otherMarshalSSZTo"), False),
        ("g6_stmt_generated", r(Cp, "type_of% (@Prysm.Checkpoint.Encode.fast_path ‹Host›)",
                                "type_of% (@Prysm.Checkpoint.Encode.generated_fast ‹Host›)"), False),
        ("g6_stmt_via_unknown", r(Cp, "  Prysm.Checkpoint.Encode.fast_path_of_kind Encode.generated_fast", "  Prysm.Checkpoint.foo Encode.generated_fast"), False),
        ("g6_hand_with_def", r(B, "namespace Prysm.BeaconBlockHeader\n", "namespace Prysm.BeaconBlockHeader\n\ndef Encode.generated_layout : EncLayout where\n  st := true\n"),
         False),
        ("g6_hs_frame_state", r(H, "  frame := 80\n", "  frame := 88\n"), False),
        ("g6_bh_state_slot", r(B, "(.reg .rax), .at (.up 16) (.reg .rbx), .at (.dn 16) (.orig 3)",
                               "(.reg .rax), .at (.up 16) (.reg .rbx), .at (.dn 16) (.reg .rbx)"), False),
    ]


def g6_selftest():
    """Rule 13 controls + the recomputation against the hand layouts of `Prysm/BeaconBlockHeader/EncodeFastPathKindInstances.lean` and the example layouts of the encoder lemma unit.
    Returns (n, bad)."""
    bad, n = [], 0
    try:
        T = {k: (KR / v).read_text() for k, v in G6_SELFTEST.items()}
        cs = g6_cases(T)
    except Exception as e:
        return 1, [("g6_fixtures", f"{type(e).__name__}: {e}")]
    for name, text, ok in cs:
        n += 1
        errs, _ = check_gen6(text, GNAMES)
        if (not errs) != ok:
            bad.append((name, errs[:3]))
    for tname, (src, short) in G6_L_LAYOUTS.items():
        n += 1
        try:
            d = "enc2/link/norm"
            sp = f"prysm/go1.26.10/e2e/{d}/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.{tname}.MarshalSSZTo.S"
            fs, goffs, size = g6_ir((KR / "prysm/ir/ir-mainnet.json").read_text(), "v1alpha1." + tname)
            X = g6_expect([l.strip() for l in (KR / sp).read_text().split("\n") if l.strip()], fs, goffs, size)
            Lx = g6_layout_def((KR / src).read_text(), short.rsplit(".", 1)[-1], short)
            if Lx != X["L"]:
                bad.append((f"g6_recompute_{tname}", Lx, X["L"]))
        except Exception as e:
            bad.append((f"g6_recompute_{tname}", f"{type(e).__name__}: {e}"))
    # an IR mutant: ValidatorBalance Balance at Go offset 24 -> the recomputation refuses
    n += 1
    try:
        d = _g6json.loads((KR / "prysm/ir/ir-mainnet.json").read_text())
        for c in d["configs"]:
            for t in c.get("types", []):
                if t.get("name") == "ValidatorBalance" and c["package"].endswith("/v1alpha1"):
                    t["go_fields"][2]["offset_gc_amd64"] = 24
        g6_ir(_g6json.dumps(d), "v1alpha1.ValidatorBalance")
        bad.append(("g6_ir_goff_mutant", "not refused"))
    except G6Mismatch:
        pass
    return n, bad


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
