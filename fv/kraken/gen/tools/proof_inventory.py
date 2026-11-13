#!/usr/bin/env python3
"""Inventory of the pinned target's SSZ methods. Python 3 standard library only.

  proof_inventory.py names <names.txt>
      write every name that the mapping rule below can choose (input of `inventory_decls.lean`)
  proof_inventory.py methods <p1cbin-amd64.nm> [<out.json>]
      read the `go tool nm` listing of the pinned ELF (not committed, 2 MB), check its sha256
      against the `nm sha256` line of `prysm/go1.26.10/build-ids.txt`, and write the list of SSZ methods of the target
      (default `prysm/go1.26.10/ssz-methods.json`). This list is the denominator of the inventory.
  proof_inventory.py run <decls.tsv> <axioms-gate.json> <proof-inventory.md> <proof-inventory.json>
      read `prysm/go1.26.10/ssz-methods.json` (every SSZ method of the pinned target), `prysm/go1.26.10/functions.json`
      (the DUMPED subset: the functions with a `.S` text), `prysm/ir/ir-mainnet.json` (field shapes, for the flat
      population), <axioms-gate.json> (the JSON of `gen/e2e/axioms_gate.py run` on the built tree of the same commit;
      its verdict must be PASS; the table records its header, declaration, theorem and module counts), the code
      constants of `lean/Prysm/**` (`def X : Program := include_x64_rt "…S"`, keyed by full declared name, whatever
      module declares them), the link tables `prysm/go1.26.10/e2e/**/RESULT`, and <decls.tsv> (output of
      `gen/tools/inventory_decls.lean` for the names above, run on the built tree of the same commit), and write the
      table. The committed record `prysm/go1.26.10/e2e/axioms-gate.json` (a past run, old names) is not read.
  (cwd = fv/kraken)

Three denominators are kept apart: (1) the SSZ methods of the target (`ssz-methods.json`, per method kind);
(2) the dumped functions (`functions.json`); (3) the development population: the 16 flat types with which the generated-decoder work
started (`DEVELOPMENT_TYPES`).
The flat fixed-size types of the target are computed from the IR by `FLAT_RULE`; those outside `DEVELOPMENT_TYPES` are listed.

Mapping. The rows are derived by a rule, not written by hand: for every directory `lean/Prysm/<GoTypeName>/` and
every part, the first candidate name of `DEC_CANDIDATES` / `ENC_FORMS` / `SIZE_FORM` (the name forms of
gen/restructure/SPEC.md and the names the generators write) that exists in <decls.tsv> is the part's theorem.
The encoder theorems outside the fast path need hand-written premise texts (`ENC_EXTRA`, keyed by full names).

Rule. A function's state comes ONLY from the mapping and the declarations in <decls.tsv>:
  * every chosen theorem must exist (kind `theorem`) and have only the standard axioms
    (`propext`, `Classical.choice`, `Quot.sound`); otherwise the script FAILS (exit 1);
  * the accept / reject / spec_k / reject_size_spec theorems of a decoder row, and the theorems of an encoder or
    SizeSSZ row, must have, in their TYPE, the code constant whose included `.S` is that function of the target, and
    that function must be the SUBJECT: the only one of the theorem's target code constants that no other of them calls
    (call graph = `call_targets` of `functions.json`); a constant counts only if its `.S` is
    `../prysm/go1.26.10/e2e/<dir>/norm/<function>.S` and `<dir>/RESULT` names the pinned ELF sha256, ends in
    `PASS all` and has `PASS (a) <function>:`; else FAIL;
  * a witness must use (in its proof) the row's accept / reject theorem, and `accept_spec_k` the accept theorem,
    `reject_size_spec` the reject theorem; else FAIL;
  * a decoder is "complete" (in this sense only) when accept, size reject, spec alignment (spec_k, reject_size_spec,
    reject_complete), codec equality / correspondence of the Desc, accept witness and reject witness are all present
    under these checks; "partial" when some are; "none" when the type has no row or no theorem.
  * an encoder `MarshalSSZTo` counts "fast path complete" when its row names a fast-path theorem, a spec
    corollary and a witness, all present under these checks: fast and spec keyed to the function by the code
    constant (subject rule), the spec corollary and every witness use the row's fast-path theorem; "fast path
    partial" when some are. The fast path has the premise `len(dst) + SizeSSZ <= cap(dst)` and exact byte-field
    lengths. The paths outside it are listed per type as NOT proved by a per-type rule:
    the path classes come from `functions.json` (growslice calls = capacity tests, `moveSliceNoCapNoScan` =
    epilogue frame test, morestack) and the IR (byte fields = length rejects); a class with no mapped theorem is
    listed in full; a class with mapped theorems needs a premise text per theorem and a row text of what stays NOT
    proved, and the cell prints both (else FAIL); a theorem mapped to a class the function lacks FAILS. No encoder
    is complete.
Types without a row are "not started". Exit 0 = table written, 1 = a check failed (nothing written), 2 = usage.

Limits (what the checks do NOT detect; also written into proof-inventory.md):
  * `codec` and `reject_complete` are checked for existence, kind and axioms only. Their types hold no code constant
    and their proofs use no mapped theorem, so a row that names ANOTHER type's codec or reject_complete theorem passes.
    Keying them (e.g. to the row's Desc constant) needs a new column in
    `inventory_decls.lean`; not done.
  * The subject rule uses the call graph of `functions.json`; a theorem whose type holds two target code constants
    where neither calls the other fails (no subject), it is not resolved.
  * The mapping rule chooses names by their form: the script checks the chosen theorems, not that the theorem's
    statement says what its part name means (that is the review of the statement and of the name).
  * <decls.tsv> carries the Lean version but no commit id; that it was made on the built tree of the same commit is
    a procedure step, not a check.
"""
import json
import pathlib
import re
import sys

KR = pathlib.Path(__file__).resolve().parent.parent.parent
STD = {"propext", "Classical.choice", "Quot.sound"}
V1A = "github.com/OffchainLabs/prysm/v7/proto/prysm/v1alpha1"
PRIM = "github.com/OffchainLabs/prysm/v7/consensus-types/primitives"
V1E = "github.com/OffchainLabs/prysm/v7/proto/engine/v1"

# The development population: the 16 flat fixed-size types with which the generated-decoder work (`scalgen.py p2dec
# --gen5`) started (decoders; AttestationData has nested fields and is listed apart).
DEVELOPMENT_TYPES = ["Checkpoint", "BeaconBlockHeader", "Eth1Data", "BlobIdentifier", "DepositMessage", "Deposit_Data",
          "PendingPartialWithdrawal", "SyncCommitteeMessage", "PendingConsolidation", "PendingDeposit", "PowBlock",
          "HistoricalSummary", "SigningData", "SyncAggregatorSelectionData", "ValidatorBalance", "VoluntaryExit"]
NESTED = ["AttestationData"]
# Why the generators refused a flat type outside DEVELOPMENT_TYPES (wording only, no state rule). Source: the single
# generator runs on the flat types outside the development population (`p2dec --gen5`, `p2enc --gen6`), the class read
# at the directive of the `.S` where the run stopped; the per-type run record is in git history only. A type or method
# missing here was generated (exit 0) by that run. The class is a field kind or a callee the generators do not support.
GENERATOR_REFUSED = {
    "v1.BuilderExitRequest": dict(decoder="byte vector 20", encoder="byte vector 20"),
    "v1.ConsolidationRequest": dict(decoder="byte vector 20", encoder="byte vector 20"),
    "v1.Withdrawal": dict(decoder="byte vector 20", encoder="byte vector 20"),
    "v1.WithdrawalRequest": dict(decoder="byte vector 20", encoder="byte vector 20"),
    "v1alpha1.BLSToExecutionChange": dict(decoder="byte vector 20", encoder="byte vector 20"),
    "v1alpha1.BuilderPendingWithdrawal": dict(decoder="byte vector 20", encoder="byte vector 20"),
    "v1alpha1.ProposerPreferences": dict(decoder="byte vector 20", encoder="byte vector 20"),
    "v1alpha1.ValidatorRegistrationV1": dict(decoder="byte vector 20", encoder="byte vector 20"),
    "v1alpha1.ENRForkID": dict(decoder="byte vector 4", encoder="byte vector 4"),
    "v1alpha1.Fork": dict(decoder="byte vector 4", encoder="byte vector 4"),
    "v1alpha1.ForkData": dict(decoder="byte vector 4", encoder="byte vector 4"),
    "v1alpha1.Status": dict(decoder="byte vector 4", encoder="byte vector 4"),
    "v1alpha1.StatusV2": dict(decoder="byte vector 4", encoder="byte vector 4"),
    "v1alpha1.Builder": dict(decoder="byte vector 1", encoder="byte vector 1"),
    "v1alpha1.PayloadAttestationData": dict(decoder="bool", encoder="bool"),
    "v1alpha1.Validator": dict(decoder="bool", encoder="bool"),
    "v1alpha1.BuilderPreferences": dict(decoder="callee primitives.Gwei.UnmarshalSSZ"),
}


# ---------------------------------------------------------------- mapping, derived by rule from the name forms
# A row is derived for every type directory `lean/Prysm/<GoTypeName>/` from the name forms of SPEC.md (gen/restructure):
# `Prysm.<GoTypeName>.Decode.accept`, `.Decode.reject_size`, `.Encode.fast_path`, `.Witness.<Role>.runs`, ... and the
# names that the generators write (`Decode.generated_accept`, `Encode.generated_fast`, ...). For each part the FIRST
# candidate that exists (a declaration of <decls.tsv>, kind not MISSING) is the row's theorem; a part with no existing
# candidate is missing. The order of the candidates is part of the rule (the hand main theorem before the generated one).
# The checks of the Rule above apply to every chosen theorem exactly as to a hand-written row.
V1A_PREFIX = "Prysm."
DEC_CANDIDATES = {
    "accept": ["Decode.accept", "Decode.accept_from_generated_steps", "Decode.generated_accept"],
    "reject": ["Decode.reject_size", "Decode.generated_reject"],
    "spec_k": ["Decode.accept_spec"],
    "reject_size_spec": ["Decode.reject_size_spec"],
    "reject_complete": ["Decode.reject_complete"],
    # codec equality of the hand Desc and the Desc checker's Desc; the alternative pair is the correspondence form
    # (same accepted inputs + number / little-endian bytes correspondence, spec uint256)
    "codec": [["desc_deserialize_checker"], ["Decode.accepts_same", "Decode.codec_checker"]],
}
# The witness of a part follows the form of the chosen theorem: for a generated theorem the generated witness comes
# first. The Rule's refs check then requires that the chosen witness uses the chosen theorem.
WIT_ACCEPT = {"Decode.generated_accept": ["Witness.GeneratedDecodeAccept.runs", "Witness.DecodeAccept.runs"]}
WIT_ACCEPT_DEFAULT = ["Witness.DecodeAccept.runs"]
WIT_REJECT = {"Decode.generated_reject": ["Witness.GeneratedDecodeRejectSize.runs", "Witness.DecodeRejectSize.runs"]}
WIT_REJECT_DEFAULT = ["Witness.DecodeRejectSize.runs", "Witness.DecodeRejectSize.runs_size",
                      "Witness.DecodeRejectSize.RejectSize.runs"]
# Encoder fast path: the generated theorem, its spec corollary and its two witness instances; else the hand theorem,
# its spec corollary and its witness instances (`runs_empty` and the qualified `runs_*` that exist).
ENC_FORMS = [
    dict(fast="Encode.generated_fast", spec="Encode.generated_fast_spec",
         witness=["Witness.GeneratedEncodeFastPath.runs_empty", "Witness.GeneratedEncodeFastPath.runs_prefix"]),
    dict(fast="Encode.fast_path", spec="Encode.fast_path_spec",
         witness=["Witness.EncodeFastPath.runs_empty", "Witness.EncodeFastPath.runs_one_element",
                  "Witness.EncodeFastPath.runs_maximum"]),
]
# When a type has both forms, the hand theorems and the hand witness are listed too (`hand`, `other_witness`).
ENC_HAND = ["Encode.fast_path", "Encode.fast_path_spec"]
ENC_HAND_WITNESS = ["Witness.EncodeFastPath.runs_empty"]
SIZE_FORM = dict(main=["Size.result"], witness=["Witness.Size.runs"])

# Encoder theorems outside the fast path need a premise text (what the theorem assumes beyond the fast-path frame
# premises) and a text of what stays NOT proved in their path class: these texts are hand-written (review of the
# statements), keyed by the present full names. A type without an entry has its path classes listed as NOT proved.
CP_GROW = "GrowsliceC + MemmoveC contracts + heap budget"
ENC_EXTRA = {
    "Checkpoint": dict(
        rejects=[("Prysm.Checkpoint.Encode.reject_length", "len + 8 ≤ cap"),
                 ("Prysm.Checkpoint.Encode.reject_length_cover",
                  "every cap, GrowsliceC contract + heap budget 4·len + 8736 ≤ avail ≤ maxAlloc")],
        grow=[("Prysm.Checkpoint.Encode.grow_first_site", f"cap < len + 8, len + 40 ≤ nextSliceCap(len + 8, cap), {CP_GROW}"),
              ("Prysm.Checkpoint.Encode.grow_second_site", f"len + 8 ≤ cap < len + 40, {CP_GROW}"),
              ("Prysm.Checkpoint.Encode.grow_any_site",
               f"cap < len + 8, {CP_GROW}: returns or reaches the second growslice call")],
        other_witness=["Prysm.Checkpoint.Witness.EncodeRejectLength.runs", "Prysm.Checkpoint.Witness.EncodeGrowFirstSite.runs"],
        left={"length rejects": "with cap < len + 8 outside the GrowsliceC contract or the heap budget",
              "growslice branches": "outside the GrowsliceC / MemmoveC contracts and the heap budget, and the run after "
                                    "the second growslice call when the heap left by the first call is below the "
                                    "second call's budget (FINDINGS.md: \"Growslice contract gives no lower bound "
                                    "on the remaining heap\"; checked by the differential test only)"}),
    "BeaconBlockHeader": dict(
        rejects=[("Prysm.BeaconBlockHeader.Encode.reject_length_parent_root", "len + 112 ≤ cap"),
                 ("Prysm.BeaconBlockHeader.Encode.reject_length_state_root", "len + 112 ≤ cap, MemmoveC"),
                 ("Prysm.BeaconBlockHeader.Encode.reject_length_body_root", "len + 112 ≤ cap, MemmoveC")],
        left={"length rejects": "with cap < len + 112 (with len + 16 ≤ cap < len + 112 a ParentRoot reject is "
                                "reached without a growslice call)"}),
}
# Encoder theorems outside the fast path that the tool does not classify (no premise text in ENC_EXTRA): the row says
# that they exist, so that its NOT-proved column does not understate silently.
ENC_UNCLASSIFIED = ["Encode.grow_first_site", "Encode.grow_second_site", "Encode.grow_one_site", "Encode.grow_any_site",
                    "Encode.reject_length", "Encode.reject_too_big"]
ENC_PARTS = ["fast", "spec", "witness", "hand", "rejects", "grow", "other_witness"]
ENC_PREMISE = "premise: len + SizeSSZ <= cap, exact field lengths"
DEC_PARTS = ["accept", "reject", "spec_k", "reject_size_spec", "reject_complete", "codec", "witness_accept",
             "witness_reject"]
SKIP_DIRS = {"ElfData", "RuntimeModel"}


def type_dirs():
    """The Go type names of the directories `lean/Prysm/<GoTypeName>/` (the ELF data and runtime models excluded)."""
    return sorted(p.name for p in (KR / "lean/Prysm").iterdir() if p.is_dir() and p.name not in SKIP_DIRS)


def candidates(t):
    """Every name that the rule can choose for type t (input of `inventory_decls.lean`)."""
    out = []
    for v in DEC_CANDIDATES.values():
        for c in v:
            out += c if isinstance(c, list) else [c]
    for v in list(WIT_ACCEPT.values()) + [WIT_ACCEPT_DEFAULT] + list(WIT_REJECT.values()) + [WIT_REJECT_DEFAULT]:
        out += v
    for f in ENC_FORMS:
        out += [f["fast"], f["spec"]] + f["witness"]
    out += ENC_UNCLASSIFIED
    out += ENC_HAND + ENC_HAND_WITNESS + SIZE_FORM["main"] + SIZE_FORM["witness"]
    out = [f"{V1A_PREFIX}{t}.{n}" for n in out]
    x = ENC_EXTRA.get(t, {})
    out += [n for n, _ in x.get("rejects", [])] + [n for n, _ in x.get("grow", [])] + x.get("other_witness", [])
    return list(dict.fromkeys(out))


def names():
    out = []
    for t in type_dirs():
        out += candidates(t)
    return list(dict.fromkeys(out))


def derive(D, target_key):
    """The rows of the mapping, chosen from the declarations D that exist. target_key: Go type name -> (package, type)."""
    have = lambda n: n in D and D[n]["kind"] != "MISSING"   # noqa: E731
    decoders, encoders, sizers, unknown = {}, {}, {}, []
    for t in type_dirs():
        if t not in target_key:
            unknown.append(t)
            continue
        key, P = target_key[t], f"{V1A_PREFIX}{t}."
        r = {}
        for part in ("accept", "reject", "spec_k", "reject_size_spec", "reject_complete"):
            r[part] = next((P + c for c in DEC_CANDIDATES[part] if have(P + c)), None)
        r["codec"] = next(([P + c for c in grp] for grp in DEC_CANDIDATES["codec"] if all(have(P + c) for c in grp)), None)
        acc_form = r["accept"][len(P):] if r["accept"] else None
        rej_form = r["reject"][len(P):] if r["reject"] else None
        wa = WIT_ACCEPT.get(acc_form, WIT_ACCEPT_DEFAULT) if acc_form else []
        wr = WIT_REJECT.get(rej_form, WIT_REJECT_DEFAULT) if rej_form else []
        r["witness_accept"] = next((P + c for c in wa if have(P + c)), None)
        r["witness_reject"] = next((P + c for c in wr if have(P + c)), None)
        notes = []
        if acc_form == "Decode.generated_accept":
            notes.append("generated accept theorem (statement = kind instance)")
        if acc_form == "Decode.accept_from_generated_steps":
            notes.append("accept composed from generated steps")
        if r["codec"] and len(r["codec"]) == 2:
            notes.append("codec: same accepted inputs + number / LE-bytes correspondence (spec uint256)")
        r["note"] = "; ".join(notes)
        if any(r[p] for p in DEC_PARTS):
            decoders[key] = r
        form = next((f for f in ENC_FORMS if have(P + f["fast"])), None)
        x = ENC_EXTRA.get(t, {})
        if form:
            e = dict(fast=[P + form["fast"]], spec=[P + form["spec"]] if have(P + form["spec"]) else [],
                     witness=[P + w for w in form["witness"] if have(P + w)], hand=[], rejects=[], grow=[],
                     other_witness=[], premise={}, left=dict(x.get("left", {})))
            if form is ENC_FORMS[0]:
                e["hand"] = [P + h for h in ENC_HAND if have(P + h)]
                if e["hand"]:
                    e["other_witness"] = [P + w for w in ENC_HAND_WITNESS if have(P + w)]
            for cls in ("rejects", "grow"):
                for n, prem in x.get(cls, []):
                    if not have(n):
                        unknown.append(f"{n} (ENC_EXTRA of {t}: not in <decls.tsv>)")
                        continue
                    e[cls].append(n)
                    e["premise"][n] = prem
            for n in x.get("other_witness", []):
                if have(n):
                    e["other_witness"].append(n)
                else:
                    unknown.append(f"{n} (ENC_EXTRA of {t}: not in <decls.tsv>)")
            mapped = set(e["rejects"] + e["grow"])
            e["unclassified"] = [P + n for n in ENC_UNCLASSIFIED if have(P + n) and P + n not in mapped]
            encoders[key] = e
        if have(P + SIZE_FORM["main"][0]):
            sizers[key] = dict(main=[P + n for n in SIZE_FORM["main"]],
                               witness=[P + n for n in SIZE_FORM["witness"] if have(P + n)])
    return decoders, encoders, sizers, unknown

WHAT_COMPLETE_EXCLUDES = [
    "morestack paths (the `jbe` to `runtime.morestack_noctxt` at entry)",
    "`runtime.writeBarrier` != 0 (every accept theorem assumes the flag word is 0)",
    "runtime callee bodies (makeslice / memmove / growslice / newobject / fmt.errorf: contract hypotheses, "
    "MakesliceC / MemmoveC / ...)",
    "callee error returns (the `fmt.Errorf` wrap paths of delegated fields; `reject_complete` covers the size path "
    "condition only)",
    "growslice (encoder capacity growth beyond the listed theorems; FINDINGS.md: \"Growslice contract gives no lower "
    "bound on the remaining heap\")",
    "x86-64 hardware execution (semantics = Kraken's model of the amd64 instructions; no hardware run)",
]
CANNOT_DETECT = [
    "a row whose `codec` or `reject_complete` names ANOTHER type's theorem: these two parts are checked for existence, "
    "kind and axioms only (their types hold no code constant, their proofs use no mapped theorem; found by "
    "an earlier review). Keying them to the row's Desc constant needs a new column in `inventory_decls.lean`; not done",
    "that a theorem's statement says what its part name means (accept, reject, spec): the mapping chooses names by "
    "their form (SPEC.md); the statements are checked by review and by the kinds, not by this script",
    "a theorem with two target code constants of which neither calls the other (it fails: no single subject)",
    "that <decls.tsv> was made on the built tree of the same commit (its header has the Lean version, no commit id)",
    "that an encoder row's premise text and NOT-proved text say what the mapped reject / growslice theorems assume "
    "(hand-written per row; checked by review against the theorem statements, not by this script)",
    "methods outside `github.com/OffchainLabs/prysm/v7/` (e.g. `github.com/holiman/uint256`) and SSZ methods with "
    "names outside the listed kinds",
]


PIN_S = re.compile(r"^\.\./prysm/go1\.26\.10/e2e/((?:[\w-]+/)*[\w-]+)/norm/([^/]+)\.S$")
CODE_DEF = re.compile(r'^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*def\s+(\S+)\s*:\s*Program\s*:=\s*'
                      r'include_x64_rt\s+"([^"]+)"', re.M)


def link_tables():
    """Link table directory (under prysm/go1.26.10/e2e/) -> set of the functions whose text check (a) PASSed, for every
    directory whose `RESULT` names the pinned ELF (`elf sha256` of build-ids.txt) and ends in `PASS all`."""
    elf = build_ids().get("elf sha256")
    out = {}
    root = KR / "prysm/go1.26.10/e2e"
    for res in sorted(root.rglob("RESULT")):
        t = res.read_text()
        if f"elf sha256 {elf}" not in t or not re.search(r"(?m)^PASS all$", t):
            continue
        out[str(res.parent.relative_to(root))] = set(re.findall(r"(?m)^PASS \(a\) (\S+?):", t))
    return out


def code_constants():
    """Lean code constant (full declared name) -> normalized function key `pkg_with_underscores.Type.Method`, for the
    constants whose `.S` is `../prysm/go1.26.10/e2e/<dir>/norm/<function>.S` with `<dir>` a link table of the pinned
    ELF (`link_tables`: RESULT with the pinned ELF sha256, `PASS all`, and `PASS (a) <function>:`); other constants ->
    None (not a target function: runtime models, other builds such as the capacity-reserved test ELF).
    Every `lean/Prysm/**.lean` file is read, whatever module declares the constant: the full name comes from the
    namespace blocks (`namespace` / `end`) and the declaring name (`_root_.` prefix, dotted names). A full name declared
    twice is a failure (second value)."""
    m, dup = {}, []
    tables = link_tables()
    for f in sorted((KR / "lean/Prysm").rglob("*.lean")):
        stack = []
        for line in f.read_text().split("\n"):
            ns = re.match(r"^namespace\s+(\S+)\s*$", line)
            if ns:
                stack.append(ns.group(1))
                continue
            en = re.match(r"^end\s+(\S+)\s*$", line)
            if en and stack and stack[-1] == en.group(1):
                stack.pop()
                continue
            d = CODE_DEF.match(line)
            if not d:
                continue
            name, path = d.group(1), d.group(2)
            full = name[len("_root_."):] if name.startswith("_root_.") else ".".join(stack + [name])
            if full in m:
                dup.append(full)
            hit = PIN_S.match(path)
            m[full] = hit.group(2) if hit and hit.group(2) in tables.get(hit.group(1), set()) else None
    return m, dup


# ---------------------------------------------------------------- denominator (1): SSZ methods of the target
SSZ_KINDS = ["UnmarshalSSZ", "MarshalSSZTo", "MarshalSSZ", "SizeSSZ", "HashTreeRoot", "HashTreeRootWith",
             "ProgressiveHashTreeRoot", "ProgressiveHashTreeRootWith", "MaxSizeSSZ"]
SCOPE = "github.com/OffchainLabs/prysm/v7/"
NM_SYM = re.compile(r"^((?:[\w.-]+/)*[\w-]+)\.(?:\(\*(\w+)\)|(\w+))\.(\w+)$")
METHODS_JSON = "prysm/go1.26.10/ssz-methods.json"


def build_ids():
    out = {}
    for line in open(KR / "prysm/go1.26.10/build-ids.txt"):
        k, _, v = line.partition(":")
        out[k.strip()] = v.strip()
    return out


def methods(nm_p, out_p):
    import hashlib
    bid = build_ids()
    h = hashlib.sha256(open(nm_p, "rb").read()).hexdigest()
    if h != bid.get("nm sha256"):
        print(f"FAIL {nm_p}: sha256 {h} != build-ids.txt nm sha256 {bid.get('nm sha256')}")
        return 1
    meth, other = {}, {}
    for line in open(nm_p):
        parts = line.split(None, 3)
        if len(parts) != 4 or parts[2] not in ("T", "t"):
            continue
        m = NM_SYM.match(parts[3].strip())
        if not m or m.group(4) not in SSZ_KINDS:
            continue
        pkg, typ, kind = m.group(1), m.group(2) or m.group(3), m.group(4)
        if not pkg.startswith(SCOPE):
            other[pkg] = other.get(pkg, 0) + 1
            continue
        meth.setdefault((pkg, typ, kind), []).append(parts[3].strip())
    rows = [dict(package=p, type=t, method=k, symbols=sorted(s)) for (p, t, k), s in sorted(meth.items())]
    out = dict(schema="fvkraken.ssz-methods/1", source="`go tool nm` listing of the pinned ELF (not committed)",
               nm_sha256=h, elf_sha256=bid.get("elf sha256"),
               rule=f"text symbols (nm type T or t) `<pkg>.<Type>.<Method>` or `<pkg>.(*<Type>).<Method>` with "
                    f"<pkg> under `{SCOPE}` and <Method> in {SSZ_KINDS}; one row per (package, type, method); "
                    "`symbols` lists the receiver forms present (a value-receiver method also has its compiler "
                    "pointer wrapper)",
               out_of_scope_symbols=dict(sorted(other.items())), methods=rows)
    head = {k: v for k, v in out.items() if k != "methods"}
    txt = json.dumps(head, indent=1)[:-2] + ',\n "methods": [\n'
    txt += ",\n".join("  " + json.dumps(r) for r in rows) + "\n ]\n}\n"
    open(out_p, "w").write(txt)
    print(json.dumps({k: sum(r["method"] == k for r in rows) for k in SSZ_KINDS}))
    return 0


# ---------------------------------------------------------------- flat fixed-size types of the target (IR)
FLAT_RULE = ("IR record `ir` of `prysm/ir/ir-mainnet.json` (the ELF is built without the `minimal` tag): "
             "`variable` false, and every field is a byte vector (`k` vector of `byte`), an unsigned integer "
             "(`k` uint), a bool (`k` bool) or a uint overlay (`k` overlay of a uint, not a bitfield); "
             "no nested container, no list, no bitfield, no vector of non-bytes")


def field_flat(v):
    k = v.get("k")
    if k in ("uint", "bool"):
        return True
    if k == "vector":
        return (v.get("elem") or {}).get("k") == "byte"
    if k == "overlay":
        return (v.get("underlying") or {}).get("k") == "uint" and not v.get("bitfield")
    return False


def ir_types():
    d = json.load(open(KR / "prysm/ir/ir-mainnet.json"))
    out, bad = {}, []
    for c in d["configs"]:
        for t in c.get("types") or []:
            key = (t["package"], t["name"])
            if key in out and out[key] != t.get("ir"):
                bad.append(key)
            out.setdefault(key, t.get("ir"))
    return out, bad


def run(decls_p, gate_p, md_p, json_p):
    fails = []
    funcs = json.load(open(KR / "prysm/go1.26.10/functions.json"))["functions"]
    gate = json.load(open(gate_p))
    for k in ("header", "verdict", "declarations", "theorems", "modules"):
        if k not in gate:
            print(f"FAIL {gate_p}: no `{k}` (not an output of gen/e2e/axioms_gate.py run)")
            return 1
    raw = open(decls_p).read().split("\n")
    if not any(l.startswith("# inventory_decls v1") for l in raw):
        print(f"FAIL {decls_p}: no inventory_decls header")
        return 1
    raw = raw[next(i for i, l in enumerate(raw) if l.startswith("# inventory_decls v1")):]
    lines = [l.split("\t") for l in raw if l.strip()]
    bad = [l for l in lines[1:] if len(l) != 5]
    if bad:
        print(f"FAIL {decls_p}: malformed rows {bad[:3]}")
        return 1
    header = lines[0][0] if lines and lines[0][0].startswith("#") else None
    D = {r[0]: dict(kind=r[1], axioms=r[2], programs=r[3], refs=r[4]) for r in lines if not r[0].startswith("#")}
    for n in names():
        if n not in D:
            fails.append(f"{n}: not in {decls_p} (run inventory_decls.lean on the names of `proof_inventory.py names`)")
    sm0 = json.load(open(KR / METHODS_JSON))
    target_key = {r["type"]: (r["package"], r["type"]) for r in sm0["methods"]}
    if len(target_key) != len({(r["package"], r["type"]) for r in sm0["methods"]}):
        fails.append(f"{METHODS_JSON}: a Go type name occurs in two packages (the directory name does not decide)")
    DECODERS, ENCODERS, SIZERS, unknown = derive(D, target_key)
    for u in unknown:
        fails.append(f"lean/Prysm/{u}: not a type of {METHODS_JSON}" if "/" not in u and " " not in u else u)
    chosen = []
    for r in DECODERS.values():
        for k in DEC_PARTS:
            v = r[k]
            chosen += v if isinstance(v, list) else ([v] if v else [])
    for r in ENCODERS.values():
        for k in ENC_PARTS:
            chosen += r[k]
    for r in SIZERS.values():
        for v in r.values():
            chosen += v
    for n in dict.fromkeys(chosen):
        if D[n]["kind"] != "theorem":
            fails.append(f"{n}: {D[n]['kind']} (a name of the mapping is not a theorem)")
        else:
            ax = set() if D[n]["axioms"] == "-" else set(D[n]["axioms"].split(","))
            if not ax <= STD:
                fails.append(f"{n}: non-standard axioms {sorted(ax - STD)}")
    cc, dup = code_constants()
    for n in dup:
        fails.append(f"code constant {n} is defined twice under lean/Prysm/")
    fn_by_key = {re.sub(r"\(\*?(\w+)\)", r"\1", f["symbol"]).replace("/", "_").replace("-", "_"): f for f in funcs}
    sym_key = {f["symbol"]: k for k, f in fn_by_key.items()}
    callees = {k: {sym_key[c] for c in f.get("call_targets", {}) if c in sym_key} for k, f in fn_by_key.items()}

    def progs(n):
        p = D.get(n, {}).get("programs", "-")
        return [] if p == "-" else p.split(",")

    def refs(n):
        r = D.get(n, {}).get("refs", "-")
        return [] if r == "-" else r.split(",")

    def symkey(pkg, typ, meth):
        return f"{pkg}.{typ}.{meth}".replace("/", "_").replace("-", "_")

    def code_ok(n, pkg, typ, meth):
        k = symkey(pkg, typ, meth)
        hits = [c for c in progs(n) if cc.get(c) == k]
        if not hits:
            fails.append(f"{n}: no code constant of {k} in its type (programs: {progs(n)})")
            return False
        # subject: the target functions of the theorem's code constants that no other of them calls
        fs = {cc[c] for c in progs(n) if cc.get(c) in fn_by_key}
        roots = sorted(f for f in fs if not any(f in callees[g] for g in fs if g != f))
        if roots != [k]:
            fails.append(f"{n}: subject {roots} is not {k} (programs: {progs(n)}; a callee's code is not the subject)")
            return False
        return True

    rows = {}
    for (pkg, typ), r in DECODERS.items():
        st = {}
        for part in DEC_PARTS:
            v = r[part]
            st[part] = bool(v)
        for part in ("accept", "reject", "spec_k", "reject_size_spec"):
            if r[part] and r[part] in D:
                code_ok(r[part], pkg, typ, "UnmarshalSSZ")
        for part, target in (("witness_accept", "accept"), ("witness_reject", "reject"), ("spec_k", "accept"),
                             ("reject_size_spec", "reject")):
            if r[part] and r[target] and r[part] in D and r[target] not in refs(r[part]):
                fails.append(f"{r[part]}: does not use {r[target]} (refs: {refs(r[part])})")
        missing = [p for p in DEC_PARTS if not st[p]]
        state = "complete" if not missing else ("partial" if len(missing) < len(DEC_PARTS) else "none")
        rows[(pkg, typ, "UnmarshalSSZ")] = dict(state=state, missing=missing,
                                                theorems={p: r[p] for p in DEC_PARTS if r[p]}, note=r["note"])
    ir_rec, _ = ir_types()
    for (pkg, typ), r in ENCODERS.items():
        for n in r["fast"] + r["spec"] + r["hand"] + r["rejects"] + r["grow"]:
            if n in D:
                code_ok(n, pkg, typ, "MarshalSSZTo")
        for n in r["spec"] + r["witness"]:
            if n in D and not any(f in refs(n) for f in r["fast"]):
                fails.append(f"{n}: does not use the fast-path theorem {r['fast']} (refs: {refs(n)})")
        missing = [p for p in ("fast", "spec", "witness") if not r[p]]
        state = ("fast path complete" if not missing else
                 "fast path partial" if len(missing) < 3 else "none")
        rec = ir_rec.get((pkg, typ)) or {}
        flds = rec.get("fields") or []
        nbytes = sum(1 for f in flds if (f["v"].get("k") == "vector"))
        ct = (fn_by_key.get(symkey(pkg, typ, "MarshalSSZTo")) or {}).get("call_targets", {})
        ngrow = ct.get("runtime.growslice", 0)
        # per-type rule: every path class of the function is listed; a class with no
        # mapped theorem is NOT proved in full; a class with mapped theorems lists each theorem with its premise
        # text and the row's text of what stays NOT proved (both required); a class the function lacks cannot be
        # mapped.
        not_proved = []
        for cls, names_, count in (("growslice branches", r["grow"], f"{ngrow} capacity tests"),
                                   ("length rejects", r["rejects"], f"{nbytes} byte fields")):
            n_cls = ngrow if cls == "growslice branches" else nbytes
            if names_ and not n_cls:
                fails.append(f"encoder row {typ}: {cls} theorems mapped but the function has no {cls}")
            if not n_cls:
                continue
            if not names_:
                if cls in r["left"]:
                    fails.append(f"encoder row {typ}: NOT-proved text for {cls} but no theorem mapped")
                not_proved.append(f"{cls} ({count})")
                continue
            miss = [n for n in names_ if not r["premise"].get(n, "").strip()]
            if miss:
                fails.append(f"encoder row {typ}: {cls} theorem(s) {miss} without premise text")
            if not r["left"].get(cls, "").strip():
                fails.append(f"encoder row {typ}: {cls} theorems mapped but no text of what stays NOT proved")
            proved = ", ".join(f"{n.rsplit('.', 1)[-1]} ({r['premise'].get(n, '')})" for n in names_)
            not_proved.append(f"{cls} {r['left'].get(cls, '')} [{count}; proved only: {proved}]")
        if "runtime.moveSliceNoCapNoScan" in ct:
            not_proved.append("the `runtime.moveSliceNoCapNoScan` branch of the epilogue frame test (shown not taken "
                              "under the fast-path premises: dst separate from the frame; the branch itself is not "
                              "proved)")
        if "runtime.morestack_noctxt.abi0" in ct:
            not_proved.append("morestack")
        if r["unclassified"]:
            not_proved.append("note: theorems for some of these paths exist but this tool does not classify them "
                              "(no premise text): " + ", ".join(n.rsplit(".", 2)[-2] + "." + n.rsplit(".", 1)[-1]
                                                                for n in r["unclassified"]))
        rows[(pkg, typ, "MarshalSSZTo")] = dict(state=state, missing=missing,
                                                theorems={k: v for k, v in r.items()
                                                          if v and k in ENC_PARTS},
                                                note=ENC_PREMISE + ("; growth and reject theorems of this type exist "
                                                     "and are not classified by this tool (no premise text): "
                                                     + ", ".join(n.rsplit(".", 2)[-2] + "." + n.rsplit(".", 1)[-1]
                                                                 for n in r["unclassified"])
                                                     if r["unclassified"] else ""),
                                                witness=bool(r["witness"]), not_proved=not_proved)
    for (pkg, typ), r in SIZERS.items():
        for n in r["main"]:
            if n in D:
                code_ok(n, pkg, typ, "SizeSSZ")
        rows[(pkg, typ, "SizeSSZ")] = dict(state="proved", missing=[], theorems=r, note="")
    # ---------------------------------------------------------------- denominators
    bid = build_ids()
    sm = json.load(open(KR / METHODS_JSON))
    if sm.get("nm_sha256") != bid.get("nm sha256") or sm.get("elf_sha256") != bid.get("elf sha256"):
        fails.append(f"{METHODS_JSON}: nm / elf sha256 differ from build-ids.txt")
    target = {(r["package"], r["type"], r["method"]): r for r in sm["methods"]}
    dumped = {(f["package"], f["type"], f["method"]): f for f in funcs if f["type"] is not None}
    for key in dumped:
        if key not in target:
            fails.append(f"functions.json {'.'.join(key)}: not an SSZ method of {METHODS_JSON}")
    for (pkg, typ, meth) in rows:
        if symkey(pkg, typ, meth) not in fn_by_key:
            fails.append(f"mapping row {pkg}.{typ}.{meth}: no such function in functions.json")
        if (pkg, typ, meth) not in target:
            fails.append(f"mapping row {pkg}.{typ}.{meth}: not an SSZ method of the target")
    ir, ir_bad = ir_types()
    for key in ir_bad:
        fails.append(f"IR: two different records for {'.'.join(key)}")
    target_types = sorted({(p, t) for (p, t, _) in target})
    flat_target, no_ir = [], []
    for key in target_types:
        rec = ir.get(key)
        if rec is None:
            no_ir.append(key)
        elif rec.get("variable") is False and rec.get("fields") and all(field_flat(f["v"]) for f in rec["fields"]):
            flat_target.append(key)
    for t in DEVELOPMENT_TYPES:
        if (V1A, t) not in flat_target:
            fails.append(f"DEVELOPMENT_TYPES type {t}: not a flat fixed-size type of the target by FLAT_RULE")
    for t in NESTED:
        if (V1A, t) in flat_target:
            fails.append(f"NESTED type {t}: flat by FLAT_RULE")
    if gate.get("verdict") != "PASS":
        fails.append(f"axioms gate {gate_p}: verdict {gate.get('verdict')}")
    if fails:
        for f in fails:
            print("FAIL", f)
        return 1

    # ---------------------------------------------------------------- table and totals
    table = []
    started_types = {(p, t) for (p, t, _) in rows}
    for key in sorted(target):
        pkg, typ, meth = key
        r = rows.get(key)
        if r is None:
            state = "not started" if (pkg, typ) not in started_types else "none"
            r = dict(state=state, missing=[], theorems={}, note="")
        f = dumped.get(key)
        table.append(dict(symbols=target[key]["symbols"], package=pkg, type=typ, method=meth,
                          dumped=f is not None, kind=f["kind"] if f else None, **r))
    kinds = [k for k in SSZ_KINDS if any(t["method"] == k for t in table)]
    by_kind = {}
    for k in kinds:
        tk = [t for t in table if t["method"] == k]
        mapped = [t for t in tk if t["theorems"]]
        if k == "UnmarshalSSZ":
            comp = sum(t["state"] == "complete" for t in tk)
            part = sum(t["state"] == "partial" for t in tk)
        else:  # no done-contract is defined for this kind here: a mapped function is "partial"
            comp, part = 0, len(mapped)
        by_kind[k] = dict(target=len(tk), functions_json=sum(t["dumped"] for t in tk), mapped=len(mapped),
                          complete=comp, partial=part)
        if k == "MarshalSSZTo":
            by_kind[k]["fast_path_complete"] = sum(t["state"] == "fast path complete" for t in tk)
            by_kind[k]["fast_path_partial"] = sum(t["state"] == "fast path partial" for t in tk)
    runtime = [f["symbol"] for f in funcs if f["type"] is None]
    dev = {t: rows[(V1A, t, "UnmarshalSSZ")]["state"] for t in DEVELOPMENT_TYPES}
    flat_ns = [k for k in flat_target if k not in {(V1A, t) for t in DEVELOPMENT_TYPES}]
    flat_ns_state = {f"{p.rsplit('/', 1)[-1]}.{t}": ("not started" if (p, t) not in started_types else "started")
                     for p, t in flat_ns}
    tot = dict(
        denominators={
            "target_ssz_methods": f"{METHODS_JSON} (from the nm listing of the pinned ELF, sha256 {sm['nm_sha256']})",
            "dumped_functions": "prysm/go1.26.10/functions.json (functions with a `.S` text)",
            "development_population": "DEVELOPMENT_TYPES of gen/tools/proof_inventory.py (the 16 flat types with which "
                                      "the generated-decoder work started)"},
        target_ssz_methods=len(target), target_types=len(target_types),
        functions_json_total=len(funcs), functions_json_runtime_helpers=runtime,
        by_kind=by_kind,
        types_not_started=sum(1 for p, t in target_types if (p, t) not in started_types),
        development_population=DEVELOPMENT_TYPES,
        development_population_decoders_complete=f"{sum(v == 'complete' for v in dev.values())}/{len(DEVELOPMENT_TYPES)}",
        development_population_not_complete={t: rows[(V1A, t, "UnmarshalSSZ")]["missing"]
                                             for t, v in dev.items() if v != "complete"},
        flat_rule=FLAT_RULE,
        flat_fixed_types_in_target=len(flat_target),
        flat_outside_development_population=flat_ns_state,
        flat_outside_development_population_states={
            f"{p.rsplit('/', 1)[-1]}.{t}": dict(
                decoder=rows.get((p, t, "UnmarshalSSZ"), {}).get("state", "not started"),
                decoder_missing=rows.get((p, t, "UnmarshalSSZ"), {}).get("missing", []),
                encoder=rows.get((p, t, "MarshalSSZTo"), {}).get("state", "not started"),
                **{f"{m}_refused_by_generator": c for m, c in GENERATOR_REFUSED.get(f"{p.rsplit('/', 1)[-1]}.{t}", {}).items()})
            for p, t in flat_ns},
        target_types_without_ir=[f"{p.rsplit('/', 1)[-1]}.{t}" for p, t in no_ir],
        nested={t: rows[(V1A, t, "UnmarshalSSZ")]["state"] for t in NESTED},
    )
    out = dict(schema="fvkraken.inventory/2", source="gen/tools/proof_inventory.py", decls_header=header,
               methods_source=dict(file=METHODS_JSON, nm_sha256=sm["nm_sha256"], elf_sha256=sm["elf_sha256"]),
               axioms_gate=dict(header=gate["header"], verdict=gate["verdict"],
                                declarations=gate["declarations"], theorems=gate["theorems"], modules=gate["modules"]),
               definition_complete="decoder: accept + size reject + spec alignment (accept_spec_k, reject_size_spec, "
               "reject_complete) + Desc codec equality / correspondence + accept witness + reject witness, all "
               "kernel-checked theorems with standard axioms; accept / reject / spec_k / reject_size_spec theorems "
               "keyed to the function by the code constant in their type (the function is the subject: no other "
               "target code constant of the theorem calls it); witnesses and spec theorems use the mapped accept / "
               "reject theorem",
               complete_does_not_include=WHAT_COMPLETE_EXCLUDES, cannot_detect=CANNOT_DETECT, totals=tot,
               functions=table)
    json.dump(out, open(json_p, "w"), indent=1)
    bk = by_kind
    ud = bk["UnmarshalSSZ"]
    ns_names = ", ".join(n for n, s in flat_ns_state.items() if s == "not started")
    md = ["# Inventory of the pinned target's SSZ methods", "",
          "Generated by `gen/tools/proof_inventory.py` (do not edit). Target: the Go 1.26.10 ELF of `prysm/go1.26.10/` "
          f"(sha256 `{sm['elf_sha256']}`, `build-ids.txt`). The Go 1.26.3 phase work is a different binary and is "
          "not counted here.", "",
          f"Inputs: `{METHODS_JSON}` (made by `proof_inventory.py methods` from the `go tool nm` listing of the ELF, "
          f"sha256 `{sm['nm_sha256']}`; the listing is not committed), `prysm/go1.26.10/functions.json`, "
          "`prysm/ir/ir-mainnet.json`, the output of `gen/e2e/axioms_gate.py run` on the built tree, the code constants "
          "of `lean/Prysm/` with the link tables of the pinned ELF (`prysm/go1.26.10/e2e/**/RESULT`), and the output "
          "of `gen/tools/inventory_decls.lean` on the built tree.", "",
          f"Declarations header: `{header}`. Axioms gate run: {gate['verdict']}, {gate['declarations']} declarations "
          f"({gate['theorems']} theorems, {gate['modules']} modules), header `{gate['header']}`.", "",
          "## Denominators", "",
          f"1. SSZ methods of the target: {len(target)} methods of {len(target_types)} types (`{METHODS_JSON}`). "
          "This is the total in every line below.",
          f"2. Dumped functions (`functions.json`, a `.S` text exists): {len(funcs)}, of which "
          f"{len(funcs) - len(runtime)} are SSZ methods and {len(runtime)} are runtime helpers "
          f"({', '.join(r.rsplit('.', 1)[-1] for r in runtime)}). A theorem needs a dumped function.",
          f"3. Development population: the {len(DEVELOPMENT_TYPES)} flat types with which the generated-decoder work "
          "started (`DEVELOPMENT_TYPES` of the script). "
          "It is not the set of flat fixed-size types of the target (see the flat types below).", "",
          "## Totals by method kind", "",
          "| method kind | in the target | in `functions.json` | with a mapping row | complete | partial |",
          "| --- | --- | --- | --- | --- | --- |"]
    for k, v in bk.items():
        md.append(f"| `{k}` | {v['target']} | {v['functions_json']} | {v['mapped']} | {v['complete']} | "
                  f"{v['partial']} |")
    md += ["", "\"complete\" is defined for `UnmarshalSSZ` only (below). For the other kinds no done-contract is "
           "defined here: a function with at least one mapped theorem is \"partial\".", "",
           "## Summary", "",
           f"- Decoders: complete {ud['complete']} of the {ud['target']} `UnmarshalSSZ` methods of the target "
           f"({ud['functions_json']} dumped); partial {ud['partial']}; none {ud['target'] - ud['complete'] - ud['partial']}.",
           f"- Encoders `MarshalSSZTo`: fast-path complete {bk['MarshalSSZTo']['fast_path_complete']} of "
           f"{bk['MarshalSSZTo']['target']} ({ENC_PREMISE.replace('<=', '≤')}); no encoder is complete. "
           f"Fast path complete = fast-path theorem + spec corollary + witness. Fast path partial: "
           f"{bk['MarshalSSZTo']['fast_path_partial']}. Not proved per type (column NOT proved below, per-type "
           "rule): the growslice branches, the length rejects, the morestack path and, for the frame-test types, "
           "the `moveSliceNoCapNoScan` branch; Checkpoint and BeaconBlockHeader: the reject / growslice theorems "
           "of their rows with the premise of each and what stays not proved. `MarshalSSZ`: none of "
           f"{bk['MarshalSSZ']['target']} ({bk['MarshalSSZ']['functions_json']} dumped).",
           f"- `SizeSSZ`: a theorem for {bk['SizeSSZ']['partial']} of {bk['SizeSSZ']['target']}."]
    htr = [k for k in bk if "HashTreeRoot" in k]
    md.append("- Hash tree root: no theorem. " + "; ".join(
        f"`{k}` {bk[k]['target']} in the target, {bk[k]['functions_json']} dumped" for k in htr) + ".")
    other = [k for k in bk if k not in ("UnmarshalSSZ", "MarshalSSZTo", "MarshalSSZ", "SizeSSZ") and k not in htr]
    if other:
        md.append("- Other: " + "; ".join(f"`{k}` {bk[k]['target']} in the target, none proved" for k in other) + ".")
    md += [f"- Types with no mapping row (\"not started\", every method): {tot['types_not_started']} of "
           f"{len(target_types)}.",
           f"- Decoders of the {len(DEVELOPMENT_TYPES)}-type development population: "
           f"{tot['development_population_decoders_complete']} complete (defined sense)."]
    for t, miss in tot["development_population_not_complete"].items():
        md.append(f"  - {t}: missing {', '.join(miss)}.")
    md += [f"- Flat fixed-size types of the target (rule below): {len(flat_target)}. Outside the development "
           f"population: {len(flat_ns)}; not started: "
           f"{sum(s == 'not started' for s in flat_ns_state.values())} ({ns_names}).",
           f"- Nested: {', '.join(f'{t} {s}' for t, s in tot['nested'].items())} (not flat)."]
    fs_ = tot["flat_outside_development_population_states"]
    started_ = {k: v for k, v in fs_.items() if flat_ns_state.get(k) == "started"}
    if started_:   # flat types outside DEVELOPMENT_TYPES with a mapping row
        md.append(f"- Flat types outside the development population with a mapping row: {len(started_)}; decoders "
                  f"complete {sum(v['decoder'] == 'complete' for v in started_.values())}, encoders fast-path complete "
                  f"{sum(v['encoder'] == 'fast path complete' for v in started_.values())}.")
        for k, v in started_.items():
            md.append(f"  - {k}: decoder {v['decoder']}"
                      + (f" (missing {', '.join(v['decoder_missing'])})" if v["decoder_missing"] else "")
                      + (f"; generator run refused: {v['decoder_refused_by_generator']}" if "decoder_refused_by_generator" in v else "")
                      + f"; encoder {v['encoder']}.")
    refused_ = {k: v for k, v in fs_.items() if flat_ns_state.get(k) == "not started"}
    if refused_:   # why the single generator run refused each not-started flat type (wording only)
        md.append(f"- Flat types outside the development population without a mapping row: {len(refused_)}; "
                  "why the single generator run (`p2dec --gen5` / `p2enc --gen6`) refused it, a field kind or callee "
                  "the generators do not support:")
        for k, v in refused_.items():
            md.append(f"  - {k}: decoder refused ({v.get('decoder_refused_by_generator', 'no record of the run')}); encoder "
                      f"refused ({v.get('encoder_refused_by_generator', 'no record of the run')}).")
    if no_ir:
        md.append(f"- Target types without an IR record (not classified): {', '.join(tot['target_types_without_ir'])}.")
    md += ["", f"Flat rule: {FLAT_RULE}.", "",
           "## What \"complete\" means here", "", out["definition_complete"] + ".", "",
           "It does NOT include:", ""] + [f"- {x}" for x in WHAT_COMPLETE_EXCLUDES] + [
           "", "## What this table cannot detect", ""] + [f"- {x}" for x in CANNOT_DETECT] + [
           "", "## Functions with at least one theorem", "",
           "| function | state | missing | theorems |", "| --- | --- | --- | --- |"]
    enc_rows = [t for t in table if t["method"] == "MarshalSSZTo" and t["theorems"]]
    for t in table:
        if t["state"] in ("not started", "none") and not t["theorems"]:
            continue
        th = "; ".join(f"{k}: {', '.join(v) if isinstance(v, list) else v}" for k, v in t["theorems"].items() if v)
        note = f" ({t['note']})" if t.get("note") else ""
        md.append(f"| `{t['type']}.{t['method']}` ({t['package'].rsplit('/', 1)[-1]}) | {t['state']}{note} | "
                  f"{', '.join(t['missing']) or '-'} | {th} |")
    md += ["", f"## Encoders `MarshalSSZTo`: fast path per type ({ENC_PREMISE.replace('<=', '≤')})", "",
           "| type | state | fast-path theorem | spec corollary | witness | NOT proved |", "| --- | --- | --- | --- | --- | --- |"]
    for t in enc_rows:
        th = t["theorems"]
        md.append(f"| {t['type']} | {t['state']} | {', '.join(th.get('fast', [])) or '-'} | "
                  f"{', '.join(th.get('spec', [])) or '-'} | {'yes' if t.get('witness') else 'no'} | "
                  f"{'; '.join(t.get('not_proved', []))} |")
    ns = sorted({(t["package"].rsplit("/", 1)[-1], t["type"]) for t in table if t["state"] == "not started"})
    md += ["", f"## Not started ({len(ns)} types, every method)", "",
           ", ".join(f"{p}.{t}" for p, t in ns), ""]
    open(md_p, "w").write("\n".join(md))
    print(json.dumps(dict(target_ssz_methods=len(target), by_kind=by_kind,
                          development_population=tot["development_population_decoders_complete"],
                          flat_fixed_types_in_target=len(flat_target), flat_outside=len(flat_ns))))
    return 0


if __name__ == "__main__":
    sys.dont_write_bytecode = True
    if len(sys.argv) == 3 and sys.argv[1] == "names":
        open(sys.argv[2], "w").write("\n".join(names()) + "\n")
        sys.exit(0)
    if len(sys.argv) in (3, 4) and sys.argv[1] == "methods":
        sys.exit(methods(sys.argv[2], sys.argv[3] if len(sys.argv) == 4 else KR / METHODS_JSON))
    if len(sys.argv) == 6 and sys.argv[1] == "run":
        sys.exit(run(*sys.argv[2:6]))
    print(__doc__)
    sys.exit(2)
