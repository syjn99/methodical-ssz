#!/usr/bin/env python3
"""Tests of the Desc producer and the closed-world checker.

  test_desc.py prepare <work-dir>
      Produce the originals (the hand types and the types of the Prysm inventory), then
      - controls (wrong Descs; each must FAIL at its designated check) and known passes (Prysm
        only: changes the inventory binding cannot see), list mutants.txt;
      - the review mutants of review_mutants.py; it writes its forged checker line with the work
        directory path as given, so give a relative work directory;
      - list scenarios: the scenarios of review_mutants.py, the scenarios of this file, and for every wrong
        hand-type Desc an "added" (next to the originals) and an "in-place" (in place of its base) scenario;
      expect.json and batch.txt.
  run_desc_checker.sh <work-dir> <fv/kraken/lean>       (a heavy job; writes the checker result files)
  test_desc.py evaluate <work-dir> <out.json>
      Reads only the checker result files (main.result.json, scen/*.result.json). Writes
      <out.json> and <out.md> (table: case -> expected -> actual -> failing check).
      Exit status 1 on any mismatch.
Python 3 standard library only. Run with python3 -I.
"""
import copy
import json
import os
import re
import shutil
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
KRAKEN = os.path.normpath(os.path.join(HERE, "..", ".."))
TGT = "github.com/OffchainLabs/methodical-ssz/fv/kraken/target"
TGTP = TGT + "/prysm"
PRYSM = "github.com/OffchainLabs/prysm/v7/proto/prysm/v1alpha1"


def _set(path, value):
    def f(d):
        o = d
        for k in path[:-1]:
            o = o[k]
        o[path[-1]] = value(o[path[-1]]) if callable(value) else value
    return f


def _del(path):
    def f(d):
        o = d
        for k in path[:-1]:
            o = o[k]
        o.pop(path[-1])
    return f


def _both(*fs):
    def f(d):
        for g in fs:
            g(d)
    return f


def _swap(i, k):
    """Swap fields i and k in term, names and claims; claims keep their positions' offsets."""
    def f(d):
        s = d["ssz"]
        s["names"][i], s["names"][k] = s["names"][k], s["names"][i]
        s["fields"][i], s["fields"][k] = s["fields"][k], s["fields"][i]
        c = d["fields"]
        oi, ok = c[i]["offset"], c[k]["offset"]
        c[i], c[k] = c[k], c[i]
        c[i]["offset"], c[i]["index"] = oi, i
        c[k]["offset"], c[k]["index"] = ok, k
    return f


def _swap01(d):
    """Swap fields 0 and 1 with consistent offsets (the same change as prysm-status-v2-swap-fields-0-and-1 of review_mutants.py)."""
    s = d["ssz"]
    s["names"][0], s["names"][1] = s["names"][1], s["names"][0]
    s["fields"][0], s["fields"][1] = s["fields"][1], s["fields"][0]
    c = d["fields"]
    c[0], c[1] = c[1], c[0]
    c[0]["offset"], c[0]["index"] = 0, 0
    c[1]["offset"], c[1]["index"] = c[0]["width"], 1


_limit17 = _both(_set(["ssz", "fields", 0, "limit"], 17), _set(["fields", 0, "limit"], 17))
_uintw = _both(_set(["ssz", "fields", 1, "w"], 4), _set(["fields", 1, "width"], 4), _set(["fields", 2, "offset"], 5),
               _set(["fields", 3, "offset"], 9), _set(["fields", 4, "offset"], 17), _set(["fixed_size"], 18),
               _set(["fixed_part_size"], 18))

# (id, base file, what, designated check, mutation)
MUTANTS = [
    ("scalars-fixed-size-claim-16-to-17", "Scalars", "wrong fixed size (16 -> 17)", "fixed", _set(["fixed_size"], 17)),
    ("attestation-data-field-2-offset-16-to-17", "AttestationData", "wrong field offset (field 2: 16 -> 17)", "offset[2]", _set(["fields", 2, "offset"], 17)),
    ("checkpoint-field-1-width-32-to-31", "Checkpoint", "wrong field width (field 1: 32 -> 31)", "width[1]", _set(["fields", 1, "width"], 31)),
    ("nested-head-size-28-to-32", "Nested", "wrong head size (28 -> 32)", "head", _set(["fixed_part_size"], 32)),
    ("nested-field-2-variable-claim-false", "Nested", "variable field claimed fixed (field 2)", "variable[2]", _set(["fields", 2, "variable"], False)),
    ("list-uint64-limit-claim-16-to-17", "ListU64", "wrong limit claim (16 -> 17)", "limit[0]", _set(["fields", 0, "limit"], 17)),
    ("list-uint64-element-size-claim-8-to-4", "ListU64", "wrong element size (8 -> 4)", "elem[0]", _set(["fields", 0, "elem_size"], 4)),
    ("list-uint64-limit-16-to-17", "ListU64", "wrong limit against the spec (term and claim 16 -> 17)", "ref", _limit17),
    ("bit-list-kind-bit-list-to-byte-list", "BitL", "wrong kind against the spec (bitList -> byteList, claims follow)", "ref",
     _both(_set(["ssz", "fields", 0, "k"], "byteList"), _set(["fields", 0, "kind"], "byteList"))),
    ("scalars-field-1-uint16-to-uint32", "Scalars", "wrong uint width against the spec (field 1: 2 -> 4, claims follow)", "ref", _uintw),
    ("fixed-vector-term-length-4-to-0", "FixedVec", "ill-formed type (vector length 4 -> 0)", "wf", _set(["ssz", "fields", 1, "n"], 0)),
    ("prysm-beacon-block-body-altair-variable-order-reversed", "prysm_v1alpha1.BeaconBlockBodyAltair", "wrong variable-field order (reversed)", "order",
     _set(["variable_order"], lambda o: list(reversed(o)))),
    ("prysm-status-v2-field-0-kind-claim-byte-vector-to-byte-list", "prysm_v1alpha1.StatusV2", "wrong kind claim (field 0 byteVector -> byteList)", "kind[0]",
     _set(["fields", 0, "kind"], "byteList")),
    ("prysm-status-v2-field-3-offset-44-to-45", "prysm_v1alpha1.StatusV2", "wrong field offset (field 3: 44 -> 45)", "offset[3]", _set(["fields", 3, "offset"], 45)),
    ("list-uint64-limit-16-to-17-reference-null", "ListU64", "limit 16 -> 17 in term and claim, reference set to null", "ref-claim",
     _both(_limit17, _set(["reference"], None))),
    ("bit-list-kind-byte-list-reference-key-deleted", "BitL", "bitList -> byteList in term and claim, reference key deleted", "ref-claim",
     _both(_set(["ssz", "fields", 0, "k"], "byteList"), _set(["fields", 0, "kind"], "byteList"), _del(["reference"]))),
    ("scalars-type-name-to-checkpoint", "Scalars", "type name Scalars -> Checkpoint (reference stays Spec.scalarsDesc)", "hand-name", _set(["type"], "Checkpoint")),
    ("scalars-field-0-claim-name-to-zzz", "Scalars", "claim name of field 0 changed (term names unchanged)", "name[0]", _set(["fields", 0, "name"], "Zzz")),
    ("checkpoint-field-1-index-claim-1-to-7", "Checkpoint", "index claim of field 1 -> 7", "index[1]", _set(["fields", 1, "index"], 7)),
    ("scalars-names-reversed-claims-follow", "Scalars", "term field names reversed, claims follow (shapes unchanged)", "go-names",
     lambda d: d["ssz"].__setitem__("names", list(reversed(d["ssz"]["names"])))
     or [f.__setitem__("name", n) for f, n in zip(d["fields"], d["ssz"]["names"])]),
    ("list-of-containers-claim-key-elem-variable-added", "ListC", "claim key elem_variable (removed from the format) put back", "claim-keys[0]",
     _set(["fields", 0, "elem_variable"], False)),
    ("attestation-data-field-3-claim-key-callee-added", "AttestationData", "claim key callee (removed from the format) put back", "claim-keys[3]",
     _set(["fields", 3, "callee"], "github.com/x/y.Other")),
    # escapes of the table key (per file)
    ("list-uint64-limit-16-to-17-package-trailing-slash", "ListU64", "limit 16 -> 17, package gets a trailing '/', reference null", "package",
     _both(_limit17, _set(["package"], lambda p: p + "/"), _set(["reference"], None))),
    ("bit-list-kind-byte-list-type-key-deleted", "BitL", "bitList -> byteList, type key deleted, reference null", "type",
     _both(_set(["ssz", "fields", 0, "k"], "byteList"), _set(["fields", 0, "kind"], "byteList"), _del(["type"]),
           _set(["reference"], None))),
    ("scalars-field-1-uint16-to-uint32-package-key-deleted", "Scalars", "uint16 -> uint32 (claims follow), package key deleted, reference null", "package",
     _both(_uintw, _del(["package"]), _set(["reference"], None))),
    ("fixed-vector-length-4-to-5-type-zero-width-space", "FixedVec", "vector length 4 -> 5 (claims follow), type name gets U+200B, reference null", "type",
     _both(_set(["ssz", "fields", 1, "n"], 5), _set(["fields", 1, "length"], 5), _set(["fields", 1, "width"], 40),
           _set(["fixed_size"], 72), _set(["fixed_part_size"], 72), _set(["type"], "FixedVec​"),
           _set(["reference"], None))),
    # reordered / renamed fields of equal shape (table types)
    ("attestation-data-swap-slot-and-committee-index", "AttestationData", "Slot and CommitteeIndex swapped in term, names and claims", "go-names", _swap(0, 1)),
    ("attestation-data-swap-source-and-target", "AttestationData", "Source and Target swapped in term, names and claims", "go-names", _swap(3, 4)),
    ("checkpoint-field-names-crossed", "Checkpoint", "uint64 field named Root, bytes32 field named Epoch (term and claims)", "go-names",
     _both(_set(["ssz", "names"], ["Root", "Epoch"]), _set(["fields", 0, "name"], "Root"), _set(["fields", 1, "name"], "Epoch"))),
    # changes that the claims do not cover, and keys outside the table
    ("nested-inner-scalars-names-b-and-c-swapped", "Nested", "inner Scalars field names B and C swapped inside Nested (claims cover only the top)", "go-names",
     _set(["ssz", "fields", 1, "names"], ["A", "C", "B", "D", "E"])),
    ("list-uint64-under-hand-prysm-package", "ListU64", "hand ListU64 under the hand prysm package (a known package)", "hand-name",
     _set(["package"], TGTP)),
    ("checkpoint-type-name-cyrillic-c", "Checkpoint", "type name with Cyrillic 'С' (U+0421) instead of 'C'", "type", _set(["type"], "Сheckpoint")),
    ("scalars-extra-key-status", "Scalars", "extra top-level key status = SPEC", "keys", _set(["status"], "SPEC")),
    ("scalars-package-lower-case-offchainlabs", "Scalars", "package with a lower-case path segment (offchainlabs)", "package",
     _set(["package"], lambda p: p.replace("OffchainLabs", "offchainlabs"))),
    ("attestation-data-source-checkpoint-names-crossed", "AttestationData", "Checkpoint names crossed inside Source (claims cover only the top)", "go-names",
     _set(["ssz", "fields", 3, "names"], ["Root", "Epoch"])),
    ("list-uint64-schema-version-2", "ListU64", "schema fv.kraken.desc/2", "schema", _set(["schema"], "fv.kraken.desc/2")),
    ("bit-list-term-extra-key-limit2", "BitL", "unknown key inside a term (limit2 next to limit)", "keys", _set(["ssz", "fields", 0, "limit2"], 1)),
]

# attempts to escape the closed-world design (checker level)
def _scalars_as_prysm_checkpoint(d):
    # hand Scalars content relabelled as the real Prysm Checkpoint key (an excepted name)
    d["package"] = PRYSM
    d["type"] = "Checkpoint"
    d["reference"] = None


def _prysm_checkpoint_epoch_bytes8(d):
    # real Prysm Checkpoint with Epoch rewritten as byteVector 8 (same size, same names)
    d["ssz"]["fields"][0] = {"k": "byteVector", "n": 8}
    d["fields"][0]["kind"] = "byteVector"
    d["fields"][0]["length"] = 8


MUTANTS += [
    ("prysm-status-v2-swap-fields-0-and-1", "prysm_v1alpha1.StatusV2", "fields 0 and 1 swapped consistently (offsets recomputed)",
     "inventory", None),   # function set below (needs _swap01)
    ("scalars-under-prysm-checkpoint-key", "Scalars", "hand Scalars content under the real Prysm Checkpoint key", "inventory", _scalars_as_prysm_checkpoint),
    ("prysm-checkpoint-epoch-uint64-to-byte-vector-8", "prysm_v1alpha1.Checkpoint", "Prysm Checkpoint Epoch uint64 -> byteVector 8", "inventory", _prysm_checkpoint_epoch_bytes8),
    ("prysm-status-v2-field-name-with-space", "prysm_v1alpha1.StatusV2", "field name 'Fork Digest' (space) in term and claim", "names",
     _both(_set(["ssz", "names", 0], "Fork Digest"), _set(["fields", 0, "name"], "Fork Digest"))),
    ("prysm-status-v2-field-name-digit-first", "prysm_v1alpha1.StatusV2", "field name '0ForkDigest' (digit first)", "names",
     _both(_set(["ssz", "names", 0], "0ForkDigest"), _set(["fields", 0, "name"], "0ForkDigest"))),
    ("prysm-status-v2-package-dot-dot-segment", "prysm_v1alpha1.StatusV2", "package with a '..' segment", "package",
     _set(["package"], lambda q: q + "/../v1alpha1")),
    ("prysm-validator-slashed-bool-to-uint8", "prysm_v1alpha1.Validator", "Slashed bool -> uint8 (claims follow): the inventory kind binding sees it",
     "inventory", _both(_set(["ssz", "fields", 3], {"k": "uint", "w": 1}), _set(["fields", 3, "kind"], "uint"))),
    ("scalars-field-0-uint-claim-with-limit", "Scalars", "uint claim carries limit (a key of another kind)", "claim-keys[0]", _set(["fields", 0, "limit"], 16)),
    # delegated containers bound recursively, and fixed_size required
    ("prysm-attestation-inner-slot-uint64-to-byte-vector-8", "prysm_v1alpha1.Attestation", "inner AttestationData.Slot uint64 -> byteVector 8 (inside a delegated container)",
     "inventory", _set(["ssz", "fields", 1, "fields", 0], {"k": "byteVector", "n": 8})),
    ("scalars-fixed-size-key-deleted", "Scalars", "top-level key fixed_size removed", "required-keys", _del(["fixed_size"])),
    ("prysm-status-v2-fixed-size-key-deleted", "prysm_v1alpha1.StatusV2", "top-level key fixed_size removed (Prysm, variable type)", "required-keys",
     _del(["fixed_size"])),
]
MUTANTS = [m if m[4] is not None else (m[0], m[1], m[2], m[3], _swap01) for m in MUTANTS]
TEXT_MUTANTS = [   # raw-text mutants: (id, base, what, designated, text transform)
    ("list-uint64-type-key-twice-same-value", "ListU64", "the key 'type' twice with the same value", "strict-json",
     lambda t: t.replace('"type": "ListU64",', '"type": "ListU64",\n "type": "ListU64",', 1)),
    ("checkpoint-fixed-size-written-as-exponent", "Checkpoint", "fixed_size written 4e1", "strict-json", lambda t: t.replace('"fixed_size": 40', '"fixed_size": 4e1', 1)),
    ("checkpoint-fixed-size-written-with-leading-zero", "Checkpoint", "fixed_size written 040", "strict-json", lambda t: t.replace('"fixed_size": 40', '"fixed_size": 040', 1)),
    # bounds before parsing (small depth only; a 200000-level probe is not in this suite)
    ("list-uint64-arrays-nested-100-deep", "ListU64", "an extra key holding arrays nested 100 deep", "bounds",
     lambda t: t.replace('"type": "ListU64",', '"type": "ListU64",\n "x": ' + "[" * 100 + "]" * 100 + ",", 1)),
    ("list-uint64-1100000-bytes-trailing-white-space", "ListU64", "1100000 bytes of trailing white space (valid JSON)", "bounds", lambda t: t + " " * 1100000),
    ("scalars-escaped-reference-key", "Scalars", "key 'refer\\u0065nce' written with an escape next to 'reference'", "strict-json",
     lambda t: t.replace('"reference": "Spec.scalarsDesc"', '"reference": "Spec.scalarsDesc",\n "refer\\u0065nce": null', 1)),
]

# Prysm types only: no independent spec Desc offline (consensus-specs is not available); these
# changes keep names, head sizes and kinds of the committed inventory, so the binding cannot see them.
KNOWN_PASS = [
    ("prysm-sync-aggregate-bit-vector-512-to-505", "prysm_v1alpha1.SyncAggregate", "Bitvector 512 -> 505 bits (still 64 bytes), claim follows",
     _both(_set(["ssz", "fields", 0, "n"], 505), _set(["fields", 0, "length"], 505))),
    ("prysm-indexed-attestation-limit-2048-to-4096", "prysm_v1alpha1.IndexedAttestation", "list[uint64] limit 2048 -> 4096 in term and claim",
     _both(_set(["ssz", "fields", 0, "limit"], 4096), _set(["fields", 0, "limit"], 4096))),
]

# List-level scenarios of my own: (id, what, {base -> mutant id | None (drop) | "dup"}, list-level finding)
SCENARIOS = [
    ("list-uint64-replaced-by-package-trailing-slash", "list-uint64-limit-16-to-17-package-trailing-slash replaces the hand ListU64 original", {"ListU64": "list-uint64-limit-16-to-17-package-trailing-slash"}, "failed_originals"),
    ("bit-list-replaced-by-type-key-deleted", "bit-list-kind-byte-list-type-key-deleted replaces the hand BitL original", {"BitL": "bit-list-kind-byte-list-type-key-deleted"}, "missing"),
    ("scalars-replaced-by-package-key-deleted", "scalars-field-1-uint16-to-uint32-package-key-deleted replaces the hand Scalars original", {"Scalars": "scalars-field-1-uint16-to-uint32-package-key-deleted"}, "missing"),
    ("fixed-vector-replaced-by-type-zero-width-space", "fixed-vector-length-4-to-5-type-zero-width-space replaces the hand FixedVec original", {"FixedVec": "fixed-vector-length-4-to-5-type-zero-width-space"}, "missing"),
    ("originals-without-nested", "the hand Nested original is missing", {"Nested": None}, "missing"),
    ("list-of-containers-listed-twice", "the hand ListC original appears twice", {"ListC": "dup"}, "duplicate_keys"),
    ("prysm-checkpoint-replaced-by-scalars", "scalars-under-prysm-checkpoint-key replaces the Prysm Checkpoint original",
     {"prysm_v1alpha1.Checkpoint": "scalars-under-prysm-checkpoint-key"}, "failed_originals"),
    ("prysm-checkpoint-replaced-by-epoch-byte-vector-8", "prysm-checkpoint-epoch-uint64-to-byte-vector-8 replaces the Prysm Checkpoint original",
     {"prysm_v1alpha1.Checkpoint": "prysm-checkpoint-epoch-uint64-to-byte-vector-8"}, "failed_originals"),
]


def write(path, d):
    with open(path, "w") as fh:
        if isinstance(d, str):
            fh.write(d)
        else:
            json.dump(d, fh, indent=1)


def hand_base(base):
    return not (base.startswith("prysm_") or base.startswith("engine_"))


def prepare(work):
    if os.path.exists(work):
        shutil.rmtree(work)
    orig, mut, scen = (os.path.join(work, x) for x in ("orig", "mut", "scen"))
    for d in (mut, scen):
        os.makedirs(d)
    py = [sys.executable, "-I"]
    subprocess.run(py + [f"{HERE}/producer.py", orig, f"{HERE}/hand-types-ir.json", f"--refs={HERE}/hand-types-references.json"],
                   check=True, capture_output=True)
    inv = json.load(open(f"{KRAKEN}/prysm/inventory.json"))
    names = ",".join(sorted(f"{t['package']}.{t['name']}" for t in inv["types"]))
    r = subprocess.run(py + [f"{HERE}/producer.py", orig, f"{KRAKEN}/prysm/ir/ir-mainnet.json", f"--types={names}"],
                       check=True, capture_output=True, text=True)
    prod = json.loads(r.stdout)
    originals = [f"{orig}/{f}" for f in sorted(os.listdir(orig))]
    exp = {"originals": originals, "controls": {}, "known_pass": {}, "review": {}, "scenarios": {},
           "producer_skipped": prod["skipped"]}
    L = lambda base: json.load(open(f"{orig}/{base}.desc.json"))
    for mid, base, what, check, fn in MUTANTS:
        d = L(base)
        fn(d)
        write(f"{mut}/{mid}.desc.json", d)
        exp["controls"][f"{mut}/{mid}.desc.json"] = {"id": mid, "base": base, "twin": f"{orig}/{base}.desc.json",
                                                    "what": what, "designated": check}
    for mid, base, what, check, tf in TEXT_MUTANTS:
        write(f"{mut}/{mid}.desc.json", tf(open(f"{orig}/{base}.desc.json").read()))
        exp["controls"][f"{mut}/{mid}.desc.json"] = {"id": mid, "base": base, "twin": f"{orig}/{base}.desc.json",
                                                    "what": what, "designated": check}
    for mid, base, what, fn in KNOWN_PASS:
        d = L(base)
        fn(d)
        write(f"{mut}/{mid}.desc.json", d)
        exp["known_pass"][f"{mut}/{mid}.desc.json"] = {"id": mid, "base": base, "what": what}
    # review mutants and their list scenarios
    subprocess.run(py + [f"{HERE}/review_mutants.py", orig, work], check=True, capture_output=True)
    review = json.load(open(f"{work}/review-mutants.json"))
    for m in review["mutants"]:
        exp["review"][m["file"]] = {"id": m["id"], "base": m["base"], "what": m["what"],
                                    "reviewer_expects": m["sound_checker_should"]}
    batch = []
    for sc in review["scenarios"]:
        exp["scenarios"][sc["id"]] = {"source": "review", "what": sc["what"], "list": sc["list"], "expect": "FAIL"}
    # the scenarios of this file
    for sid, what, repl, finding in SCENARIOS:
        lst = []
        for p in originals:
            base = os.path.basename(p)[:-len(".desc.json")]
            v = repl.get(base, p)
            if base in repl:
                if v is None:
                    continue
                if v == "dup":
                    lst += [p, p]
                    continue
                v = f"{mut}/{v}.desc.json"
            lst.append(v)
        write(f"{scen}/{sid}.txt", "\n".join(lst) + "\n")
        if sid in exp["scenarios"]:
            raise SystemExit(f"duplicate scenario id {sid}")
        exp["scenarios"][sid] = {"source": "test_desc", "what": what, "list": f"{scen}/{sid}.txt", "expect": "FAIL", "finding": finding}
    # added and in-place scenarios (source "boundary"): every wrong hand-type Desc (controls and review mutants with a
    # hand base that a sound checker must reject), added next to the originals and in place of its base.
    # The id starts with the set of the mutant, because a control and a review mutant can have the same id.
    wrong = [("control", m["id"], m["base"], p) for p, m in exp["controls"].items() if hand_base(m["base"])]
    wrong += [("review", m["id"], m["base"], p) for p, m in exp["review"].items()
              if hand_base(m["base"]) and m["reviewer_expects"] == "FAIL"]
    for kind, mid, base, p in wrong:
        bp = f"{orig}/{base}.desc.json"
        for how, lst in (("added", originals + [p]), ("in-place", [p if q == bp else q for q in originals])):
            sid = f"{kind}-{mid}-{how}"
            if sid in exp["scenarios"]:
                raise SystemExit(f"duplicate scenario id {sid}")
            write(f"{scen}/{sid}.txt", "\n".join(lst) + "\n")
            exp["scenarios"][sid] = {"source": "boundary", "what": f"{mid} {how}", "list": f"{scen}/{sid}.txt", "expect": "FAIL",
                                     "mutant": p, "base": base}
    for sid, sc in exp["scenarios"].items():
        batch.append(f"{sid}\t{sc['list']}\t{scen}/{sid}.result.json")
        sc["result"] = f"{scen}/{sid}.result.json"
    write(f"{work}/batch.txt", "\n".join(batch) + "\n")
    write(f"{work}/list.txt", "\n".join(originals) + "\n")
    write(f"{work}/mutants.txt", "\n".join(list(exp["controls"]) + list(exp["known_pass"]) + list(exp["review"])) + "\n")
    json.dump(exp, open(f"{work}/expect.json", "w"), indent=1)
    print(json.dumps({"originals": len(originals), "controls": len(exp["controls"]), "known_pass": len(exp["known_pass"]),
                      "review": len(exp["review"]), "scenarios": len(exp["scenarios"]),
                      "boundary_wrong_hand_descs": len(wrong), "producer_skipped": prod["skipped"]}))


def evaluate(work, out):
    exp = json.load(open(f"{work}/expect.json"))
    rcs = dict(l.split() for l in open(f"{work}/logs/rc.txt"))
    res = json.load(open(f"{work}/main.result.json"))
    recs = {}
    for r in res["records"]:
        recs.setdefault((r["role"], r["path"]), r)
    get = lambda role, p: recs.get((role, p), {"result": "not run", "status": None, "failed": []})
    rows, bad = [], 0
    for p in exp["originals"]:
        g = get("original", p)
        ok = g["result"] == "PASS"
        bad += not ok
        rows.append({"file": os.path.basename(p), "role": "original", "result": g["result"], "status": g["status"], "as_expected": ok})
    main_ok = res["verdict"] == "OK" and rcs.get("main") == "0"
    bad += not main_ok
    for p, m in exp["controls"].items():
        g = get("mutant", p)
        twin = get("original", m["twin"])["result"]
        ok = g["result"] == "FAIL" and m["designated"] in g["failed"] and twin == "PASS"
        bad += not ok
        rows.append({"file": os.path.basename(p), "role": "control", "id": m["id"], "base": m["base"], "what": m["what"],
                     "designated": m["designated"], "result": g["result"], "status": g["status"], "failed_checks": g["failed"],
                     "twin_result": twin, "as_expected": ok})
    for p, m in exp["known_pass"].items():
        g = get("mutant", p)
        rows.append({"file": os.path.basename(p), "role": "known-pass", "id": m["id"], "base": m["base"], "what": m["what"],
                     "result": g["result"], "status": g["status"], "failed_checks": g["failed"],
                     "as_expected": g["result"] in ("PASS", "FAIL"),
                     "note": "Prysm type: no independent spec; PASS is the known limit, FAIL means the inventory binding saw it"})
    scen_rows = []
    for sid, sc in exp["scenarios"].items():
        try:
            r = json.load(open(sc["result"]))
            verdict, lst = r["verdict"], r["list"]
        except (OSError, ValueError):
            verdict, lst = "no result", {}
        ok = verdict == "FAIL" and (not sc.get("finding") or bool(lst.get(sc["finding"])))
        bad += not ok
        scen_rows.append({"id": sid, "source": sc["source"], "what": sc["what"], "verdict": verdict,
                          "findings": {k: v for k, v in lst.items() if v and k != "table_self_check"}, "expected_finding": sc.get("finding"),
                          "as_expected": ok})
    rep_rows = []
    for p, m in exp["review"].items():
        g = get("mutant", p)
        want = m["reviewer_expects"]
        hand = hand_base(m["base"])
        if want == "FAIL":
            ok = g["result"] == "FAIL" or not hand   # Prysm-base PASS = known limit (no independent spec)
        else:
            ok = True
        bad += not ok
        rep_rows.append({"id": m["id"], "base": m["base"], "hand_type": hand, "what": m["what"],
                         "reviewer_expects": want, "result": g["result"], "status": g["status"], "failed_checks": g["failed"],
                         "as_expected": ok,
                         "note": "" if g["result"] == "FAIL" or want != "FAIL" else "Prysm type: known limit"})
    wrong_hand_pass = [r["id"] for r in rep_rows if r["hand_type"] and r["reviewer_expects"] == "FAIL" and r["result"] != "FAIL"] + \
                      [r["id"] for r in rows if r["role"] == "control" and r["result"] != "FAIL"]
    boundary = [r for r in scen_rows if r["source"] == "boundary"]
    summary = {
        "main_verdict": res["verdict"], "main_checker_rc": rcs.get("main"), "batch_rc": rcs.get("batch"),
        "inventory": res["inventory"], "expected_key_count": res["expected_key_count"],
        "originals": len(exp["originals"]), "originals_pass": sum(r["role"] == "original" and r["as_expected"] for r in rows),
        "originals_spec": sum(r["role"] == "original" and r["status"] == "SPEC" for r in rows),
        "originals_none": sum(r["role"] == "original" and r["status"] == "NONE" for r in rows),
        "controls": len(exp["controls"]), "controls_as_expected": sum(r["role"] == "control" and r["as_expected"] for r in rows),
        "known_pass_prysm": len(exp["known_pass"]),
        "known_pass_result": {r["id"]: r["result"] for r in rows if r["role"] == "known-pass"},
        "review": len(rep_rows),
        "review_fail": sum(r["result"] == "FAIL" for r in rep_rows), "review_pass": sum(r["result"] == "PASS" for r in rep_rows),
        "review_pass_ids": [r["id"] for r in rep_rows if r["result"] == "PASS"],
        "wrong_hand_type_descs_passing_per_file": wrong_hand_pass,
        "scenarios": len(scen_rows), "scenarios_as_expected": sum(r["as_expected"] for r in scen_rows),
        "boundary_scenarios": len(boundary), "boundary_scenarios_verdict_fail": sum(r["verdict"] == "FAIL" for r in boundary),
        "unexpected": bad, "producer_skipped": exp["producer_skipped"],
    }
    strip = lambda s: s.replace(work + "/", "")
    full = json.loads(strip(json.dumps({"schema": "fv.kraken.desc-test/4", "summary": summary, "rows": rows,
                                        "scenarios": scen_rows, "review": rep_rows})))
    json.dump(full, open(out, "w"), indent=1)
    md = ["# Desc checker: controls, review mutants and list scenarios", "",
          "Generated by `gen/desc/test_desc.py evaluate` from the checker result files. Do not edit.", "",
          "## Summary", "", "```", json.dumps(full["summary"], indent=1), "```", "",
          "## Controls and known passes", "", "| id | role | base | expected | result | status | failed checks |",
          "| --- | --- | --- | --- | --- | --- | --- |"]
    for r in full["rows"]:
        if r["role"] != "original":
            md.append(f"| {r['id']} | {r['role']} | {r['base']} | {r.get('designated', 'PASS or FAIL')} | {r['result']} | {r['status']} | "
                      f"{', '.join(r.get('failed_checks', []))} |")
    md += ["", "## Review mutants of review_mutants.py", "",
           "| id | base | expected by the mutant file | result | status | failed checks | note |", "| --- | --- | --- | --- | --- | --- | --- |"]
    for r in full["review"]:
        md.append(f"| {r['id']} | {r['base']} | {r['reviewer_expects']} | {r['result']} | {r['status']} | "
                  f"{', '.join(r['failed_checks'])} | {r['note']} |")
    md += ["", "## List scenarios (review_mutants.py, this file, added and in-place scenarios)", "",
           "| id | source | verdict | findings | as expected |", "| --- | --- | --- | --- | --- |"]
    for r in full["scenarios"]:
        f = "; ".join(f"{k}: {len(v) if isinstance(v, list) else v}" for k, v in r["findings"].items())
        md.append(f"| {r['id']} | {r['source']} | {r['verdict']} | {f} | {r['as_expected']} |")
    open(out[:-5] + ".md", "w").write("\n".join(md) + "\n")
    print(json.dumps(full["summary"], indent=1))
    return 1 if bad else 0


if __name__ == "__main__":
    if sys.argv[1] == "prepare":
        prepare(sys.argv[2])
    elif sys.argv[1] == "evaluate":
        sys.exit(evaluate(sys.argv[2], sys.argv[3]))
    else:
        raise SystemExit(__doc__)
