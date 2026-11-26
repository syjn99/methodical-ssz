#!/usr/bin/env python3
"""Review mutants and list scenarios for the Desc checker desc-checker/DescChecker.lean.

Usage: review_mutants.py <orig-dir> <work-dir>
Reads <orig-dir>/*.desc.json (the original Descs that test_desc.py prepare writes).
Writes <work>/review-mutants/<id>.desc.json, <work>/forge/Nested.desc.json, <work>/scen/<id>.txt
(and the extra files of the scenarios), and <work>/review-mutants.json (mutants and scenarios).
The forged checker line of the mutant engine-withdrawal-field-name-forges-file-record names a path
under <work-dir> as given. Give a relative work directory, so that the checker result holds no machine path.
Python 3 standard library only. Run with python3 -I.
"""
import copy
import json
import os
import shutil
import sys

ORIG, WORK = sys.argv[1], sys.argv[2]
OUT = f"{WORK}/review-mutants"
SCEN = f"{WORK}/scen"
FORGE = f"{WORK}/forge"
for d in (OUT, SCEN, FORGE):
    os.makedirs(d, exist_ok=True)
TGT = "github.com/OffchainLabs/methodical-ssz/fv/kraken/target"
PV1 = "github.com/OffchainLabs/prysm/v7/proto/prysm/v1alpha1"
PENG = "github.com/OffchainLabs/prysm/v7/proto/engine/v1"


def L(base):
    return json.load(open(f"{ORIG}/{base}.desc.json"))


def fnv(b):
    h = 14695981039346656037
    for x in b:
        h = ((h ^ x) * 1099511628211) & 0xFFFFFFFFFFFFFFFF
    return h


M = []  # {id, base, what, sound_checker_should, file}


def add(mid, base, what, should, fn=None, text=None):
    """Write one mutant. fn changes the Desc in place, or returns a replacement (JSON value or raw text)."""
    if text is None:
        d = L(base)
        r = fn(d)
        text = r if isinstance(r, str) else json.dumps(d if r is None else r, indent=1)
    p = f"{OUT}/{mid}.desc.json"
    if any(m["id"] == mid for m in M):
        raise SystemExit(f"duplicate mutant id {mid}")
    M.append({"id": mid, "base": base, "what": what, "sound_checker_should": should, "file": p})
    with open(p, "w") as fh:
        fh.write(text)


def both(*fs):
    def f(d):
        for g in fs:
            g(d)
    return f


def setk(k, v):
    def f(d):
        d[k] = v(d[k]) if callable(v) else v
    return f


noref = setk("reference", None)


# wrong contents of hand types (term and claims consistent with each other)
def w_scalars(d):          # field 1 uint16 -> uint32
    d["ssz"]["fields"][1]["w"] = 4
    d["fields"][1]["width"] = 4
    for i, o in ((2, 5), (3, 9), (4, 17)):
        d["fields"][i]["offset"] = o
    d["fixed_size"] = d["fixed_part_size"] = 18


def w_listu64(d):          # limit 16 -> 17
    d["ssz"]["fields"][0]["limit"] = 17
    d["fields"][0]["limit"] = 17


def w_nested(d):           # inner ListU64 limit 16 -> 17
    d["ssz"]["fields"][2]["fields"][0]["limit"] = 17


def w_bitl(d):             # bitList -> byteList
    d["ssz"]["fields"][0]["k"] = "byteList"
    d["fields"][0]["kind"] = "byteList"


def w_fixedvec(d):         # vector length 4 -> 5
    d["ssz"]["fields"][1]["n"] = 5
    d["fields"][1]["length"] = 5
    d["fields"][1]["width"] = 40
    d["fixed_size"] = d["fixed_part_size"] = 72


def w_cp(d):               # Epoch uint64 -> byteVector 8
    d["ssz"]["fields"][0] = {"k": "byteVector", "n": 8}
    d["fields"][0]["kind"] = "byteVector"
    d["fields"][0]["length"] = 8


# ---- single changes of the term, the claims and the reference ----
def limit17_noref(d):
    d["ssz"]["fields"][0]["limit"] = 17; d["fields"][0]["limit"] = 17; d["reference"] = None
add("list-uint64-limit-16-to-17-reference-null", "ListU64", "limit 16->17 in term and claim, reference set to null",
    "FAIL", limit17_noref)


def bytelist_noref_key(d):
    d["ssz"]["fields"][0]["k"] = "byteList"; d["fields"][0]["kind"] = "byteList"; del d["reference"]
add("bit-list-kind-byte-list-reference-key-deleted", "BitL", "bitList->byteList in term and claim, reference key deleted",
    "FAIL", bytelist_noref_key)


def slashed_uint8(d):
    d["ssz"]["fields"][3] = {"k": "uint", "w": 1}; d["fields"][3]["kind"] = "uint"
add("prysm-validator-slashed-bool-to-uint8", "prysm_v1alpha1.Validator", "Slashed bool -> uint8, claim follows", "FAIL",
    slashed_uint8)


def bitvec505(d):
    d["ssz"]["fields"][0]["n"] = 505; d["fields"][0]["length"] = 505
add("prysm-sync-aggregate-bit-vector-512-to-505", "prysm_v1alpha1.SyncAggregate",
    "Bitvector 512 -> 505 bits (still 64 bytes), claim follows", "FAIL", bitvec505)


def limit4096(d):
    d["ssz"]["fields"][0]["limit"] = 4096; d["fields"][0]["limit"] = 4096
add("prysm-indexed-attestation-limit-2048-to-4096", "prysm_v1alpha1.IndexedAttestation",
    "list[uint64] limit 2048 -> 4096 in term and claim", "FAIL", limit4096)


def swap01(d):
    s = d["ssz"]; s["names"][0], s["names"][1] = s["names"][1], s["names"][0]
    s["fields"][0], s["fields"][1] = s["fields"][1], s["fields"][0]
    f = d["fields"]; f[0], f[1] = f[1], f[0]
    f[0]["offset"] = 0; f[0]["index"] = 0; f[1]["offset"] = f[0]["width"]; f[1]["index"] = 1
add("prysm-status-v2-swap-fields-0-and-1", "prysm_v1alpha1.StatusV2", "fields 0 and 1 swapped consistently", "FAIL", swap01)
add("scalars-field-0-claim-name-to-zzz", "Scalars", "claim name of field 0 changed (term names unchanged)", "FAIL",
    lambda d: d["fields"][0].__setitem__("name", "Zzz"))
add("scalars-term-names-reversed", "Scalars", "term field names reversed, shapes unchanged", "FAIL",
    lambda d: d["ssz"].__setitem__("names", list(reversed(d["ssz"]["names"]))))
add("list-of-containers-claim-key-elem-variable-added", "ListC", "claim key elem_variable (not in the format) set to false",
    "FAIL", lambda d: d["fields"][0].__setitem__("elem_variable", False))
add("attestation-data-field-3-claim-key-callee-added", "AttestationData", "claim key callee (not in the format) on field 3",
    "FAIL", lambda d: d["fields"][3].__setitem__("callee", "github.com/x/y.Other"))
add("checkpoint-field-1-index-claim-1-to-7", "Checkpoint", "index claim of field 1 -> 7", "FAIL",
    lambda d: d["fields"][1].__setitem__("index", 7))
add("scalars-type-name-to-checkpoint", "Scalars", "type name Scalars -> Checkpoint (reference stays Spec.scalarsDesc)", "FAIL",
    setk("type", "Checkpoint"))
add("scalars-reference-to-checkpoint", "Scalars", "reference Spec.scalarsDesc -> Spec.checkpointDesc", "FAIL",
    setk("reference", "Spec.checkpointDesc"))
add("checkpoint-extra-field-claim", "Checkpoint", "one extra field claim", "FAIL",
    lambda d: d["fields"].append(dict(d["fields"][-1], index=2, offset=40)))
add("checkpoint-term-field-0-uint64-to-uint32", "Checkpoint", "term uint 8 -> 4 bytes, claims unchanged", "FAIL",
    lambda d: d["ssz"]["fields"][0].__setitem__("w", 4))
add("nested-field-2-offset-24-to-20", "Nested", "variable field 2 offset 24 -> 20", "FAIL",
    lambda d: d["fields"][2].__setitem__("offset", 20))
add("prysm-attestation-inner-slot-uint64-to-byte-vector-8", "prysm_v1alpha1.Attestation",
    "inner AttestationData.Slot uint64 -> byteVector 8", "FAIL",
    lambda d: d["ssz"]["fields"][1]["fields"].__setitem__(0, {"k": "byteVector", "n": 8}))


def bytes0(d):
    d["ssz"]["fields"][1]["n"] = 0; d["fields"][1]["length"] = 0; d["fields"][1]["width"] = 0
add("prysm-sync-aggregate-field-1-length-96-to-0", "prysm_v1alpha1.SyncAggregate",
    "byteVector 96 -> 0 with claims (offsets consistent)", "FAIL", bytes0)
add("list-uint64-variable-order-0-twice", "ListU64", "variable_order [0] -> [0,0]", "FAIL", setk("variable_order", [0, 0]))
add("list-uint64-fixed-size-null-to-4", "ListU64", "fixed_size null -> 4", "FAIL", setk("fixed_size", 4))


# ---- a wrong hand-type Desc under a key outside the (package, type) table ----
def limit17(d):
    d["ssz"]["fields"][0]["limit"] = 17
    d["fields"][0]["limit"] = 17


def a1(d):
    limit17(d); d["package"] += "/"; d["reference"] = None
add("list-uint64-limit-16-to-17-package-trailing-slash", "ListU64",
    "limit 16->17 (term+claim), package gets a trailing '/', reference null", "FAIL", a1)


def a2(d):
    d["ssz"]["fields"][0]["k"] = "byteList"; d["fields"][0]["kind"] = "byteList"; del d["type"]; d["reference"] = None
add("bit-list-kind-byte-list-type-key-deleted", "BitL", "bitList->byteList (term+claim), `type` key deleted, reference null",
    "FAIL", a2)


def uintw(d):
    d["ssz"]["fields"][1]["w"] = 4; d["fields"][1]["width"] = 4; d["fields"][2]["offset"] = 5
    d["fields"][3]["offset"] = 9; d["fields"][4]["offset"] = 17; d["fixed_size"] = 18; d["fixed_part_size"] = 18


def a3(d):
    uintw(d); del d["package"]; d["reference"] = None
add("scalars-field-1-uint16-to-uint32-package-key-deleted", "Scalars",
    "uint16->uint32 with all claims following, `package` key deleted, reference null", "FAIL", a3)


def a4(d):
    d["ssz"]["fields"][0] = {"k": "byteVector", "n": 8}; d["fields"][0]["kind"] = "byteVector"; d["fields"][0]["length"] = 8
    d["package"] = PV1; d["reference"] = None
add("checkpoint-epoch-to-byte-vector-8-under-prysm-package", "Checkpoint",
    "hand Checkpoint, Epoch uint64->byteVector 8 (claims follow), package = the real Prysm package, reference null", "FAIL", a4)


def a5(d):
    d["ssz"]["fields"][1]["n"] = 5; d["fields"][1]["length"] = 5; d["fields"][1]["width"] = 40
    d["fixed_size"] = 72; d["fixed_part_size"] = 72; d["type"] = "FixedVec​"; d["reference"] = None
add("fixed-vector-length-4-to-5-type-zero-width-space", "FixedVec",
    "vector length 4->5 (claims follow), type name gets U+200B, reference null", "FAIL", a5)

# ---- reference variants ----
add("prysm-checkpoint-reference-to-checkpoint", "prysm_v1alpha1.Checkpoint",
    "unchanged Prysm Checkpoint, reference set to Spec.checkpointDesc (type not in table)", "FAIL",
    setk("reference", "Spec.checkpointDesc"))


def ref_array(d):
    limit17(d); d["reference"] = ["Spec.listU64Desc"]
add("list-uint64-limit-16-to-17-reference-array", "ListU64", "limit 16->17, reference is a JSON array", "FAIL", ref_array)


def listc_body(d):
    c = L("ListC"); c["type"] = "ListU64"; c["package"] = d["package"]; c["reference"] = "Spec.listOfContainersDesc"
    return c
add("list-of-containers-body-under-list-uint64-key", "ListU64",
    "whole body of ListC under type ListU64, reference Spec.listOfContainersDesc", "FAIL", listc_body)


def status_none(d):
    uintw(d); d["reference"] = None; d["status"] = "NONE"; d["spec"] = "NONE"; d["ref_status"] = "NONE"
add("scalars-field-1-uint16-to-uint32-status-keys-none", "Scalars",
    "uint16->uint32 (claims follow), reference null, file carries status/spec/ref_status = NONE", "FAIL", status_none)


def ref_space(d):
    limit17(d); d["reference"] = "Spec.listU64Desc "
add("list-uint64-limit-16-to-17-reference-trailing-space", "ListU64",
    "limit 16->17, reference 'Spec.listU64Desc ' (trailing space)", "FAIL", ref_space)


# ---- reordered or duplicated fields with consistent names (hand types, same shape) ----
def swap(i, k):
    def f(d):
        s = d["ssz"]
        s["names"][i], s["names"][k] = s["names"][k], s["names"][i]
        s["fields"][i], s["fields"][k] = s["fields"][k], s["fields"][i]
        f_ = d["fields"]
        oi, ok_ = f_[i]["offset"], f_[k]["offset"]
        f_[i], f_[k] = f_[k], f_[i]
        f_[i]["offset"], f_[i]["index"] = oi, i
        f_[k]["offset"], f_[k]["index"] = ok_, k
    return f
add("attestation-data-swap-slot-and-committee-index", "AttestationData",
    "fields 0 (Slot) and 1 (CommitteeIndex) swapped in term, names and claims; shapes are equal", "FAIL", swap(0, 1))
add("attestation-data-swap-source-and-target", "AttestationData",
    "fields 3 (Source) and 4 (Target) swapped in term, names and claims; shapes are equal", "FAIL", swap(3, 4))


def both_epoch(d):
    d["ssz"]["names"] = ["Epoch", "Epoch"]; d["fields"][1]["name"] = "Epoch"
add("checkpoint-both-fields-named-epoch", "Checkpoint", "both fields named Epoch in term and claims", "FAIL", both_epoch)


def crossed(d):
    d["ssz"]["names"] = ["Root", "Epoch"]; d["fields"][0]["name"] = "Root"; d["fields"][1]["name"] = "Epoch"
add("checkpoint-field-names-crossed", "Checkpoint",
    "names crossed: uint64 field named Root, bytes32 field named Epoch (term and claims agree)", "FAIL", crossed)


# ---- equal only after a normalisation that the checker must not do ----
def bytevec_as_vector(d):
    d["ssz"]["fields"][0] = {"k": "vector", "elem": {"k": "uint", "w": 1}, "n": 32}
    d["fields"][0].update(kind="vector", elem_size=1)
add("fixed-vector-byte-vector-32-to-uint8-vector", "FixedVec",
    "byteVector 32 -> vector(uint8) 32 (same bytes, different Desc), claims follow", "FAIL", bytevec_as_vector)


def bitvec_as_uint8(d):
    d["ssz"]["fields"][0] = {"k": "uint", "w": 1}; d["fields"][0]["kind"] = "uint"; d["fields"][0].pop("length")
add("bit-vector-bit-vector-4-to-uint8", "BitVec", "bitVector 4 -> uint8 (same width), claims follow", "FAIL", bitvec_as_uint8)
add("nested-inner-list-uint64-limit-16-to-17", "Nested", "inner ListU64 limit 16->17 inside Nested (no claim covers it)",
    "FAIL", w_nested)


def extra_bool(d):
    d["ssz"]["names"].append("Z"); d["ssz"]["fields"].append({"k": "bool"})
    d["fields"].append({"name": "Z", "index": 5, "offset": 16, "width": 1, "variable": False, "kind": "bool"})
    d["fixed_size"] = 17; d["fixed_part_size"] = 17
add("scalars-extra-bool-field-at-end", "Scalars", "one extra bool field at the end, all claims consistent", "FAIL", extra_bool)
add("list-uint64-limit-written-with-decimal-point", "ListU64", "limit written 16.0 in term and claim (value equal; informational)",
    "either", lambda d: json.dumps(d, indent=1).replace('"limit": 16', '"limit": 16.0'))


def dupkeys(first_wrong):
    def f(d):
        good = copy.deepcopy(d)
        bad = copy.deepcopy(d)
        limit17(bad)
        a, b = (bad, good) if first_wrong else (good, bad)
        ja, jb = json.dumps(a, indent=1), json.dumps(b, indent=1)
        return ja.rstrip()[:-1].rstrip() + ",\n" + jb.lstrip()[1:]
    return f
add("list-uint64-all-keys-twice-first-copy-wrong", "ListU64",
    "every key twice: first copy limit 17, second copy correct (Python json reads the second)",
    "either (must agree with last-wins)", dupkeys(True))
add("list-uint64-all-keys-twice-second-copy-wrong", "ListU64",
    "every key twice: first copy correct, second copy limit 17 (Python json reads the second = wrong)", "FAIL", dupkeys(False))

# ---- malformed JSON shapes ----
add("checkpoint-top-level-array", "Checkpoint", "top level is a JSON array holding the Desc", "FAIL",
    lambda d: [copy.deepcopy(d)])
add("list-uint64-term-is-string", "ListU64", "ssz is the string 'Spec.listU64Desc'", "FAIL",
    setk("ssz", "Spec.listU64Desc"))


def no_name_index(d):
    for f in d["fields"]:
        f.pop("name"); f.pop("index")
add("checkpoint-claims-without-name-and-index", "Checkpoint", "claims without name and index keys", "FAIL", no_name_index)
add("checkpoint-field-1-index-is-string", "Checkpoint", "index of field 1 is the string '1'", "FAIL",
    lambda d: d["fields"][1].__setitem__("index", "1"))
add("checkpoint-claims-truncated-to-1-field", "Checkpoint", "claims truncated to one field", "FAIL",
    lambda d: d.__setitem__("fields", d["fields"][:1]))
add("checkpoint-empty-file", "Checkpoint", "empty file", "FAIL", lambda d: "")
add("checkpoint-term-names-1-for-2-fields", "Checkpoint", "term names has 1 entry for 2 fields", "FAIL",
    lambda d: d["ssz"].__setitem__("names", ["Epoch"]))
add("checkpoint-field-0-width-negative", "Checkpoint", "width of field 0 is -8", "FAIL",
    lambda d: d["fields"][0].__setitem__("width", -8))
add("list-uint64-term-limit-16-to-17-claim-unchanged", "ListU64", "term limit 17, claim limit 16, reference kept", "FAIL",
    lambda d: d["ssz"]["fields"][0].__setitem__("limit", 17))
add("checkpoint-term-uint-width-is-string", "Checkpoint", "term uint width is the string '8'", "FAIL",
    lambda d: d["ssz"]["fields"][0].__setitem__("w", "8"))


def unknown_keys(d):
    d["ssz"]["fields"][0]["extra"] = {"k": "uint", "w": 4}; d["bogus_claim"] = "x"; d["fields"][0]["callee"] = "a.B"
add("checkpoint-unknown-keys-in-term-top-level-and-claim", "Checkpoint",
    "unknown keys in term, top level and a claim (informational: ignored or rejected?)", "either", unknown_keys)

# ---- leave the table, or detach the key from the content ----
add("scalars-field-1-uint16-to-uint32-under-prysm-package", "Scalars",
    "wrong Scalars (uint16->uint32) under the real Prysm v1alpha1 package; no Prysm type has this name",
    "FAIL", both(w_scalars, setk("package", PV1), noref))
add("nested-inner-limit-16-to-17-type-name-lower-case", "Nested", "wrong Nested (inner limit 17), type name 'nested' (case variant)",
    "FAIL", both(w_nested, setk("type", "nested"), noref))
add("list-uint64-limit-16-to-17-type-name-trailing-underscore", "ListU64", "wrong ListU64 (limit 17), type name 'ListU64_'",
    "FAIL", both(w_listu64, setk("type", "ListU64_"), noref))
add("bit-list-kind-byte-list-under-engine-package", "BitL", "wrong BitL (byteList) under the Prysm engine package", "FAIL",
    both(w_bitl, setk("package", PENG), noref))
add("fixed-vector-length-4-to-5-type-name-arabic-digit", "FixedVec",
    "wrong FixedVec, type name 'FixedVec' + U+0661 (non-ASCII digit)", "FAIL",
    both(w_fixedvec, setk("type", "FixedVec١"), noref))
add("list-uint64-limit-16-to-17-package-cyrillic-o", "ListU64",
    "wrong ListU64, package with Cyrillic 'о' (U+043E) in 'OffchainLabs'", "FAIL",
    both(w_listu64, setk("package", lambda p: p.replace("Offchain", "Оffchain")), noref))
add("scalars-field-1-uint16-to-uint32-type-name-leading-space", "Scalars", "wrong Scalars, type ' Scalars' (leading space)",
    "FAIL", both(w_scalars, setk("type", " Scalars"), noref))
add("scalars-field-1-uint16-to-uint32-package-trailing-space", "Scalars", "wrong Scalars, package + trailing space", "FAIL",
    both(w_scalars, setk("package", lambda p: p + " "), noref))
add("bit-list-kind-byte-list-type-name-nul", "BitL", "wrong BitL, type 'BitL' + U+0000", "FAIL",
    both(w_bitl, setk("type", "BitL\u0000"), noref))
add("scalars-field-1-uint16-to-uint32-type-name-array", "Scalars", "wrong Scalars, type is the array ['Scalars']", "FAIL",
    both(w_scalars, setk("type", ["Scalars"]), noref))
add("checkpoint-epoch-to-byte-vector-8-package-upper-case-prysm", "Checkpoint",
    "wrong hand Checkpoint, package path upper-cased segment 'Prysm'", "FAIL",
    both(w_cp, setk("package", TGT + "/Prysm"), noref))
add("checkpoint-epoch-to-byte-vector-8-under-engine-package", "Checkpoint",
    "wrong hand Checkpoint under the Prysm engine package (no such engine type)", "FAIL",
    both(w_cp, setk("package", PENG), noref))
# duplicate JSON keys: the first 'type' is the table name, the later one leaves the table
d = L("ListU64"); w_listu64(d); d["reference"] = None
t = json.dumps(d, indent=1)
t = t.replace('"type": "ListU64",', '"type": "ListU64",\n "type": "ListU64x",', 1)
add("list-uint64-limit-16-to-17-second-type-key", "ListU64", "wrong ListU64, two 'type' keys (ListU64 then ListU64x)", "FAIL",
    text=t)


# ---- in the table: content wrong, key right ----
def root_vector_u8(d):  # Root byteVector 32 -> vector(uint8, 32): same bytes on the wire, another Desc
    d["ssz"]["fields"][1] = {"k": "vector", "elem": {"k": "uint", "w": 1}, "n": 32}
    d["fields"][1].update({"kind": "vector", "length": 32, "elem_size": 1})
add("checkpoint-root-byte-vector-32-to-uint8-vector", "Checkpoint",
    "Root byteVector 32 -> vector(uint8,32) (same wire bytes, other Desc; needs normalisation to match)", "FAIL", root_vector_u8)


def bits_4_to_8(d):
    d["ssz"]["fields"][0]["n"] = 8
    d["fields"][0]["length"] = 8
add("bit-vector-length-4-to-8", "BitVec", "bitVector 4 -> 8 bits (still 1 byte)", "FAIL", bits_4_to_8)


def root_bitvector(d):
    d["ssz"]["fields"][2] = {"k": "bitVector", "n": 256}
    d["fields"][2].update({"kind": "bitVector", "length": 256})
add("attestation-data-beacon-block-root-to-bit-vector-256", "AttestationData",
    "BeaconBlockRoot byteVector 32 -> bitVector 256 (same size)", "FAIL", root_bitvector)


def bool_uint8(d):
    d["ssz"]["fields"][4] = {"k": "uint", "w": 1}
    d["fields"][4]["kind"] = "uint"
add("scalars-field-4-bool-to-uint8", "Scalars", "E bool -> uint8 on a hand type", "FAIL", bool_uint8)


def names_lower(d):
    d["ssz"]["names"] = [n.lower() for n in d["ssz"]["names"]]
    for f, n in zip(d["fields"], d["ssz"]["names"]):
        f["name"] = n
add("scalars-field-names-lower-case", "Scalars", "field names lower-cased (the spec structure names, not the Go names)",
    "FAIL", names_lower)
add("list-of-containers-inner-limit-16-to-32", "ListC", "inner ListU64 limit 16 -> 32 inside ListC", "FAIL",
    lambda d: d["ssz"]["fields"][0]["elem"]["fields"][0].__setitem__("limit", 32))
add("list-of-containers-inner-field-name-lower-case", "ListC", "inner ListU64 field name 'L' -> 'l' inside ListC", "FAIL",
    lambda d: d["ssz"]["fields"][0]["elem"].__setitem__("names", ["l"]))
add("scalars-reference-trailing-space", "Scalars", "correct content, reference 'Spec.scalarsDesc ' (trailing space)", "FAIL",
    setk("reference", "Spec.scalarsDesc "))
add("nested-reference-null", "Nested", "correct content, reference null (table type claiming status NONE)", "FAIL", noref)
add("bit-list-reference-array", "BitL", "correct content, reference is an array", "FAIL", setk("reference", ["Spec.bitListDesc"]))
add("scalars-field-0-claims-limit-length-and-element-size", "Scalars",
    "uint field 0 claims limit 17, length 3, elem_size 9 (attributes that do not apply to a uint)", "FAIL",
    lambda d: d["fields"][0].update({"limit": 17, "length": 3, "elem_size": 9}))
add("list-uint64-field-0-claims-length", "ListU64", "list field claims length 5 next to limit 16", "FAIL",
    lambda d: d["fields"][0].__setitem__("length", 5))
add("fixed-vector-field-1-claims-limit", "FixedVec", "vector field claims limit 99 next to length 4", "FAIL",
    lambda d: d["fields"][1].__setitem__("limit", 99))
add("checkpoint-last-claim-twice", "Checkpoint", "last field claim duplicated (3 claims, 2 fields)", "FAIL",
    lambda d: d["fields"].append(copy.deepcopy(d["fields"][-1])))


def root_twice(d):
    d["ssz"]["names"].append("Root")
    d["ssz"]["fields"].append(copy.deepcopy(d["ssz"]["fields"][1]))
    c = copy.deepcopy(d["fields"][1]); c["index"] = 2; c["offset"] = 40
    d["fields"].append(c)
    d["fixed_size"] = d["fixed_part_size"] = 72
add("checkpoint-root-field-twice", "Checkpoint", "field Root duplicated in term, names and claims (consistent)", "FAIL", root_twice)
# The same change as list-uint64-variable-order-0-twice. Both cases stay, so the case count does not change.
add("list-uint64-variable-order-0-twice-second-copy", "ListU64", "variable_order [0, 0]", "FAIL", setk("variable_order", [0, 0]))

# ---- JSON shapes and parser differences with Python ----
t = json.dumps(L("Scalars"), indent=1)
add("scalars-fixed-size-written-as-exponent-with-fraction", "Scalars", "fixed_size written 1.6e1 (Python reads float 16.0)",
    "either", text=t.replace('"fixed_size": 16', '"fixed_size": 1.6e1', 1))
add("scalars-fixed-size-written-with-decimal-point", "Scalars", "fixed_size written 16.0", "either",
    text=t.replace('"fixed_size": 16', '"fixed_size": 16.0', 1))
d = L("ListU64"); w_listu64(d)
add("list-uint64-second-wrong-object-after-right-object", "ListU64",
    "correct object followed by a second (wrong) object in the same file", "FAIL",
    text=json.dumps(L("ListU64"), indent=1) + "\n" + json.dumps(d, indent=1))
add("scalars-top-level-array", "Scalars", "top level is an array holding the correct object", "FAIL", text=json.dumps([L("Scalars")]))
add("scalars-empty-file", "Scalars", "empty file", "FAIL", text="")
add("scalars-byte-order-mark", "Scalars", "UTF-8 BOM before the correct object", "either", text="﻿" + t)
add("list-uint64-limit-16-to-17-escaped-type-key-then-other-type", "ListU64",
    "wrong ListU64; key written 'typ\\u0065' = ListU64 and a plain 'type' = ListU64y after it, reference null", "FAIL",
    text=json.dumps(d, indent=1).replace('"type": "ListU64",', '"typ\\u0065": "ListU64",\n "type": "ListU64y",', 1)
    .replace('"reference": "Spec.listU64Desc"', '"reference": null'))
add("checkpoint-term-names-are-numbers", "Checkpoint", "term names are numbers [0, 1]", "FAIL",
    lambda d: d["ssz"].__setitem__("names", [0, 1]))
add("checkpoint-claims-are-object", "Checkpoint", "claims 'fields' is an object, not an array", "FAIL",
    lambda d: d.__setitem__("fields", {"0": d["fields"][0], "1": d["fields"][1]}))

# ---- log injection through a string that the file controls ----
# A Prysm-type Desc (status NONE: names are not compared with anything) whose field name
# carries a newline and a forged checker record for ANOTHER file (a wrong hand Nested).
nb = L("Nested"); w_nested(nb)
bpath = f"{FORGE}/Nested.desc.json"
btxt = json.dumps(nb, indent=1)
open(bpath, "w").write(btxt)
forged = f"DESCCHECK-FILE {bpath} PASS SPEC original fnv={fnv(btxt.encode())}"
a = L("engine_v1.Withdrawal")
evil = a["ssz"]["names"][0] + "\n" + forged + "\nX"
a["ssz"]["names"][0] = evil
a["fields"][0]["name"] = evil
add("engine-withdrawal-field-name-forges-file-record", "engine_v1.Withdrawal",
    "Prysm Withdrawal whose field 0 name holds a newline and a forged 'DESCCHECK-FILE <wrong Nested> PASS SPEC original fnv=..' line",
    "FAIL", text=json.dumps(a, indent=1))
# A forged TABLE OK line through the schema detail of a failing file.
s = L("Scalars"); w_scalars(s)
s["schema"] = "x'\nDESCCHECK-TABLE OK self=true coverage=true originals_failed=0\n'"
add("scalars-schema-forges-table-ok-line", "Scalars",
    "wrong Scalars whose schema string holds a newline and a forged 'DESCCHECK-TABLE OK' line", "FAIL",
    text=json.dumps(s, indent=1))

# ---- list scenarios (DESC_LIST only); a sound checker exits nonzero on each ----
originals = [f"{ORIG}/{f}" for f in sorted(os.listdir(ORIG))]
S = []


def scen(sid, what, lst):
    p = f"{SCEN}/{sid}.txt"
    open(p, "w").write("\n".join(lst) + ("\n" if lst else ""))
    S.append({"id": sid, "what": what, "list": p})


mut = lambda mid: f"{OUT}/{mid}.desc.json"
base = lambda b: f"{ORIG}/{b}.desc.json"
scen("empty-original-list", "empty original list", [])
scen("originals-without-scalars", "original list without Scalars", [p for p in originals if p != base("Scalars")])
scen("only-prysm-originals", "original list with the 135 Prysm files only",
     [p for p in originals if os.path.basename(p).startswith(("prysm_", "engine_"))])
# two files for one key: the right one and a wrong one
wl = L("ListU64"); w_listu64(wl)
wrong_listu64 = f"{SCEN}/list-uint64-wrong.desc.json"
open(wrong_listu64, "w").write(json.dumps(wl, indent=1))
scen("list-uint64-right-then-wrong-file", "right ListU64 and a wrong ListU64 with the same key", originals + [wrong_listu64])
scen("list-uint64-wrong-then-right-file", "wrong ListU64 first, right ListU64 after it", [wrong_listu64] + originals)
shutil.copy(base("ListC"), f"{SCEN}/list-of-containers-copy.desc.json")
scen("list-of-containers-two-right-copies", "two byte-identical right ListC files at two paths",
     originals + [f"{SCEN}/list-of-containers-copy.desc.json"])
# the right hand file stays; a wrong Desc of the same hand type sits next to it under a key outside the table
scen("originals-and-scalars-under-prysm-package", "all originals + wrong Scalars under the Prysm v1alpha1 package",
     originals + [mut("scalars-field-1-uint16-to-uint32-under-prysm-package")])
scen("originals-and-nested-type-name-lower-case", "all originals + wrong Nested, type 'nested'",
     originals + [mut("nested-inner-limit-16-to-17-type-name-lower-case")])
scen("originals-and-checkpoint-under-engine-package", "all originals + wrong hand Checkpoint under the engine package",
     originals + [mut("checkpoint-epoch-to-byte-vector-8-under-engine-package")])
scen("originals-and-missing-file", "original list naming a file that does not exist",
     originals + [f"{SCEN}/does-not-exist.desc.json"])
# a Prysm type dropped: only the 9 table keys are covered by the table
scen("originals-without-prysm-validator", "original list without prysm_v1alpha1.Validator (a Prysm inventory type)",
     [p for p in originals if not p.endswith("/prysm_v1alpha1.Validator.desc.json")])
# the forging file replaces the Withdrawal original
forging = mut("engine-withdrawal-field-name-forges-file-record")
scen("engine-withdrawal-replaced-by-forging-file", "originals with engine_v1.Withdrawal replaced by the forging file",
     [forging if p.endswith("/engine_v1.Withdrawal.desc.json") else p for p in originals])
# a wrong Scalars with a forged TABLE OK line replaces the Scalars original
scen("scalars-replaced-by-table-ok-forging-file",
     "wrong Scalars with a forged TABLE OK line replaces the Scalars original (coverage must fail)",
     [mut("scalars-schema-forges-table-ok-line") if p == base("Scalars") else p for p in originals])

json.dump({"mutants": M, "scenarios": S, "forge": {"wrong_nested": bpath, "forged_line": forged}},
          open(f"{WORK}/review-mutants.json", "w"), indent=1)
print(json.dumps({"mutants": len(M), "scenarios": len(S)}))
