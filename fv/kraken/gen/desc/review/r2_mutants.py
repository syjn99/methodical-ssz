#!/usr/bin/env python3
"""phase1c-r2 reviewer mutants for DescCheck.lean (114fdfc). Usage: r2_mutants.py <work-dir>
Reads <work>/orig, writes <work>/n/*.desc.json, <work>/nmut.json, <work>/list-r2.txt
(originals + committed controls + r1 mutants (if <work>/rmut.json exists) + these)."""
import copy
import json
import os
import sys

work = sys.argv[1]
orig = work + "/orig"
out = work + "/n"
os.makedirs(out, exist_ok=True)
M = []
PRYSM_PKG = "github.com/OffchainLabs/prysm/v7/proto/prysm/v1alpha1"


def L(name):
    return json.load(open(f"{orig}/{name}.desc.json"))


def add(i, base, what, fn, want, cls):
    d = L(base)
    r = fn(d)
    p = f"{out}/{i}.desc.json"
    with open(p, "w") as fh:
        if isinstance(r, str):
            fh.write(r)          # raw text mutant
        else:
            json.dump(d if r is None else r, fh, indent=1)
    M.append({"id": i, "base": base, "what": what, "file": p, "sound_checker_should": want, "class": cls})


# ---- A. escape the (package, type) table with a wrong hand-type Desc ----
def limit17(d):
    d["ssz"]["fields"][0]["limit"] = 17
    d["fields"][0]["limit"] = 17


def a1(d):
    limit17(d); d["package"] += "/"; d["reference"] = None
add("n01-esc-pkg-slash", "ListU64", "limit 16->17 (term+claim), package gets a trailing '/', reference null", a1, "FAIL", "escape")


def a2(d):
    d["ssz"]["fields"][0]["k"] = "byteList"; d["fields"][0]["kind"] = "byteList"; del d["type"]; d["reference"] = None
add("n02-esc-type-missing", "BitL", "bitList->byteList (term+claim), `type` key deleted, reference null", a2, "FAIL", "escape")


def uintw(d):
    d["ssz"]["fields"][1]["w"] = 4; d["fields"][1]["width"] = 4; d["fields"][2]["offset"] = 5
    d["fields"][3]["offset"] = 9; d["fields"][4]["offset"] = 17; d["fixed_size"] = 18; d["fixed_part_size"] = 18


def a3(d):
    uintw(d); del d["package"]; d["reference"] = None
add("n03-esc-pkg-missing", "Scalars", "uint16->uint32 with all claims following, `package` key deleted, reference null", a3, "FAIL", "escape")


def a4(d):
    d["ssz"]["fields"][0] = {"k": "byteVector", "n": 8}; d["fields"][0]["kind"] = "byteVector"; d["fields"][0]["length"] = 8
    d["package"] = PRYSM_PKG; d["reference"] = None
add("n04-esc-pkg-prysm", "Checkpoint", "hand Checkpoint, Epoch uint64->byteVector 8 (claims follow), package = the real Prysm package, reference null", a4, "FAIL", "escape")


def a5(d):
    d["ssz"]["fields"][1]["n"] = 5; d["fields"][1]["length"] = 5; d["fields"][1]["width"] = 40
    d["fixed_size"] = 72; d["fixed_part_size"] = 72; d["type"] = "FixedVec​"; d["reference"] = None
add("n05-esc-type-zwsp", "FixedVec", "vector length 4->5 (claims follow), type name gets U+200B, reference null", a5, "FAIL", "escape")

# ---- B. reference variants ----
add("n06-ref-extra-on-prysm", "prysm_v1alpha1.Checkpoint", "unchanged Prysm Checkpoint, reference set to Fv1.cpDesc (type not in table)",
    lambda d: d.__setitem__("reference", "Fv1.cpDesc"), "FAIL", "reference")


def b2(d):
    limit17(d); d["reference"] = ["Fv1.luDesc"]
add("n07-ref-nonstring", "ListU64", "limit 16->17, reference is a JSON array", b2, "FAIL", "reference")


def b3(d):
    c = L("ListC"); c["type"] = "ListU64"; c["package"] = d["package"]; c["reference"] = "Fv1.lcDesc"
    return c
add("n08-wrong-body-right-key", "ListU64", "whole body of ListC under type ListU64, reference Fv1.lcDesc", b3, "FAIL", "reference")


def b4(d):
    uintw(d); d["reference"] = None; d["status"] = "NONE"; d["spec"] = "NONE"; d["ref_status"] = "NONE"
add("n09-claims-status-none", "Scalars", "uint16->uint32 (claims follow), reference null, file carries status/spec/ref_status = NONE", b4, "FAIL", "reference")


def b5(d):
    limit17(d); d["reference"] = "Fv1.luDesc "
add("n10-ref-trailing-space", "ListU64", "limit 16->17, reference 'Fv1.luDesc ' (trailing space)", b5, "FAIL", "reference")

# ---- C. reordered / duplicated fields with consistent names (hand types, same shape) ----
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
add("n11-ad-swap-slot-index", "AttestationData", "fields 0 (Slot) and 1 (CommitteeIndex) swapped in term, names and claims; shapes are equal", swap(0, 1), "FAIL", "reorder")
add("n12-ad-swap-source-target", "AttestationData", "fields 3 (Source) and 4 (Target) swapped in term, names and claims; shapes are equal", swap(3, 4), "FAIL", "reorder")


def c3(d):
    d["ssz"]["names"] = ["Epoch", "Epoch"]; d["fields"][1]["name"] = "Epoch"
add("n13-dup-field-name", "Checkpoint", "both fields named Epoch in term and claims", c3, "FAIL", "reorder")


def c4(d):
    d["ssz"]["names"] = ["Root", "Epoch"]; d["fields"][0]["name"] = "Root"; d["fields"][1]["name"] = "Epoch"
add("n14-cp-names-crossed", "Checkpoint", "names crossed: uint64 field named Root, bytes32 field named Epoch (term and claims agree)", c4, "FAIL", "reorder")

# ---- D. equal only after a normalisation the checker should not do ----
def d1(d):
    d["ssz"]["fields"][0] = {"k": "vector", "elem": {"k": "uint", "w": 1}, "n": 32}
    d["fields"][0].update(kind="vector", elem_size=1)
add("n15-norm-bytevec-as-vector", "FixedVec", "byteVector 32 -> vector(uint8) 32 (same bytes, different Desc), claims follow", d1, "FAIL", "normalise")


def d2(d):
    d["ssz"]["fields"][0] = {"k": "uint", "w": 1}; d["fields"][0]["kind"] = "uint"; d["fields"][0].pop("length")
add("n16-norm-bitvec4-as-uint8", "BitVec", "bitVector 4 -> uint8 (same width), claims follow", d2, "FAIL", "normalise")


def d3(d):
    d["ssz"]["fields"][2]["fields"][0]["limit"] = 17
add("n17-nested-inner-limit", "Nested", "inner ListU64 limit 16->17 inside Nested (no claim covers it)", d3, "FAIL", "normalise")


def d4(d):
    d["ssz"]["names"].append("Z"); d["ssz"]["fields"].append({"k": "bool"})
    d["fields"].append({"name": "Z", "index": 5, "offset": 16, "width": 1, "variable": False, "kind": "bool"})
    d["fixed_size"] = 17; d["fixed_part_size"] = 17
add("n18-extra-trailing-field", "Scalars", "one extra bool field at the end, all claims consistent", d4, "FAIL", "normalise")


def d5(d):
    return json.dumps(d, indent=1).replace('"limit": 16', '"limit": 16.0')
add("n19-num-float", "ListU64", "limit written 16.0 in term and claim (value equal; informational)", d5, "either", "json")


def dupkeys(first_wrong):
    def f(d):
        good = copy.deepcopy(d)
        bad = copy.deepcopy(d)
        limit17(bad)
        a, b = (bad, good) if first_wrong else (good, bad)
        ja, jb = json.dumps(a, indent=1), json.dumps(b, indent=1)
        return ja.rstrip()[:-1].rstrip() + ",\n" + jb.lstrip()[1:]
    return f
add("n20-dupkey-first-wrong", "ListU64", "every key twice: first copy limit 17, second copy correct (Python json reads the second)", dupkeys(True), "either (must agree with last-wins)", "json")
add("n21-dupkey-last-wrong", "ListU64", "every key twice: first copy correct, second copy limit 17 (Python json reads the second = wrong)", dupkeys(False), "FAIL", "json")

# ---- E. malformed JSON shapes ----
add("n22-top-array", "Checkpoint", "top level is a JSON array holding the Desc", lambda d: [copy.deepcopy(d)], "FAIL", "malformed")
add("n23-ssz-string", "ListU64", "ssz is the string 'Fv1.luDesc'", lambda d: d.__setitem__("ssz", "Fv1.luDesc"), "FAIL", "malformed")


def e3(d):
    for f in d["fields"]:
        f.pop("name"); f.pop("index")
add("n24-claims-no-name-index", "Checkpoint", "claims without name and index keys", e3, "FAIL", "malformed")
add("n25-index-string", "Checkpoint", "index of field 1 is the string '1'", lambda d: d["fields"][1].__setitem__("index", "1"), "FAIL", "malformed")
add("n26-claims-short", "Checkpoint", "claims truncated to one field", lambda d: d.__setitem__("fields", d["fields"][:1]), "FAIL", "malformed")
add("n27-empty-file", "Checkpoint", "empty file", lambda d: "", "FAIL", "malformed")
add("n28-names-short", "Checkpoint", "term names has 1 entry for 2 fields", lambda d: d["ssz"].__setitem__("names", ["Epoch"]), "FAIL", "malformed")
add("n29-negative-width", "Checkpoint", "width of field 0 is -8", lambda d: d["fields"][0].__setitem__("width", -8), "FAIL", "malformed")


def e9(d):
    d["ssz"]["fields"][0]["limit"] = 17   # claim keeps 16: term-only change on a hand type
add("n30-term-only-limit", "ListU64", "term limit 17, claim limit 16, reference kept", e9, "FAIL", "malformed")


def e10(d):
    d["ssz"]["fields"][0]["w"] = "8"
add("n31-term-number-string", "Checkpoint", "term uint width is the string '8'", e10, "FAIL", "malformed")


def e11(d):
    d["ssz"]["fields"][0]["extra"] = {"k": "uint", "w": 4}; d["bogus_claim"] = "x"; d["fields"][0]["callee"] = "a.B"
add("n32-unknown-keys", "Checkpoint", "unknown keys in term, top level and a claim (informational: ignored or rejected?)", e11, "either", "malformed")

json.dump(M, open(work + "/nmut.json", "w"), indent=1)
lst = [x for x in open(work + "/list.txt").read().split("\n") if x]
if os.path.exists(work + "/rmut.json"):
    lst += [m["file"] for m in json.load(open(work + "/rmut.json"))]
open(work + "/list-r2.txt", "w").write("\n".join(lst + [m["file"] for m in M]) + "\n")
print(len(M), len(lst) + len(M))
