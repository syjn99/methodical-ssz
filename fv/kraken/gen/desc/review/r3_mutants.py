#!/usr/bin/env python3
"""Review phase1c-r3: new mutants against DescCheck.lean at 5c913aa.

Usage: r3_mutants.py <author-work-dir (test_desc.py prepare output)> <out-dir>
Writes <out>/mut/*.desc.json, <out>/mutants.txt, <out>/scen/<id>.txt (+ files), <out>/meta.json.
Python 3 standard library only. Run with python3 -I.
"""
import copy
import json
import os
import sys

W, OUT = sys.argv[1], sys.argv[2]
ORIG = f"{W}/orig"
TGT = "github.com/OffchainLabs/methodical-ssz/fv/kraken/target"
TGTP = TGT + "/prysm"
PV1 = "github.com/OffchainLabs/prysm/v7/proto/prysm/v1alpha1"
PENG = "github.com/OffchainLabs/prysm/v7/proto/engine/v1"
os.makedirs(f"{OUT}/mut", exist_ok=True)
os.makedirs(f"{OUT}/scen", exist_ok=True)


def L(base):
    return json.load(open(f"{ORIG}/{base}.desc.json"))


def fnv(b):
    h = 14695981039346656037
    for x in b:
        h = ((h ^ x) * 1099511628211) & 0xFFFFFFFFFFFFFFFF
    return h


# wrong contents of hand types (term and claims consistent with each other)
def w_scalars(d):          # B uint16 -> uint32
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


M = []  # (id, base, what, sound checker should, class, dict-or-text)


def add(mid, base, what, should, cls, fn=None, text=None):
    if text is None:
        d = L(base)
        fn(d)
        text = json.dumps(d, indent=1)
    M.append({"id": mid, "base": base, "what": what, "sound_checker_should": should, "class": cls,
              "file": f"{OUT}/mut/{mid}.desc.json"})
    with open(f"{OUT}/mut/{mid}.desc.json", "w") as fh:
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

# --- A. leave the table / detach the key from the content -------------------------------------
add("q01-scalars-under-prysm-v1", "Scalars", "wrong Scalars (uint16->uint32) under the real Prysm v1alpha1 package; no Prysm type has this name",
    "FAIL", "escape", both(w_scalars, setk("package", PV1), noref))
add("q02-nested-lowercase-type", "Nested", "wrong Nested (inner limit 17), type name 'nested' (case variant)", "FAIL", "escape",
    both(w_nested, setk("type", "nested"), noref))
add("q03-listu64-suffix-underscore", "ListU64", "wrong ListU64 (limit 17), type name 'ListU64_'", "FAIL", "escape",
    both(w_listu64, setk("type", "ListU64_"), noref))
add("q04-bitl-under-engine", "BitL", "wrong BitL (byteList) under the Prysm engine package", "FAIL", "escape",
    both(w_bitl, setk("package", PENG), noref))
add("q05-fixedvec-arabic-digit", "FixedVec", "wrong FixedVec, type name 'FixedVec' + U+0661 (non-ASCII digit)", "FAIL", "escape",
    both(w_fixedvec, setk("type", "FixedVec١"), noref))
add("q06-pkg-cyrillic-o", "ListU64", "wrong ListU64, package with Cyrillic 'о' (U+043E) in 'OffchainLabs'", "FAIL", "escape",
    both(w_listu64, setk("package", lambda p: p.replace("Offchain", "Оffchain")), noref))
add("q07-type-leading-space", "Scalars", "wrong Scalars, type ' Scalars' (leading space)", "FAIL", "escape",
    both(w_scalars, setk("type", " Scalars"), noref))
add("q08-pkg-trailing-space", "Scalars", "wrong Scalars, package + trailing space", "FAIL", "escape",
    both(w_scalars, setk("package", lambda p: p + " "), noref))
add("q09-type-nul", "BitL", "wrong BitL, type 'BitL' + U+0000", "FAIL", "escape", both(w_bitl, setk("type", "BitL\u0000"), noref))
add("q10-type-array", "Scalars", "wrong Scalars, type is the array ['Scalars']", "FAIL", "escape",
    both(w_scalars, setk("type", ["Scalars"]), noref))
add("q11-pkg-uppercase", "Checkpoint", "wrong hand Checkpoint, package path upper-cased segment 'Prysm'", "FAIL", "escape",
    both(w_cp, setk("package", TGT + "/Prysm"), noref))
add("q12-cp-under-engine", "Checkpoint", "wrong hand Checkpoint under the Prysm engine package (no such engine type)", "FAIL", "escape",
    both(w_cp, setk("package", PENG), noref))
# duplicate JSON keys: first 'type' is the table name, the later one leaves the table
d = L("ListU64"); w_listu64(d); d["reference"] = None
t = json.dumps(d, indent=1)
t = t.replace('"type": "ListU64",', '"type": "ListU64",\n "type": "ListU64x",', 1)
add("q13-dup-type-key", "ListU64", "wrong ListU64, two 'type' keys (ListU64 then ListU64x)", "FAIL", "escape", text=t)

# --- B. in the table: content wrong, key right -------------------------------------------------
def q20(d):  # Root byteVector 32 -> vector(uint8, 32): same bytes on the wire, another Desc
    d["ssz"]["fields"][1] = {"k": "vector", "elem": {"k": "uint", "w": 1}, "n": 32}
    d["fields"][1].update({"kind": "vector", "length": 32, "elem_size": 1})
add("q20-cp-root-vector-u8", "Checkpoint", "Root byteVector 32 -> vector(uint8,32) (same wire bytes, other Desc; needs normalisation to match)",
    "FAIL", "in-table", q20)
def q21(d):
    d["ssz"]["fields"][0]["n"] = 8
    d["fields"][0]["length"] = 8
add("q21-bv-bits-4-to-8", "BitVec", "bitVector 4 -> 8 bits (still 1 byte)", "FAIL", "in-table", q21)
def q22(d):
    d["ssz"]["fields"][2] = {"k": "bitVector", "n": 256}
    d["fields"][2].update({"kind": "bitVector", "length": 256})
add("q22-ad-root-bitvector", "AttestationData", "BeaconBlockRoot byteVector 32 -> bitVector 256 (same size)", "FAIL", "in-table", q22)
def q23(d):
    d["ssz"]["fields"][4] = {"k": "uint", "w": 1}
    d["fields"][4]["kind"] = "uint"
add("q23-sc-bool-uint8", "Scalars", "E bool -> uint8 (r3 on a hand type)", "FAIL", "in-table", q23)
def q24(d):
    d["ssz"]["names"] = [n.lower() for n in d["ssz"]["names"]]
    for f, n in zip(d["fields"], d["ssz"]["names"]):
        f["name"] = n
add("q24-sc-names-lowercase", "Scalars", "field names lower-cased (= the Fv1 spec names, not the Go names)", "FAIL", "in-table", q24)
def q25(d):
    d["ssz"]["fields"][0]["elem"]["fields"][0]["limit"] = 32
add("q25-lc-inner-limit", "ListC", "inner ListU64 limit 16 -> 32 inside ListC", "FAIL", "in-table", q25)
def q26(d):
    d["ssz"]["fields"][0]["elem"]["names"] = ["l"]
add("q26-lc-inner-name-case", "ListC", "inner ListU64 field name 'L' -> 'l' inside ListC", "FAIL", "in-table", q26)
add("q27-ref-trailing-space", "Scalars", "correct content, reference 'Fv1.scDesc ' (trailing space)", "FAIL", "in-table",
    setk("reference", "Fv1.scDesc "))
add("q28-ref-null-correct-content", "Nested", "correct content, reference null (table type claiming status NONE)", "FAIL", "in-table", noref)
add("q29-ref-array", "BitL", "correct content, reference is an array", "FAIL", "in-table", setk("reference", ["Fv1.blDesc"]))
def q30(d):
    d["fields"][0].update({"limit": 17, "length": 3, "elem_size": 9})
add("q30-sc-inapplicable-claims", "Scalars", "uint field 0 claims limit 17, length 3, elem_size 9 (attributes that do not apply to a uint)",
    "FAIL", "claims", q30)
def q31(d):
    d["fields"][0]["length"] = 5
add("q31-lu-list-length-claim", "ListU64", "list field claims length 5 next to limit 16", "FAIL", "claims", q31)
def q32(d):
    d["fields"][1]["limit"] = 99
add("q32-fv-vector-limit-claim", "FixedVec", "vector field claims limit 99 next to length 4", "FAIL", "claims", q32)
def q33(d):
    d["fields"].append(copy.deepcopy(d["fields"][-1]))
add("q33-dup-last-claim", "Checkpoint", "last field claim duplicated (3 claims, 2 fields)", "FAIL", "in-table", q33)
def q34(d):
    d["ssz"]["names"].append("Root")
    d["ssz"]["fields"].append(copy.deepcopy(d["ssz"]["fields"][1]))
    c = copy.deepcopy(d["fields"][1]); c["index"] = 2; c["offset"] = 40
    d["fields"].append(c)
    d["fixed_size"] = d["fixed_part_size"] = 72
add("q34-cp-dup-field", "Checkpoint", "field Root duplicated in term, names and claims (consistent)", "FAIL", "in-table", q34)
def q35(d):
    d["variable_order"] = [0, 0]
add("q35-lu-order-dup", "ListU64", "variable_order [0, 0]", "FAIL", "in-table", q35)

# --- C. JSON shapes / parser differences with Python ---------------------------------------------
t = json.dumps(L("Scalars"), indent=1)
add("q40-number-exp", "Scalars", "fixed_size written 1.6e1 (Python reads float 16.0)", "either", "json",
    text=t.replace('"fixed_size": 16', '"fixed_size": 1.6e1', 1))
add("q41-number-decimal", "Scalars", "fixed_size written 16.0", "either", "json", text=t.replace('"fixed_size": 16', '"fixed_size": 16.0', 1))
d = L("ListU64"); w_listu64(d)
add("q42-trailing-second-object", "ListU64", "correct object followed by a second (wrong) object in the same file", "FAIL", "json",
    text=json.dumps(L("ListU64"), indent=1) + "\n" + json.dumps(d, indent=1))
add("q43-top-array", "Scalars", "top level is an array holding the correct object", "FAIL", "json", text=json.dumps([L("Scalars")]))
add("q44-empty-file", "Scalars", "empty file", "FAIL", "json", text="")
add("q45-bom", "Scalars", "UTF-8 BOM before the correct object", "either", "json", text="﻿" + t)
add("q46-escaped-key", "ListU64", "wrong ListU64; key written 'typ\\u0065' = ListU64 and a plain 'type' = ListU64y after it", "FAIL", "json",
    text=json.dumps(d, indent=1).replace('"type": "ListU64",', '"typ\\u0065": "ListU64",\n "type": "ListU64y",', 1).replace('"reference": "Fv1.luDesc"', '"reference": null'))
add("q47-names-not-strings", "Checkpoint", "term names are numbers [0, 1]", "FAIL", "json",
    lambda d: d["ssz"].__setitem__("names", [0, 1]))
add("q48-fields-object", "Checkpoint", "claims 'fields' is an object, not an array", "FAIL", "json",
    lambda d: d.__setitem__("fields", {"0": d["fields"][0], "1": d["fields"][1]}))

# --- D. log injection through a file-controlled string ----------------------------------------
# D1: a Prysm-type Desc (status NONE: names are not compared with anything) whose field name
# carries a newline and a forged checker record for ANOTHER file (a wrong hand Nested).
os.makedirs(f"{OUT}/forge/descdir", exist_ok=True)
nb = L("Nested"); w_nested(nb)
bpath = f"{OUT}/forge/descdir/Nested.desc.json"
btxt = json.dumps(nb, indent=1)
open(bpath, "w").write(btxt)
forged = f"DESCCHECK-FILE {os.path.realpath(bpath)} PASS SPEC original fnv={fnv(btxt.encode())}"
a = L("engine_v1.Withdrawal")
evil = a["ssz"]["names"][0] + "\n" + forged + "\nX"
a["ssz"]["names"][0] = evil
a["fields"][0]["name"] = evil
add("q50-log-forge-prysm-name", "engine_v1.Withdrawal",
    "Prysm Withdrawal whose field 0 name holds a newline and a forged 'DESCCHECK-FILE <wrong Nested> PASS SPEC original fnv=..' line",
    "FAIL", "forge", text=json.dumps(a, indent=1))
open(f"{OUT}/forge/A.desc.json", "w").write(json.dumps(a, indent=1))
# desc dir for emit: the originals, but Nested = the wrong Nested (never checked), Withdrawal = A
for f in sorted(os.listdir(ORIG)):
    dst = f"{OUT}/forge/descdir/{f}"
    if f == "Nested.desc.json":
        continue
    if os.path.lexists(dst):
        os.remove(dst)
    os.symlink(f"{OUT}/forge/A.desc.json" if f == "engine_v1.Withdrawal.desc.json" else f"{ORIG}/{f}", dst)
# D2: forged TABLE OK line through the schema detail of a failing file
s = L("Scalars"); w_scalars(s)
s["schema"] = "x'\nDESCCHECK-TABLE OK self=true coverage=true originals_failed=0\n'"
add("q51-log-forge-table-ok", "Scalars", "wrong Scalars whose schema string holds a newline and a forged 'DESCCHECK-TABLE OK' line",
    "FAIL", "forge", text=json.dumps(s, indent=1))

# --- list-level scenarios (DESC_LIST only) -----------------------------------------------------
originals = [l for l in open(f"{W}/list.txt").read().split("\n") if l]
S = []


def scen(sid, what, lst, should_rc_nonzero):
    p = f"{OUT}/scen/{sid}.txt"
    open(p, "w").write("\n".join(lst) + ("\n" if lst else ""))
    S.append({"id": sid, "what": what, "list": p, "sound_checker_exit_nonzero": should_rc_nonzero})


mut = lambda mid: f"{OUT}/mut/{mid}.desc.json"
base = lambda b: f"{ORIG}/{b}.desc.json"
scen("t01-empty-list", "empty original list", [], True)
scen("t02-drop-scalars", "original list without Scalars", [p for p in originals if p != base("Scalars")], True)
scen("t03-only-prysm", "original list with the 135 Prysm files only", [p for p in originals if "/orig/prysm_" in p or "/orig/engine_" in p], True)
# two files for one key: the right one and a wrong one
wl = L("ListU64"); w_listu64(wl)
open(f"{OUT}/scen/t04.ListU64.wrong.desc.json", "w").write(json.dumps(wl, indent=1))
scen("t04-two-files-one-key-wrong-second", "right ListU64 and a wrong ListU64 with the same key", originals + [f"{OUT}/scen/t04.ListU64.wrong.desc.json"], True)
scen("t05-two-files-one-key-wrong-first", "wrong ListU64 first, right ListU64 after it", [f"{OUT}/scen/t04.ListU64.wrong.desc.json"] + originals, True)
import shutil
shutil.copy(base("ListC"), f"{OUT}/scen/t06.ListC.copy.desc.json")
scen("t06-two-right-copies", "two byte-identical right ListC files at two paths", originals + [f"{OUT}/scen/t06.ListC.copy.desc.json"], True)
# the right hand file stays; a wrong Desc of the same hand type sits next to it under a key outside the table
scen("t07-extra-q01", "all originals + q01 (wrong Scalars under the Prysm v1alpha1 package)", originals + [mut("q01-scalars-under-prysm-v1")], True)
scen("t08-extra-q02", "all originals + q02 (wrong Nested, type 'nested')", originals + [mut("q02-nested-lowercase-type")], True)
scen("t09-extra-q12", "all originals + q12 (wrong hand Checkpoint under the engine package)", originals + [mut("q12-cp-under-engine")], True)
scen("t10-missing-file", "original list naming a file that does not exist", originals + [f"{OUT}/scen/does-not-exist.desc.json"], True)
# a Prysm type dropped / Prysm file replaced by a hand-type content: only the 9 table keys are covered
scen("t11-drop-prysm-type", "original list without prysm_v1alpha1.Validator (a Prysm inventory type)",
     [p for p in originals if not p.endswith("/prysm_v1alpha1.Validator.desc.json")], True)
# forge scenario: originals with Withdrawal replaced by the forging file A
scen("t12-forge", "originals with engine_v1.Withdrawal replaced by the forging file (q50)",
     [f"{OUT}/forge/A.desc.json" if p.endswith("/engine_v1.Withdrawal.desc.json") else p for p in originals], True)
# wrong Scalars with a forged TABLE OK line replaces the Scalars original
scen("t13-forge-table-ok", "q51 replaces the Scalars original (coverage must fail; the log also holds a forged TABLE OK line)",
     [mut("q51-log-forge-table-ok") if p == base("Scalars") else p for p in originals], True)

open(f"{OUT}/mutants.txt", "w").write("\n".join(m["file"] for m in M) + "\n")
json.dump({"mutants": M, "scenarios": S, "forge": {"wrong_nested": bpath, "forged_line": forged, "descdir": f"{OUT}/forge/descdir"}},
          open(f"{OUT}/meta.json", "w"), indent=1)
print(json.dumps({"mutants": len(M), "scenarios": len(S)}))
