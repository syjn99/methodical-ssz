#!/usr/bin/env python3
"""Provisional scope classification of the Prysm types of the inventory.

Usage: type_scope.py <kraken-dir>     writes prysm/type-scope.json and prysm/type-scope.md

PROVISIONAL. Nothing here is proved or attempted. For every type of the inventory:
- patterns: the field shapes mapped to the existing hand proof patterns; shapes with no hand
  pattern are "new pattern"
- contracts: runtime calls of the three functions (go1.26.10/functions.json) checked against
  the contract registry of the hand case; fmt format shapes (verbs of the Go literal) against
  the three hand fmt contracts
- tool: Kraken runtime parser result of the three functions (go1.26.10/kparse.json)
- size band of the largest function against the largest hand function
- expected failure classes (all that apply) and the first one, in the order
  tool gap > missing contract > new pattern (automation) > none known.
"Generator defect" is a class too; no type gets it because no output-code defect is known.
Python 3 standard library only. Run with python3 -I.
"""
import json
import os
import re
import sys
from collections import Counter

HAND_PATTERN = {
    "uint64": "Scalars", "uint8": "Scalars", "uint16": "Scalars", "uint32": "Scalars", "bool": "Scalars",
    "bytesN": "Checkpoint.root", "vector[uint64]": "FixedVec.W", "list[uint64]": "ListU64",
    "bitlist": "BitL", "bitvector": "BitVec",
    "delegated container (fixed)": "AttestationData.source", "delegated container (variable)": "Nested.L",
}
NEW_PATTERN = {
    "vector[bytesN]": "vector of byte slices", "list[bytesN]": "list of fixed byte vectors",
    "list[byte]": "byte list (BitL without ValidateBitlist)", "vector[ValidatorIndex]": "vector of hand-written delegates",
    "list[list[byte]]": "list of byte lists (deep)",
}
COVERED_CALLS = {"makeslice", "growslice", "memmove", "newobject", "convT64", "ValidateBitlist", "ValidateBitvector",
                 "generated method", "panic*", "write barrier", "morestack_noctxt", "fmt"}
FMT_CONTRACT = {"": "FmtErrorfNilContract", "%w": "FmtErrorfWrapContract", "%d%w": "FmtErrorfDecimalWrapContract"}
ORDER = ["tool gap", "missing contract", "new pattern (automation)", "none known"]


def fmt_shapes(go_dir, typ):
    shapes = Counter()
    for f in os.listdir(go_dir):
        src = open(os.path.join(go_dir, f)).read().split("\n")
        i = 0
        while i < len(src):
            m = re.match(r"^func \(c \*(\w+)\) (UnmarshalSSZ|MarshalSSZTo)\(", src[i])
            if m and m.group(1) == typ:
                j = i + 1
                while src[j] != "}":
                    for lit in re.findall(r'fmt\.Errorf\(("(?:[^"\\]|\\.)*")', src[j]):
                        shapes["".join(re.findall(r"%[a-z]", lit))] += 1
                    j += 1
                i = j
            i += 1
    return shapes


def main():
    k = sys.argv[1]
    inv = json.load(open(f"{k}/prysm/inventory.json"))
    fn = json.load(open(f"{k}/prysm/go1.26.10/functions.json"))
    kp = {r["symbol"]: r for r in json.load(open(f"{k}/prysm/go1.26.10/kparse.json"))["functions"]}
    hand_max = max(sum(1 for l in open(os.path.join(f"{k}/link/out/norm", f)) if l.startswith("  "))
                   for f in os.listdir(f"{k}/link/out/norm") if f.startswith("target"))
    funcs = {(f["package"], f["type"], f["method"]): f for f in fn["functions"]}
    hand_types = {tuple(h["type"].rsplit(".", 1)) for h in inv["hand_written_delegates"]}
    go_dir = f"{k}/prysm/_generated/mainnet"
    var_of = {f"{t['package']}/{t['name']}": t["variable"] for t in inv["types"]}
    rows = []
    for t in inv["types"]:
        shapes = sorted({f["shape"] for f in t["fields"]})
        pats, new = set(), set()
        for s in shapes:
            if s in HAND_PATTERN:
                pats.add(HAND_PATTERN[s])
            elif s.startswith("delegated overlay"):
                new.add(f"hand-written delegate {s.split()[-1]}")
            elif s == "list[container]":
                # the hand ListC has variable elements; fixed-size elements are a new pattern
                for f in t["fields"]:
                    if f["shape"] == s:
                        ev = var_of.get(f["callee"])
                        if ev:
                            pats.add("ListC")
                        else:
                            new.add("list of fixed-size containers")
            elif s in NEW_PATTERN:
                new.add(NEW_PATTERN[s])
            else:
                new.add(f"unmapped shape {s}")
        fs = [funcs.get((t["package"], t["name"], m)) for m in ("MarshalSSZTo", "SizeSSZ", "UnmarshalSSZ")]
        calls = Counter()
        for f in fs:
            if f:
                calls.update(f["calls"])
        missing = []
        if calls.get("hand-written primitives method"):
            missing.append("hand-written primitives SSZ methods (no spec)")
        for c in calls:
            if c not in COVERED_CALLS and c != "hand-written primitives method":
                missing.append(f"runtime call {c}")
        sh = fmt_shapes(go_dir, t["name"]) if calls.get("fmt") else Counter()
        for s in sh:
            if s not in FMT_CONTRACT:
                missing.append(f"fmt shape '{s}'")
        parse = [kp.get(f["symbol"], {}).get("status", "not run") if f else "missing" for f in fs]
        maxins = max((f["instructions"] for f in fs if f), default=0)
        band = "within hand range" if maxins <= hand_max else ("up to 3x hand max" if maxins <= 3 * hand_max else "over 3x hand max")
        classes = []
        if any(p != "OK" for p in parse):
            classes.append("tool gap")
        if missing:
            classes.append("missing contract")
        if new:
            classes.append("new pattern (automation)")
        if not classes:
            classes.append("none known")
        rows.append({"type": t["name"], "package": t["package"], "fulu_reachable": t["in_B"], "scope": t["scope"],
                     "kind": t["kind"], "fields": t["field_count"], "shapes": shapes,
                     "hand_patterns": sorted(pats), "new_patterns": sorted(new), "missing_contracts": sorted(set(missing)),
                     "fmt_shapes": dict(sh), "calls": dict(calls), "kraken_parse_marshal_size_unmarshal": parse,
                     "max_instructions": maxins, "size_band": band, "expected_failure_classes": classes,
                     "first_class": min(classes, key=ORDER.index)})
    # a type is only as complete as its generated callees: worst class over the callee closure
    by = {f"{r['package']}/{r['type']}": r for r in rows}
    callees = {f"{t['package']}/{t['name']}": [c for c in t["callees"] if c in by] for t in inv["types"]}
    for key, r in by.items():
        seen, stack = set(), [key]
        while stack:
            x = stack.pop()
            if x in seen:
                continue
            seen.add(x)
            stack.extend(callees.get(x, []))
        r["callee_closure"] = len(seen) - 1
        r["first_class_transitive"] = min((by[x]["first_class"] for x in seen), key=ORDER.index)
    cnt = lambda key: dict(sorted(Counter(key(r) for r in rows).items()))
    rin = [r for r in rows if r["scope"] == "in"]
    split = {
        "types": len(rin),
        "calls_hand_written": sum(1 for r in rin if any(x.startswith("hand-written") for x in r["missing_contracts"])),
        "bitlist_via_contract": sum(1 for r in rin if "bitlist" in r["shapes"]),
        "list_container": sum(1 for r in rin if "list[container]" in r["shapes"]),
        "list_container_variable_elements_ListC": sum(1 for r in rin if "ListC" in r["hand_patterns"]),
        "list_container_fixed_elements_new": sum(1 for r in rin if "list of fixed-size containers" in r["new_patterns"]),
        "vector_of_container_forms": sum(1 for r in rin if any(s.startswith("vector[") and s not in ("vector[uint64]", "vector[bytesN]") for s in r["shapes"])),
        "vector_of_byte_slices": sum(1 for r in rin if "vector[bytesN]" in r["shapes"]),
        "three_functions_parse": sum(1 for r in rin if all(p == "OK" for p in r["kraken_parse_marshal_size_unmarshal"])),
        "some_function_does_not_parse": sum(1 for r in rin if any(p != "OK" for p in r["kraken_parse_marshal_size_unmarshal"])),
    }
    res = {"schema": "type-scope/1", "status": "PROVISIONAL (classification, no proof attempted)",
           "hand_max_instructions": hand_max, "types": len(rows),
           "counts": {"first_class": cnt(lambda r: r["first_class"]),
                      "first_class_transitive": cnt(lambda r: r["first_class_transitive"]),
                      "first_class_transitive_fulu_reachable": dict(sorted(Counter(r["first_class_transitive"] for r in rows if r["fulu_reachable"]).items())),
                      "first_class_scope_in_only": dict(sorted(Counter(r["first_class"] for r in rows if r["scope"] == "in").items())),
                      "has_class": {c: sum(1 for r in rows if c in r["expected_failure_classes"]) for c in ORDER},
                      "size_band": cnt(lambda r: r["size_band"]),
                      "missing_contract_kinds": dict(sorted(Counter(m for r in rows for m in r["missing_contracts"]).items())),
                      "new_pattern_kinds": dict(sorted(Counter(m for r in rows for m in r["new_patterns"]).items())),
                      "scope_in_split": split,
                      "fulu_reachable_first_class": dict(sorted(Counter(r["first_class"] for r in rows if r["fulu_reachable"]).items()))},
           "rows": rows}
    json.dump(res, open(f"{k}/prysm/type-scope.json", "w"), indent=1)
    L = ["# Type scope: provisional classification of the Prysm types", "",
         "**It is provisional.** We did not try proofs. This table does not say whether a proof is possible. `gen/type_scope.py` makes it from JSON.", "",
         "Failure reason classes (in the order in which they apply first): tool gap (`%riz`) > missing contract > new pattern (automation) > none known.",
         "\"Including callees\" is the first class that applies in the type and the closure of its generated callees. If the type alone is \"none known\" but a callee blocks it, the type is blocked.",
         "123 of the 135 Prysm types are protobuf structs. Their Go layout is different from the reduced types of the hand case (`ir/*.json` `go_fields`).",
         "Generator defect is one of the classes, but no output code defect is known, so no type has that class.",
         "\"None known\" does not count the models for each contract instance (esz, sz, format string and argument types) or the contract recheck against the Go 1.26.10 runtime source (`gen/frozen/ASSUMPTIONS.json` revision 2). Thus it does not mean that nothing blocks the type.",
         f"The largest function of the hand case has {hand_max} instructions. The size bands use it as the reference (we do not extrapolate time).", "",
         "## 1. Numbers", "", "| Item | Value |", "| --- | --- |"]
    for kk, v in res["counts"].items():
        L.append(f"| `{kk}` | {json.dumps(v, ensure_ascii=False)} |")
    L += ["", "## 2. Type table", "",
          "| Type | Fulu-reachable | Scope | First failure class | First class including callees | All classes | Hand patterns | New patterns | Missing contracts | Parser (MarshalSSZTo/SizeSSZ/UnmarshalSSZ) | Max instructions |",
          "| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |"]
    for r in sorted(rows, key=lambda r: (ORDER.index(r["first_class"]), r["type"])):
        L.append(f"| `{r['type']}` | {'yes' if r['fulu_reachable'] else ''} | {r['scope']} | {r['first_class']} | {r['first_class_transitive']} | "
                 f"{', '.join(r['expected_failure_classes'])} | {', '.join(r['hand_patterns']) or '-'} | "
                 f"{', '.join(r['new_patterns']) or '-'} | {', '.join(r['missing_contracts']) or '-'} | "
                 f"{'/'.join(r['kraken_parse_marshal_size_unmarshal'])} | {r['max_instructions']} |")
    open(f"{k}/prysm/type-scope.md", "w").write("\n".join(L) + "\n")
    print(json.dumps(res["counts"], indent=1, ensure_ascii=False))


if __name__ == "__main__":
    main()
