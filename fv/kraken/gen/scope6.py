#!/usr/bin/env python3
"""P6: provisional scope classification of the Prysm inventory for X5.

Usage: scope6.py <kraken-dir>     writes prysm/SCOPE-P6.json and prysm/SCOPE-P6.md

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
FMT_CONTRACT = {"": "FmtErrorfNilC", "%w": "FmtErrorfWC", "%d%w": "FmtErrorfDWC"}
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
        rows.append({"type": t["name"], "package": t["package"], "in_B": t["in_B"], "p1_scope": t["scope"],
                     "kind": t["kind"], "fields": t["field_count"], "shapes": shapes,
                     "hand_patterns": sorted(pats), "new_patterns": sorted(new), "missing_contracts": sorted(set(missing)),
                     "fmt_shapes": dict(sh), "calls": dict(calls), "kraken_parse_M_S_U": parse,
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
    rin = [r for r in rows if r["p1_scope"] == "in"]
    split = {
        "types": len(rin),
        "calls_hand_written": sum(1 for r in rin if any(x.startswith("hand-written") for x in r["missing_contracts"])),
        "bitlist_via_contract": sum(1 for r in rin if "bitlist" in r["shapes"]),
        "list_container": sum(1 for r in rin if "list[container]" in r["shapes"]),
        "list_container_variable_elements_ListC": sum(1 for r in rin if "ListC" in r["hand_patterns"]),
        "list_container_fixed_elements_new": sum(1 for r in rin if "list of fixed-size containers" in r["new_patterns"]),
        "vector_of_container_forms": sum(1 for r in rin if any(s.startswith("vector[") and s not in ("vector[uint64]", "vector[bytesN]") for s in r["shapes"])),
        "vector_of_byte_slices": sum(1 for r in rin if "vector[bytesN]" in r["shapes"]),
        "three_functions_parse": sum(1 for r in rin if all(p == "OK" for p in r["kraken_parse_M_S_U"])),
        "some_function_does_not_parse": sum(1 for r in rin if any(p != "OK" for p in r["kraken_parse_M_S_U"])),
    }
    res = {"schema": "fvphase1c.scope-p6/1", "status": "PROVISIONAL (classification, no proof attempted)",
           "hand_max_instructions": hand_max, "types": len(rows),
           "counts": {"first_class": cnt(lambda r: r["first_class"]),
                      "first_class_transitive": cnt(lambda r: r["first_class_transitive"]),
                      "first_class_transitive_in_B": dict(sorted(Counter(r["first_class_transitive"] for r in rows if r["in_B"]).items())),
                      "first_class_p1_in_only": dict(sorted(Counter(r["first_class"] for r in rows if r["p1_scope"] == "in").items())),
                      "has_class": {c: sum(1 for r in rows if c in r["expected_failure_classes"]) for c in ORDER},
                      "size_band": cnt(lambda r: r["size_band"]),
                      "missing_contract_kinds": dict(sorted(Counter(m for r in rows for m in r["missing_contracts"]).items())),
                      "new_pattern_kinds": dict(sorted(Counter(m for r in rows for m in r["new_patterns"]).items())),
                      "p1_in_split": split,
                      "in_B_first_class": dict(sorted(Counter(r["first_class"] for r in rows if r["in_B"]).items()))},
           "rows": rows}
    json.dump(res, open(f"{k}/prysm/SCOPE-P6.json", "w"), indent=1)
    L = ["# SCOPE-P6: X5를 위한 잠정 분류 (phase1c P6)", "",
         "**잠정이다.** 증명을 시도하지 않았다. 이 표는 증명 가능성을 말하지 않는다. `gen/scope6.py`가 JSON에서 만든다.", "",
         "실패 이유 종류(먼저 걸리는 순서): 도구 빈틈(`%riz`) > 계약 부재 > 새 패턴(자동화) > 알려진 것 없음.",
         "\"피호출 포함\"은 타입과 그 생성 피호출자 폐포 중 가장 먼저 걸리는 종류다. 타입 혼자 \"알려진 것 없음\"이어도 피호출자가 막으면 막힌다.",
         "Prysm 타입 135개 중 123개는 protobuf 구조체다. 손 사례의 축약 타입과 Go 배치가 다르다(`ir/*.json` `go_fields`).",
         "생성기 결함은 종류에 있지만 출력 코드 결함이 알려지지 않아 해당 타입이 없다.",
         f"손 사례의 가장 큰 함수는 명령어 {hand_max}개다. 크기 띠는 그 기준이다(시간을 외삽하지 않는다).", "",
         "## 1. 수치", "", "| 항목 | 값 |", "| --- | --- |"]
    for kk, v in res["counts"].items():
        L.append(f"| `{kk}` | {json.dumps(v, ensure_ascii=False)} |")
    L += ["", "## 2. 타입 표", "",
          "| 타입 | B | P1 범위 | 첫 실패 종류 | 피호출 포함 첫 종류 | 모든 종류 | 손 패턴 | 새 패턴 | 없는 계약 | 파서 M/S/U | 최대 명령어 |",
          "| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |"]
    for r in sorted(rows, key=lambda r: (ORDER.index(r["first_class"]), r["type"])):
        L.append(f"| `{r['type']}` | {'B' if r['in_B'] else ''} | {r['p1_scope']} | {r['first_class']} | {r['first_class_transitive']} | "
                 f"{', '.join(r['expected_failure_classes'])} | {', '.join(r['hand_patterns']) or '-'} | "
                 f"{', '.join(r['new_patterns']) or '-'} | {', '.join(r['missing_contracts']) or '-'} | "
                 f"{'/'.join(r['kraken_parse_M_S_U'])} | {r['max_instructions']} |")
    open(f"{k}/prysm/SCOPE-P6.md", "w").write("\n".join(L) + "\n")
    print(json.dumps(res["counts"], indent=1, ensure_ascii=False))


if __name__ == "__main__":
    main()
