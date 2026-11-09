#!/usr/bin/env python3
"""Regenerate the REPORT.md section 2 gate table from resolved Lean declarations (P5).

Usage: table.py <complete-log> <THEOREMS.json> <negative/RESULT> <REPORT.md> <out.json> <out.md>

Inputs:
  complete-log  `COMPLETE {json}` lines of gen/complete/Complete.lean (resolved names)
  THEOREMS.json the frozen obligation list (roles: which theorem is which obligation)
  RESULT        negative suite output (case -> designated theorem name; resolved by Complete)
  REPORT.md     only to read the hand table for the comparison (never written)
Rules per column (all from the data above, no Lean source text):
  accept        an accept main resolves and has a witness; `ethlib_links` names the users whose
                type mentions EthLib serialize/deserialize; reject_spec theorems are listed
  rejects       closed = decoder reject obligations whose mapped theorem resolves and has a
                witness; total = decoder error return sites of the Go source (frozen list)
  witnesses     witness declarations (resolved: proof uses the main, type has no Host binder)
  contracts     registry contracts in the hypotheses of the type's mains, plus the contracts of
                function-spec holders (contracts_via)
  negative      RESULT cases (controls with an identity mutation excluded) whose designated theorem is a main of the type, reaches one
                (dependent_mains), or is a callee spec whose contract the type's mains assume
  compose       composition theorem resolves; its witnesses
  post          per main: dmem_eq -> memory identity; frame and no True -> frame exact;
                frame and True -> frame + True; no frame -> no frame
Cells that are free text in REPORT (witness detail, Go value) are not compared.
Python 3 standard library only. Run with python3 -I.
"""
import json
import re
import sys

ROWS = [("Scalars", "Scalars"), ("FixedVec", "FixedVec"), ("ListU64", "ListU64"), ("BitVec", "BitVec"),
        ("BitL", "BitL"), ("Nested", "Nested"), ("List[container]", "ListC"),
        ("Prysm 축약 Checkpoint", "Checkpoint"), ("Prysm 축약 AttestationData", "AttestationData")]
KEYWORD = {"MakesliceC": "makeslice", "MemmoveC": "memmove", "GrowsliceC": "growslice", "NewobjectC": "newobject",
           "ConvT64C": "convT64", "FmtErrorfNilC": "fmt", "FmtErrorfWC": "fmt", "FmtErrorfDWC": "fmt",
           "ValidateBitlistC": "ValidateBitlist", "ValidateBitlistErrC": "ValidateBitlist",
           "VbvAccC": "ValidateBitvector", "VbvPadC": "ValidateBitvector", "ScUAccC": "Scalars 함수 명세",
           "LuUAccC": "ListU64 함수 명세"}
HAND_KEYWORDS = ["makeslice", "memmove", "growslice", "newobject", "convT64", "fmt", "ValidateBitlist"]
SPEC_CONTRACT = {"ssz.ValidateBitvector": {"VbvAccC", "VbvPadC"}}


def short(n):
    return n.rsplit(".", 1)[-1]


def post_class(p):
    if not p.get("eventually"):
        return "not Eventually"
    if p["dmem_eq"]:
        return "memory identity"
    if p["frame"] and not p["true"]:
        return "frame exact"
    if p["frame"]:
        return "frame + True"
    return "no frame" + (" (True)" if p["true"] else "")


def hand_table(report):
    lines = open(report).read().split("\n")
    i = next(k for k, l in enumerate(lines) if l.startswith("| 타입 | 수용 방향"))
    head = [c.strip() for c in lines[i].strip("|").split("|")]
    rows = {}
    for l in lines[i + 2:]:
        if not l.startswith("|"):
            break
        cells = [c.strip() for c in l.strip("|").split("|")]
        rows[cells[0]] = dict(zip(head, cells))
    return head, rows


def main():
    log, thp, resp, report, out_json, out_md = sys.argv[1:7]
    comp = {}
    for line in open(log):
        if line.startswith("COMPLETE {"):
            d = json.loads(line[len("COMPLETE "):])
            comp[short(d["name"])] = d
    th = json.load(open(thp))
    obl = th["hand_case"]["obligations"]
    neg = []
    for line in open(resp):
        f = [x.strip() for x in line.split("|")]
        if len(f) >= 5:
            # a case whose mutation leaves the instruction unchanged ('X' -> 'X') is a control, not a negative test
            mu = re.search(r"'([^']*)' -> '([^']*)'", f[1])
            if mu and mu.group(1) == mu.group(2):
                continue
            neg.append({"case": f[0], "designated": f[2].split(" ")[0], "result": f[4]})
    head, hand = hand_table(report)
    rows, table = [], []
    for hname, t in ROWS:
        tob = [r for r in obl if r["type"] == t]
        mains = sorted({n for r in tob for n in r["hand_theorems"] if n in comp and r["obligation"] not in ("compose_hupd", "compose_witness")})
        has_wit = lambda n: n in comp and len(comp[n]["witnesses"]) > 0
        # accept
        acc = [n for r in tob if r["obligation"] == "accept" for n in r["hand_theorems"]]
        links = sorted({short(x) for n in acc if n in comp for x in comp[n]["ethlib_links"]})
        rspec = sorted({n for r in tob if r["obligation"] == "reject_spec" for n in r["hand_theorems"]})
        accept = ("EthLib→기계어" if acc and all(has_wit(n) for n in acc) and links else "없음") + \
                 (f" (link: {', '.join(links)})" if links else "") + (f" + EthLib 거부 정리 {', '.join(rspec)}" if rspec else "")
        # rejects
        dec = [r for r in tob if r["function"] == "UnmarshalSSZ" and r["obligation"] == "reject"]
        closed = [r for r in dec if r["hand_theorems"] and all(has_wit(n) for n in r["hand_theorems"])]
        open_ = [r["site_kind"] for r in dec if r not in closed]
        rejects = f"{len(closed)}/{len(dec)}" + (f". 남음: {', '.join(open_)}" if open_ else "")
        # witnesses
        wits = sorted({w["name"] for n in mains for w in comp[n]["witnesses"]})
        # contracts
        cs = set()
        for n in mains:
            cs.update(short(c) for c in comp[n]["contracts"])
            for v in comp[n]["contracts_via"]:
                cs.update(short(c) for c in v["contracts"])
        kws = sorted({KEYWORD[c] for c in cs})
        # negative
        cases = []
        for c in neg:
            d = c["designated"]
            if d in mains or (d in comp and set(map(short, comp[d]["dependent_mains"])) & set(mains)):
                cases.append(c["case"])
            else:
                for spec, cc in SPEC_CONTRACT.items():
                    if d in th["callee_function_specs"].get(spec, []) and cc & cs:
                        cases.append(c["case"])
        # compose
        ch = [n for r in tob if r["obligation"] == "compose_hupd" for n in r["hand_theorems"]]
        compose = "없음" if not ch else ", ".join(f"{n} (증인 {len(comp[n]['witnesses'])})" for n in ch if n in comp)
        # post
        post = {f"{r['function']}.{r['obligation']}": post_class(comp[n]["post"]) for r in tob
                for n in r["hand_theorems"] if n in comp and r["obligation"] in ("accept", "marshal", "size")}
        derived = {"수용 방향": accept, "거부 경로 (닫힘 / 남음)": rejects, "증인": f"{len(wits)} 선언",
                   "추상 모델": ", ".join(kws) or "없음", "부정 시험": ", ".join(cases) or "없음",
                   "조합": compose, "사후": "; ".join(f"{k}: {v}" for k, v in post.items())}
        hc = hand.get(hname, {})
        cmp = {}
        # per-cell comparison where a mechanical rule exists
        m = re.match(r"(\d+)/(\d+)", hc.get("거부 경로 (닫힘 / 남음)", ""))
        cmp["거부 경로 (닫힘 / 남음)"] = ("equal" if m and (int(m.group(1)), int(m.group(2))) == (len(closed), len(dec)) else
                                     f"different: hand {m.group(0) if m else '?'}, derived {len(closed)}/{len(dec)}")
        hk = sorted({k for k in HAND_KEYWORDS if k.lower() in hc.get("추상 모델", "").lower()})
        dk = sorted(k for k in kws if k in HAND_KEYWORDS)
        cmp["추상 모델"] = "equal" if hk == dk else f"different: hand {hk}, derived {dk}"
        hn = sorted(re.findall(r"[a-z0-9]+", hc.get("부정 시험", "").replace("없음", "")))
        cmp["부정 시험"] = "equal" if hn == sorted(cases) else f"different: hand {hn}, derived {sorted(cases)}"
        hcomp = hc.get("조합", "")
        dn = sorted(ch)
        hnames = sorted(re.findall(r"\w+_unmarshal_then_marshal", hcomp))
        hwit = "증인 없음" not in hcomp and bool(hnames)
        dwit = all(len(comp[n]["witnesses"]) > 0 for n in ch if n in comp) and bool(ch)
        cmp["조합"] = "equal" if hnames == dn and hwit == dwit else f"different: hand {hnames} witness={hwit}, derived {dn} witness={dwit}"
        ha = hc.get("수용 방향", "")
        cmp["수용 방향"] = "equal" if ("EthLib→기계어" in ha) == accept.startswith("EthLib→기계어") and (("거부" in ha) == bool(rspec)) \
            else f"different: hand '{ha}', derived '{accept}'"
        hp = hc.get("사후", "")
        size_mem = post.get("SizeSSZ.size") == "memory identity"
        cmp["사후"] = ("size: equal" if ("크기 동일" in hp) == size_mem else f"size: different (hand '{hp}', derived size {post.get('SizeSSZ.size')})")
        cmp["증인"] = "not compared (free text)"
        cmp["Go 값"] = "not derivable from Lean (goval)"
        rows.append({"type": t, "hand_row": hname, "derived": derived, "hand": hc, "compare": cmp,
                     "mains": mains, "witnesses": wits, "contracts": sorted(cs), "open_reject_sites": open_})
        table.append(f"| {hname} | " + " | ".join(derived[c] if c in derived else "(goval)" for c in head[1:]) + " |")
    counts = {"cells_compared": sum(1 for r in rows for v in r["compare"].values() if v == "equal" or v.startswith("different") or v.startswith("size")),
              "equal": sum(1 for r in rows for v in r["compare"].values() if v in ("equal", "size: equal")),
              "different": sum(1 for r in rows for v in r["compare"].values() if v.startswith("different") or v.startswith("size: different")),
              "not_compared": sum(1 for r in rows for v in r["compare"].values() if v.startswith("not")),
              "mains_resolved": sum(1 for n in comp if "error" not in comp[n]),
              "mains_with_witness": sum(1 for n in comp if comp[n].get("witnesses"))}
    json.dump({"schema": "fvphase1c.gate-table/1", "counts": counts, "rows": rows}, open(out_json, "w"), indent=1, ensure_ascii=False)
    md = ["| " + " | ".join(head) + " |", "| " + " | ".join("---" for _ in head) + " |"] + table
    open(out_md, "w").write("\n".join(md) + "\n")
    print(json.dumps(counts))
    for r in rows:
        for k, v in r["compare"].items():
            if v.startswith("different") or v.startswith("size: different"):
                print(r["type"], k, v)


if __name__ == "__main__":
    main()
