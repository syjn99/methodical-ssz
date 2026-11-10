#!/usr/bin/env python3
"""prysm-e2e: the six-element table and the totals line, from saved JSON only.

Usage: table.py <e2e-dir> [<markdown-file>...]
<e2e-dir> = fv/kraken/prysm/go1.26.10/e2e (e2e.json, negative/result.json, differential.json, axioms.json).
Prints the table. For each markdown file, replaces the table that starts with the header line below
(up to the next blank line) and the line that starts with "부정 시험 전체:". Python 3 stdlib only.
Column "나머지" (audit AU-11): read by program from the theorem statements in fv/kraken/lean/{E2e,E2eAd}:
"`⋆ True`" when the statement contains `⋆ fun _ => True` (or `⋆ True`), "exact frame" for another machine
theorem (`Eventually` / `step1` in the statement), "n/a" otherwise; a row with several theorems lists each class.
"""
import json
import pathlib
import re
import sys

HEAD = "| 정리 | 의무 | 문장 | 증인 | 기계어 정리 | 나머지 | 링크 | 부정 시험 | Go 값 |"
OLD_HEADS = ["| 정리 | 의무 | 문장 | 증인 | 기계어 정리 | 링크 | 부정 시험 | Go 값 |"]
LEAN = pathlib.Path(__file__).resolve().parent.parent.parent / "lean"
TRUE_REM = re.compile(r"⋆\s*(fun _ => True|True)\b")


def statements():
    src = {}
    for f in sorted(LEAN.glob("E2e/*.lean")) + sorted(LEAN.glob("E2eAd/*.lean")):
        L = f.read_text().split("\n")
        for i, l in enumerate(L):
            m = re.match(r"^(?:private )?theorem (\S+)", l)
            if not m:
                continue
            out = []
            for l2 in L[i:]:
                out.append(l2)
                if re.search(r":=\s*(by)?\s*$", l2) or re.search(r":= by\b", l2):
                    break
            src.setdefault(m[1], "\n".join(out))
    return src


def remainder(name, src):
    cls = {}
    for x in re.findall(r"[A-Za-z_][A-Za-z0-9_.']*", name):
        s = src.get(x.split(".")[-1])
        if s is None or "_" not in x:
            continue
        k = "`⋆ True`" if TRUE_REM.search(s) else ("exact frame" if ("Eventually" in s or "step1" in s) else "n/a")
        cls.setdefault(k, []).append(x.split(".")[-1])
    if not cls:
        return "n/a"
    if len(cls) == 1:
        return next(iter(cls))
    return "; ".join(f"{k} ({', '.join(v)})" for k, v in cls.items())


def build(d):
    e = json.load(open(d / "e2e.json"))
    neg = json.load(open(d / "negative" / "result.json"))["cases"]
    dif = json.load(open(d / "differential.json"))
    ax = json.load(open(d / "axioms.json"))
    rows = [HEAD, "| --- | --- | --- | --- | --- | --- | --- | --- | --- |"]
    src = statements()
    for t in e["theorems"]:
        n = t["negative"]
        if n == "done":
            cs = [c for c in neg if any(c["id"].startswith(p) for p in t["neg_ids"])]
            n = f"{sum(c['pass'] for c in cs)}/{len(cs)} 통과"
        rows.append(f"| `{t['name']}` | {t['kind']} | {t['statement']} | {t['witness']} | {t['theorem']} | "
                    f"{remainder(t['name'], src)} | {t['link']} | {n} | {t['go_value']} |")
    tot = (f"부정 시험 전체: {sum(c['pass'] for c in neg)}/{len(neg)} 통과 (`negative/result.json`). "
           f"Go 차분: {dif['cases']}건, 불일치 {dif['mismatches']}건 (`differential.json`). "
           f"공리: {ax['count']}개 이름, 판정 {ax['verdict']} (`axioms.json`).")
    return rows, tot


def patch(md, rows, tot):
    lines = md.read_text().split("\n")
    i = next(n for n, l in enumerate(lines) if l in [HEAD] + OLD_HEADS)
    j = i
    while j < len(lines) and lines[j].strip():
        j += 1
    lines[i:j] = rows
    k = next(n for n, l in enumerate(lines) if l.startswith("부정 시험 전체:"))
    lines[k] = tot
    md.write_text("\n".join(lines))


def main(d, *mds):
    d = pathlib.Path(d)
    rows, tot = build(d)
    print("\n".join(rows))
    print()
    print(tot)
    for m in mds:
        patch(pathlib.Path(m), rows, tot)
    return 0


if __name__ == "__main__":
    sys.exit(main(*sys.argv[1:]))
