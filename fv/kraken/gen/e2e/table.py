#!/usr/bin/env python3
"""prysm-e2e: the six-element table and the totals line, from saved JSON only.

Usage: table.py <e2e-dir> [<markdown-file>...]
<e2e-dir> = fv/kraken/prysm/go1.26.10/e2e (e2e.json, negative/result.json, differential.json, axioms.json).
Prints the table. For each markdown file, replaces the table that starts with the header line below
(up to the next blank line) and the line that starts with "부정 시험 전체:". Python 3 stdlib only.
"""
import json
import pathlib
import sys

HEAD = "| 정리 | 의무 | 문장 | 증인 | 기계어 정리 | 링크 | 부정 시험 | Go 값 |"


def build(d):
    e = json.load(open(d / "e2e.json"))
    neg = json.load(open(d / "negative" / "result.json"))["cases"]
    dif = json.load(open(d / "differential.json"))
    ax = json.load(open(d / "axioms.json"))
    rows = [HEAD, "| --- | --- | --- | --- | --- | --- | --- | --- |"]
    for t in e["theorems"]:
        n = t["negative"]
        if n == "done":
            cs = [c for c in neg if any(c["id"].startswith(p) for p in t["neg_ids"])]
            n = f"{sum(c['pass'] for c in cs)}/{len(cs)} 통과"
        rows.append(f"| `{t['name']}` | {t['kind']} | {t['statement']} | {t['witness']} | {t['theorem']} | "
                    f"{t['link']} | {n} | {t['go_value']} |")
    tot = (f"부정 시험 전체: {sum(c['pass'] for c in neg)}/{len(neg)} 통과 (`negative/result.json`). "
           f"Go 차분: {dif['cases']}건, 불일치 {dif['mismatches']}건 (`differential.json`). "
           f"공리: {ax['count']}개 이름, 판정 {ax['verdict']} (`axioms.json`).")
    return rows, tot


def patch(md, rows, tot):
    lines = md.read_text().split("\n")
    i = lines.index(HEAD)
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
