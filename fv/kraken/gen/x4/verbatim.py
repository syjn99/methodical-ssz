#!/usr/bin/env python3
"""Verbatim share of generated proofs (INBOX 014 honesty rule).

Usage: verbatim.py <generated.lean> <hand.lean>[,<hand.lean>...] <theorem> [<theorem> ...]
For each generated theorem: the tactic lines (the lines after `:= by` up to the next blank line,
stripped, non-empty) and how many of them occur verbatim (stripped) as a line of the hand files.
The rest differ by lemma names, hypothesis names or generated numbers. Prints one JSON object.
Python 3 standard library only. Run with python3 -I -B.
"""
import json
import sys


def tactic_lines(path, name):
    lines = open(path).read().split("\n")
    i = next(i for i, l in enumerate(lines) if l.startswith(f"theorem {name} "))
    while not lines[i].rstrip().endswith(":= by"):
        i += 1
    out = []
    for l in lines[i + 1:]:
        if not l.strip():
            break
        out.append(l.strip())
    return out


def main():
    gen, hands, names = sys.argv[1], sys.argv[2].split(","), sys.argv[3:]
    hand = set()
    for h in hands:
        hand |= {l.strip() for l in open(h) if l.strip()}
    rows = {}
    for n in names:
        t = tactic_lines(gen, n)
        rows[n] = {"tactic_lines": len(t), "verbatim_in_hand": sum(x in hand for x in t)}
    print(json.dumps({"generated": gen, "hand": hands, "rows": rows}, indent=1))


if __name__ == "__main__":
    main()
