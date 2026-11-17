#!/usr/bin/env python3
"""Compare two decl_dump.lean outputs (reviewed base vs head), both directions.

usage: decl_drift.py BASE.tsv HEAD.tsv [--allow FILE]

A declaration drifts when it is REMOVED (in base only), ADDED (in head only),
or CHANGED in kind, type hash, value hash (def/opaque) or axiom set.
An axiom-set change is drift even if every axiom is on the allowed policy
list: "same allowed axioms" is not "no drift".

Allowlist file: one entry per line, `<declaration name> <reason>`; `#` starts
a comment. The reason is required. An allowlisted drift is printed as ALLOWED
with its reason. An allowlist entry that matches no drift is printed as
UNUSED-ALLOW and counts as drift, so the list stays exact.

Exit codes: 0 clean, 1 drift (or unused allowlist entry), 2 usage error
(missing/unreadable file, bad header, different Lean builds, empty dump,
malformed line or allowlist entry).

Limits: hashes come from Lean's structural Expr.hash; equal hashes are not a
proof of definitional equivalence, and different hashes do not say what
changed. Theorem proofs are compared only through their axiom sets.
"""
import sys

USAGE = "usage: decl_drift.py BASE.tsv HEAD.tsv [--allow FILE]"


class Usage(Exception):
    pass


def load_dump(path):
    try:
        with open(path, encoding="utf-8") as f:
            lines = f.read().splitlines()
    except OSError as e:
        raise Usage(f"cannot read {path}: {e}")
    if not lines or not lines[0].startswith("# decl_dump v1 "):
        raise Usage(f"{path}: missing '# decl_dump v1' header")
    header = {}
    for tok in lines[0].split()[3:]:
        k, _, v = tok.partition("=")
        header[k] = v
    if "lean" not in header or "githash" not in header:
        raise Usage(f"{path}: header lacks lean= or githash=")
    rows = {}
    for i, line in enumerate(lines[1:], start=2):
        if not line:
            continue
        cols = line.split("\t")
        if len(cols) != 5:
            raise Usage(f"{path}:{i}: expected 5 tab-separated columns")
        name = cols[0]
        if name in rows:
            raise Usage(f"{path}:{i}: duplicate declaration {name}")
        rows[name] = {"kind": cols[1], "type": cols[2], "value": cols[3], "axioms": cols[4]}
    if not rows:
        raise Usage(f"{path}: no declarations (refusing a vacuous comparison)")
    return header, rows


def load_allow(path):
    allow = {}
    try:
        with open(path, encoding="utf-8") as f:
            lines = f.read().splitlines()
    except OSError as e:
        raise Usage(f"cannot read allowlist {path}: {e}")
    for i, raw in enumerate(lines, start=1):
        line = raw.split("#", 1)[0].strip()
        if not line:
            continue
        parts = line.split(None, 1)
        if len(parts) < 2:
            raise Usage(f"{path}:{i}: allowlist entry needs '<name> <reason>'")
        allow[parts[0]] = parts[1].strip()
    return allow


def diff(base, head):
    out = []
    for name in sorted(set(base) | set(head)):
        b, h = base.get(name), head.get(name)
        if h is None:
            out.append((name, "REMOVED", ""))
        elif b is None:
            out.append((name, "ADDED", f"kind={h['kind']} axioms={h['axioms']}"))
        else:
            what = [f"{k}: {b[k]} -> {h[k]}" for k in ("kind", "type", "value", "axioms") if b[k] != h[k]]
            if what:
                out.append((name, "CHANGED", "; ".join(what)))
    return out


def main(argv):
    args = list(argv)
    allow_path = None
    if "--allow" in args:
        i = args.index("--allow")
        if i + 1 >= len(args):
            raise Usage(USAGE)
        allow_path = args[i + 1]
        del args[i:i + 2]
    if len(args) != 2 or any(a.startswith("-") for a in args):
        raise Usage(USAGE)
    bh, base = load_dump(args[0])
    hh, head = load_dump(args[1])
    if (bh["lean"], bh["githash"]) != (hh["lean"], hh["githash"]):
        raise Usage(f"dumps come from different Lean builds ({bh['lean']} {bh['githash']} vs "
                    f"{hh['lean']} {hh['githash']}); hashes are not comparable")
    if bh.get("roots") != hh.get("roots"):
        raise Usage(f"dumps cover different roots ({bh.get('roots')} vs {hh.get('roots')})")
    allow = load_allow(allow_path) if allow_path else {}
    drift = 0
    used = set()
    for name, tag, detail in diff(base, head):
        if name in allow:
            used.add(name)
            print(f"ALLOWED\t{tag}\t{name}\t{detail}\treason: {allow[name]}")
        else:
            drift += 1
            print(f"{tag}\t{name}\t{detail}")
    for name in sorted(set(allow) - used):
        drift += 1
        print(f"UNUSED-ALLOW\t{name}\treason: {allow[name]}")
    print(f"SUMMARY base={len(base)} head={len(head)} drift={drift} allowed={len(used)}")
    return 1 if drift else 0


if __name__ == "__main__":
    try:
        sys.exit(main(sys.argv[1:]))
    except Usage as e:
        print(f"decl_drift: {e}", file=sys.stderr)
        sys.exit(2)
