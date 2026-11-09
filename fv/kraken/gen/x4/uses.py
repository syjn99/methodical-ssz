#!/usr/bin/env python3
"""Hand-theorem use check of the generated theorems (X4, anchored templates).

Usage: uses.py write <out.lean> <module>... -- <generated theorem>... [--control <stmt>=<hand theorem>]
       uses.py check <lean-log> <out.json> <generated theorem>...
For each generated theorem, the Lean file follows the constants it uses (type and value), through every
Gen1cX4 declaration, and prints the constants outside Gen1cX4 whose names end in `_main` or
`_unmarshal_then_marshal` (the hand main theorems). Expected: none. The control declares
`Gen1cX4.UsesCtl.c : <stmt> := <hand theorem>` in the check file; it must report that hand theorem. The anchored templates copy the hand
declarations into Gen1cX4; this shows that the proofs do not lean on the hand theorems they restate.
Python 3 standard library only.
"""
import json
import re
import sys

if sys.argv[1] == "write":
    out, rest = sys.argv[2], sys.argv[3:]
    k = rest.index("--")
    mods, names = rest[:k], rest[k + 1:]
    ctl = []
    if "--control" in names:
        i = names.index("--control")
        st, hand = names[i + 1].split("=")
        names = names[:i] + ["Gen1cX4.UsesCtl.c"]
        ctl = ["open Fk Fk.Code in", f"theorem Gen1cX4.UsesCtl.c [Host] : {st} := {hand}", ""]
    lst = ", ".join(f"``{n}" for n in names)
    open(out, "w").write("\n".join([*[f"import {m}" for m in mods], "", *ctl, "open Lean Meta in",
        "#eval show MetaM Unit from do",
        "  let env ← getEnv",
        f"  for g in [{lst}] do",
        "    let mut seen : NameSet := {}",
        "    let mut todo : Array Name := #[g]",
        "    let mut bad : Array Name := #[]",
        "    while !todo.isEmpty do",
        "      let n := todo.back!",
        "      todo := todo.pop",
        "      if seen.contains n then continue",
        "      seen := seen.insert n",
        "      let some ci := env.find? n | continue",
        "      let v : Option Expr := match ci with | .thmInfo i => some i.value | .defnInfo i => some i.value | _ => none",
        "      for c in ci.type.getUsedConstants ++ (v.map Expr.getUsedConstants).getD #[] do",
        "        if (`Gen1cX4).isPrefixOf c then todo := todo.push c",
        "        else if c.toString.endsWith \"_main\" || c.toString.endsWith \"_unmarshal_then_marshal\" then",
        "          bad := bad.push c",
        "    IO.println s!\"X4USES {g} {seen.size} {bad.toList}\"", ""]))
else:
    log, out, names = open(sys.argv[2]).read(), sys.argv[3], sys.argv[4:]
    rows, ok = [], True
    for n in names:
        m = re.search(rf"^X4USES {re.escape(n)} (\d+) \[(.*)\]$", log, re.M)
        hand = [x.strip() for x in m[2].split(",") if x.strip()] if m else None
        good = bool(hand) if n == "Gen1cX4.UsesCtl.c" else hand == []
        ok &= good
        rows.append({"name": n, "gen1cx4_decls_followed": int(m[1]) if m else None, "hand_mains_used": hand, "ok": good})
    json.dump({"rows": rows, "none_used": ok}, open(out, "w"), indent=1)
    print(json.dumps({"names": len(rows), "none_used": ok}))
    sys.exit(0 if ok else 1)
