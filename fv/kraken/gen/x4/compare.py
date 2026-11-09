#!/usr/bin/env python3
"""Statement comparison for X4 (elaborated equality with the hand theorems).

Usage: compare.py <pairs.json> <out.lean>
pairs.json: {"imports": [...], "pairs": [[gen_stmt, hand_theorem, expect, why], ...], "no_smart_unfolding": bool (optional)}
For each pair the Lean file prints `X4COMPARE <gen> <hand> SAME|DIFF`: SAME iff
`∀ [Host], gen` and the hand theorem's type are definitionally equal (transparency all),
as in gen/gen1c/test_emit.py. Python 3 standard library only.
"""
import json
import sys

cfg = json.load(open(sys.argv[1]))
pairs = ", ".join(f"(``{g}, ``{h})" for g, h, _, _ in cfg["pairs"])
# "no_smart_unfolding": compare with smart unfolding off, so that a structurally recursive statement
# definition restated with the same text (Gen1cX4.lcObjs vs lcObjs) unfolds on a variable argument.
nsu = ["set_option smartUnfolding false in"] if cfg.get("no_smart_unfolding") else []
lean = "\n".join([f"import {i}" for i in cfg["imports"]] + ["", *nsu, "open Lean Meta in",
    "#eval show MetaM Unit from do",
    f"  for (g, h) in [{pairs}] do",
    "    let hc ← getConstInfo h",
    "    let gc ← getConstInfo g",
    "    let gt ← forallTelescopeReducing gc.type fun xs _ => do",
    "      mkForallFVars xs (mkAppN (mkConst g (gc.levelParams.map mkLevelParam)) xs)",
    "    let same ← withTransparency .all (isDefEq gt hc.type)",
    "    IO.println s!\"X4COMPARE {g} {h} {if same then \"SAME\" else \"DIFF\"}\"", ""])
open(sys.argv[2], "w").write(lean)
