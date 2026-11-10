#!/usr/bin/env python3
"""prysm-e2e: parse `lake env lean gen/e2e/Axioms.lean` output into JSON; allowed axioms: propext,
Classical.choice, Quot.sound. Usage: axioms.py <log> <out.json> [<names.lean>] (default: the Axioms.lean next
to this file; the AttestationData set passes gen/e2e/AxiomsAd.lean). Exit 1 if any theorem uses another axiom,
if a theorem is missing from the output, or if `sorryAx` appears."""
import json, re, sys
log = open(sys.argv[1]).read()
src = sys.argv[3] if len(sys.argv) > 3 else __file__.replace("axioms.py", "Axioms.lean")
want = re.findall(r"#print axioms (\S+)", open(src).read())
ok = {"propext", "Classical.choice", "Quot.sound"}
res = {}
for m in re.finditer(r"'([^']+)' depends on axioms: \[([^\]]*)\]", log):
    res[m[1]] = [a.strip() for a in m[2].split(",") if a.strip()]
for m in re.finditer(r"'([^']+)' does not depend on any axioms", log):
    res[m[1]] = []
missing = [t for t in want if t not in res]
bad = {t: a for t, a in res.items() if not set(a) <= ok}
out = {"allowed": sorted(ok), "theorems": res, "missing": missing, "nonstandard": bad,
       "count": len(res), "verdict": "PASS" if not missing and not bad and "sorryAx" not in log else "FAIL"}
json.dump(out, open(sys.argv[2], "w"), indent=1)
print(out["verdict"], out["count"], "missing", missing, "nonstandard", bad)
sys.exit(0 if out["verdict"] == "PASS" else 1)
