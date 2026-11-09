#!/usr/bin/env python3
"""Tests of the generator skeleton (P4).

  test_emit.py prepare <work-dir>
      Produce the 9 hand Descs (gen/desc/producer.py), run emit.py for them (old Go 1.26.3 ELF, read-only) into
      <work-dir>/out, run the guard control, check the frozen-list hashes, cross-check
      the emitted data items with the include API item table, and write
      <work-dir>/Compare.lean (statement comparison, to be run gated) and
      <work-dir>/prepare.json.
  test_emit.py evaluate <work-dir> <lean-log> <out.json>
      Read the comparison log and check it against the expectations below.

Lean run (gated): cd fv/kraken/lean && lake env lean <work-dir>/Compare.lean
Python 3 standard library only. Run with python3 -I.
"""
import hashlib
import json
import os
import re
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
KRAKEN = os.path.normpath(os.path.join(HERE, "..", ".."))
HAND = ["Scalars", "FixedVec", "ListU64", "BitVec", "Nested", "ListC", "BitL", "Checkpoint", "AttestationData"]
FROZEN = {"THEOREMS.json": "7b7a24f55047e3137c8745d27eec21d494fd1749cb26e277b71941dc6e10a479",
          "ASSUMPTIONS.json": "84ca497180efbc1c091289b453796fff1649378f71f1bdc9c35159202795385c"}
# (emitted statement, hand theorem, expected, explanation)
COMPARE = [
    ("Gen1c.Checkpoint.size_stmt", "cp_size_main", "SAME", "fixed-size template"),
    ("Gen1c.AttestationData.size_stmt", "ad_size_main", "SAME", "fixed-size template"),
    ("Gen1c.BitVec.size_stmt", "bv_size_main", "SAME", "fixed-size template"),
    ("Gen1c.FixedVec.size_stmt", "fv_size_main", "SAME", "fixed-size template"),
    ("Gen1c.Scalars.size_stmt", "sc_size_main", "DIFF",
     "sc_size_main states only pc and rax = 16, without rsp + 8 and memory identity (REPORT section 0 item 2, "
     "astra fix2 review finding 5); the template states the full postcondition"),
    ("Gen1c.Checkpoint.size_stmt", "ad_size_main", "DIFF", "control: 40 vs 128, must differ"),
]
IMPORTS = ["Fk.CpSpec", "Fk.AdSpec", "Fk.BvSpec", "Fk.FvSmall", "Fk.ScSize"]


def sha(p):
    return hashlib.sha256(open(p, "rb").read()).hexdigest()


def run_emit(out, desc_dir, extra=()):
    k = KRAKEN
    cmd = [sys.executable, "-I", f"{HERE}/emit.py", "--out", out, "--desc-dir", desc_dir,
           "--go", f"{k}/target/types.ssz.go,{k}/target/types1b.ssz.go,{k}/target/prysm/types.ssz.go",
           "--elf", f"{k}/link/out/p1bin-amd64", "--nm", f"{k}/link/out/p1bin-amd64.nm", "--norm", f"{k}/link/out/norm",
           "--types", ",".join(HAND), "--code-prefix", "/target/prysm=Prysm", "--obligations", "hand_case", *extra]
    return subprocess.run(cmd, capture_output=True, text=True)


def prepare(work):
    os.makedirs(work, exist_ok=True)
    res = {"checks": []}
    desc_dir = f"{work}/desc"
    r = subprocess.run([sys.executable, "-I", f"{KRAKEN}/gen/desc/producer.py", desc_dir, f"{KRAKEN}/gen/desc/ir-hand.json",
                        f"--refs={KRAKEN}/gen/desc/refs-hand.json"], capture_output=True, text=True)
    res["checks"].append(("producer rc 0 (9 hand Descs)", r.returncode == 0 and len(os.listdir(desc_dir)) == 9))
    before = {n: sha(f"{KRAKEN}/gen/frozen/{n}") for n in FROZEN}
    r = run_emit(f"{work}/out", desc_dir)
    res["emit"] = {"rc": r.returncode, "stdout": r.stdout.strip(), "stderr": r.stderr.strip()[-500:]}
    res["checks"].append(("emit rc 0", r.returncode == 0))
    after = {n: sha(f"{KRAKEN}/gen/frozen/{n}") for n in FROZEN}
    res["checks"].append(("frozen lists unchanged and equal to the P2 hashes", before == after == FROZEN))
    # guard control: an output inside lean/Fk must be refused and nothing written there
    bad = f"{KRAKEN}/lean/Fk/zz-gen1c-guard-test"
    g = run_emit(bad, desc_dir)
    res["checks"].append(("guard refuses lean/Fk output", g.returncode != 0 and "refusing" in g.stderr + g.stdout
                          and not os.path.exists(bad)))
    m = json.load(open(f"{work}/out/manifest.json"))
    files = sorted(os.listdir(f"{work}/out/Checkpoint"))
    res["checks"].append(("per-type files", files == ["desc.json", "negative.json", "statements.lean", "witness.json"]))
    sorry = [p for t in HAND for p in [f"{work}/out/{t}/statements.lean"] if re.search(r"\b(sorry|admit|axiom|native_decide|bv_decide)\b", open(p).read())]
    res["checks"].append(("no sorry/admit/axiom/native_decide/bv_decide in emitted Lean", not sorry))
    # data cross-check with the include API item table (old ELF offsets)
    sys.path.insert(0, HERE)
    sys.dont_write_bytecode = True
    import include_adapter
    api = include_adapter.check_api()
    res["include_api_version"] = include_adapter.API_VERSION
    cross = []
    for it in api["items"]:
        if it.get("label") != "go_string._":
            continue
        hit = [k for k, v in m["data_items"].items() if v.get("off") == it["offset"] and v.get("length") == it["length"]]
        cross.append({"api_id": it["id"], "offset": it["offset"], "length": it["length"], "emitted": hit})
    used = [c for c in cross if c["emitted"]]
    res["data_cross_check"] = cross
    res["checks"].append(("every emitted format literal is located once in go:string.*",
                          all("error" not in v for v in m["data_items"].values())))
    res["checks"].append(("emitted rodata items that the API also lists agree on offset and length",
                          all(len(c["emitted"]) >= 1 for c in used) and len(used) >= 7))
    # Lean comparison file
    stm = "\n".join(open(f"{work}/out/{t}/statements.lean").read() for t in ["Checkpoint", "AttestationData", "BitVec", "FixedVec", "Scalars"])
    pairs = ", ".join(f'(``{a}, ``{b})' for a, b, _, _ in COMPARE)
    lean = "\n".join([f"import {i}" for i in IMPORTS] + ["", "open Fk Fk.Code", "variable [Host]", "", stm, "",
        "open Lean Meta in",
        "#eval show MetaM Unit from do",
        f"  for (g, h) in [{pairs}] do",
        "    let hc ← getConstInfo h",
        "    let gc ← getConstInfo g",
        "    -- ∀ [inst : Host], gen inst   versus   the hand theorem's type",
        "    let gt ← forallTelescopeReducing gc.type fun xs _ => do",
        "      mkForallFVars xs (mkAppN (mkConst g (gc.levelParams.map mkLevelParam)) xs)",
        "    let same ← withTransparency .all (isDefEq gt hc.type)",
        "    IO.println s!\"COMPARE {g} {h} {if same then \"SAME\" else \"DIFF\"}\"",
        ""])
    open(f"{work}/Compare.lean", "w").write(lean)
    res["compare_expected"] = [{"gen": a, "hand": b, "expect": e, "why": w} for a, b, e, w in COMPARE]
    json.dump(res, open(f"{work}/prepare.json", "w"), indent=1)
    ok = all(c[1] for c in res["checks"])
    print(json.dumps({"checks": res["checks"], "all_ok": ok}, indent=1))
    return 0 if ok else 1


def evaluate(work, log, out):
    prep = json.load(open(f"{work}/prepare.json"))
    got = {}
    for line in open(log):
        m = re.match(r"COMPARE (\S+) (\S+) (SAME|DIFF)", line)
        if m:
            got[(m.group(1), m.group(2))] = m.group(3)
    rows = []
    for c in prep["compare_expected"]:
        g = got.get((c["gen"], c["hand"]), "not run")
        rows.append({**c, "got": g, "as_expected": g == c["expect"]})
    errors = [l.strip() for l in open(log) if re.search(r": error", l)]
    res = {"schema": "fvphase1c.gen-test/1", "prepare_checks": prep["checks"], "compare": rows,
           "lean_errors": errors, "all_ok": all(r["as_expected"] for r in rows) and not errors and all(c[1] for c in prep["checks"]),
           "data_cross_check": prep["data_cross_check"]}
    json.dump(res, open(out, "w"), indent=1)
    print(json.dumps({"compare": [(r["gen"], r["hand"], r["got"], r["as_expected"]) for r in rows],
                      "lean_errors": errors, "all_ok": res["all_ok"]}, indent=1))
    return 0 if res["all_ok"] else 1


if __name__ == "__main__":
    if sys.argv[1] == "prepare":
        sys.exit(prepare(sys.argv[2]))
    elif sys.argv[1] == "evaluate":
        sys.exit(evaluate(sys.argv[2], sys.argv[3], sys.argv[4]))
    raise SystemExit(__doc__)
