#!/usr/bin/env python3
"""Tests of the generator skeleton (P4).

  test_emit.py prepare <work-dir> <desc-work-dir>
      Take the Descs and the checker result of a gen/desc/test_desc.py run
      (<desc-work-dir>/orig, <desc-work-dir>/main.result.json), run emit.py for the 9 hand
      types, selected by package-qualified name (old Go 1.26.3 ELF, read-only) into
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
TGT = "github.com/OffchainLabs/methodical-ssz/fv/kraken/target"
HAND_Q = [f"{TGT}/prysm.{t}" if t in ("Checkpoint", "AttestationData") else f"{TGT}.{t}" for t in HAND]
FROZEN = {"THEOREMS.json": "e4d7dcf8be132789333aced22c5e1e4278539edf4aee6aaeef9cc77dd141b342",
          "ASSUMPTIONS.json": "9decb220f35736b9b8d07700f606e146c1c076f5016789ac5c7c22c1a213905f"}
# (emitted statement, hand theorem, expected, explanation)
COMPARE = [
    ("Gen1c.Hand.Checkpoint.size_stmt", "cp_size_main", "SAME", "fixed-size template"),
    ("Gen1c.Hand.AttestationData.size_stmt", "ad_size_main", "SAME", "fixed-size template"),
    ("Gen1c.Hand.BitVec.size_stmt", "bv_size_main", "SAME", "fixed-size template"),
    ("Gen1c.Hand.FixedVec.size_stmt", "fv_size_main", "SAME", "fixed-size template"),
    ("Gen1c.Hand.Scalars.size_stmt", "sc_size_main", "DIFF",
     "sc_size_main states only pc and rax = 16, without rsp + 8 and memory identity (REPORT section 0 item 2, "
     "astra fix2 review finding 5); the template states the full postcondition"),
    ("Gen1c.Hand.Checkpoint.size_stmt", "ad_size_main", "DIFF", "control: 40 vs 128, must differ"),
]
IMPORTS = ["Fk.CpSpec", "Fk.AdSpec", "Fk.BvSpec", "Fk.FvSmall", "Fk.ScSize"]


def sha(p):
    return hashlib.sha256(open(p, "rb").read()).hexdigest()


def outdir(t):
    """Output directory of a hand type: <package with / -> _>/<Type> (emit.py)."""
    pkg = f"{TGT}/prysm" if t in ("Checkpoint", "AttestationData") else TGT
    return f"{pkg.replace('/', '_')}/{t}"


def run_emit(out, desc_dir, result, types=None, extra=()):
    k = KRAKEN
    cmd = [sys.executable, "-I", f"{HERE}/emit.py", "--out", out, "--desc-dir", desc_dir, "--desccheck-result", result,
           "--go", f"{k}/target/types.ssz.go,{k}/target/types1b.ssz.go,{k}/target/prysm/types.ssz.go",
           "--elf", f"{k}/link/out/p1bin-amd64", "--nm", f"{k}/link/out/p1bin-amd64.nm", "--norm", f"{k}/link/out/norm",
           "--types", ",".join(types or HAND_Q), "--code-prefix", "/target/prysm=Prysm", "--obligations", "hand_case", *extra]
    return subprocess.run(cmd, capture_output=True, text=True)


def prepare(work, dwork):
    import shutil
    if os.path.exists(work):
        shutil.rmtree(work)
    os.makedirs(work)
    res = {"checks": []}
    desc_dir = f"{dwork}/orig"
    log = f"{dwork}/main.result.json"
    before = {n: sha(f"{KRAKEN}/gen/frozen/{n}") for n in FROZEN}
    r = run_emit(f"{work}/out", desc_dir, log)
    res["emit"] = {"rc": r.returncode, "stdout": r.stdout.strip(), "stderr": r.stderr.strip()[-500:]}
    res["checks"].append(("emit rc 0", r.returncode == 0))
    after = {n: sha(f"{KRAKEN}/gen/frozen/{n}") for n in FROZEN}
    res["checks"].append(("frozen lists unchanged and equal to the P2 hashes", before == after == FROZEN))
    # guard control: an output inside lean/Fk must be refused and nothing written there
    bad = f"{KRAKEN}/lean/Fk/zz-gen1c-guard-test"
    g = run_emit(bad, desc_dir, log)
    res["checks"].append(("guard refuses lean/Fk output", g.returncode != 0 and "refusing" in g.stderr + g.stdout
                          and not os.path.exists(bad)))
    # end-to-end CLI controls (the full case table is gen1c/test_boundary.py)
    # control: a hand Desc changed after the check in a copied tree is refused (sha256 differs)
    tam = f"{work}/tampered"
    shutil.copytree(desc_dir, tam)
    nd = json.load(open(f"{tam}/Nested.desc.json"))
    nd["ssz"]["fields"][2]["fields"][0]["limit"] = 17
    json.dump(nd, open(f"{tam}/Nested.desc.json", "w"), indent=1)
    t1 = run_emit(f"{work}/out-tampered", tam, log)
    res["checks"].append(("emit refuses a Desc changed after the check (copied tree, sha256)",
                          t1.returncode != 0 and "sha256" in t1.stderr + t1.stdout))
    # control: the escaped hand ListU64 (review r2 n01: package + '/') in place of the original,
    # selected by bare name: its record is a FAIL mutant -> refused
    esc = f"{work}/escaped"
    os.makedirs(esc)
    for f in os.listdir(desc_dir):
        src = f"{dwork}/mut/n01-esc-pkg-slash.desc.json" if f == "ListU64.desc.json" else f"{desc_dir}/{f}"
        os.symlink(src, f"{esc}/{f}")
    t2 = run_emit(f"{work}/out-escaped", esc, log, types=["ListU64"])
    res["checks"].append(("emit refuses a bare type name (and the escaped n01 next to it)", t2.returncode != 0
                          and "package-qualified" in t2.stderr + t2.stdout))
    # control: the result of a failed run (scenario s-n01, verdict FAIL) is refused
    t3 = run_emit(f"{work}/out-cov", desc_dir, f"{dwork}/scen/s-n01.result.json")
    res["checks"].append(("emit refuses a checker result whose verdict is FAIL", t3.returncode != 0
                          and "verdict" in t3.stderr + t3.stdout))
    # control: the checked file itself changed after the check (same path): sha256 differs -> refused
    orig_nested = f"{desc_dir}/Nested.desc.json"
    keep = open(orig_nested, "rb").read()
    try:
        open(orig_nested, "w").write(json.dumps(nd, indent=1))
        t4 = run_emit(f"{work}/out-changed", desc_dir, log)
    finally:
        open(orig_nested, "wb").write(keep)
    res["checks"].append(("emit refuses a checked file changed in place after the check (sha256)",
                          t4.returncode != 0 and "sha256" in t4.stderr + t4.stdout))
    # control (R4-S5): a second run into the non-empty output directory is refused, nothing merged
    before_out = sorted(os.listdir(f"{work}/out"))
    t5 = run_emit(f"{work}/out", desc_dir, log)
    res["checks"].append(("emit refuses a non-empty --out (no merge)", t5.returncode != 0 and "not an empty directory" in t5.stderr + t5.stdout
                          and sorted(os.listdir(f"{work}/out")) == before_out))
    res["controls_stderr"] = [x.stderr.strip()[-300:].replace(work + "/", "").replace(dwork + "/", "") for x in (t1, t2, t3, t4, t5)]
    m = json.load(open(f"{work}/out/manifest.json"))
    files = sorted(os.listdir(f"{work}/out/{outdir('Checkpoint')}"))
    res["checks"].append(("per-type files", files == ["desc.json", "negative.json", "statements.lean", "witness.json"]))
    sorry = [p for t in HAND for p in [f"{work}/out/{outdir(t)}/statements.lean"] if re.search(r"\b(sorry|admit|axiom|native_decide|bv_decide)\b", open(p).read())]
    res["checks"].append(("no sorry/admit/axiom/native_decide/bv_decide in emitted Lean", not sorry))
    # data cross-check with the include API item table (old ELF offsets)
    sys.path.insert(0, HERE)
    sys.dont_write_bytecode = True
    import include_adapter
    api = include_adapter.check_api()
    res["include_api_version"] = include_adapter.API_VERSION
    cross = []
    for it in api["items"]:
        if it.get("label") != include_adapter.RODATA_LABEL:
            continue
        hit = [k for k, v in m["data_items"].items() if v.get("off") == it["offset"] and v.get("length") == it["length"]
               and v.get("api_id") == it["id"]]
        cross.append({"api_id": it["id"], "offset": it["offset"], "length": it["length"], "emitted": hit})
    used = [c for c in cross if c["emitted"]]
    res["data_cross_check"] = cross
    res["checks"].append(("every emitted format literal is located once in go:string.*",
                          all("error" not in v for v in m["data_items"].values())))
    res["checks"].append(("emitted rodata items that the API also lists agree on offset and length",
                          all(len(c["emitted"]) >= 1 for c in used) and len(used) >= 7))
    # Lean comparison file
    stm = "\n".join(open(f"{work}/out/{outdir(t)}/statements.lean").read() for t in ["Checkpoint", "AttestationData", "BitVec", "FixedVec", "Scalars"])
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
        sys.exit(prepare(sys.argv[2], sys.argv[3]))
    elif sys.argv[1] == "evaluate":
        sys.exit(evaluate(sys.argv[2], sys.argv[3], sys.argv[4]))
    raise SystemExit(__doc__)
