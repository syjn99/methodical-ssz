#!/usr/bin/env python3
"""Tests of the Desc producer and the independent checker (P3).

  test_desc.py prepare <work-dir>
      Produce Desc files for the 9 hand types (with Fv1 references) and for
      every type of the Prysm inventory I, then write mutated copies (negative
      controls) and <work-dir>/list.txt, <work-dir>/expect.json.
  test_desc.py evaluate <work-dir> <checker-log> <out.json>
      Compare the checker log with the expectations. An original must PASS.
      A mutant must FAIL, and its failed checks must include the designated
      check (the stated reason). Exit status 1 on any mismatch.

The checker run itself is gated Lean:
  cd fv/kraken/lean && DESC_LIST=<work-dir>/list.txt lake env lean ../gen/desccheck/DescCheck.lean
Python 3 standard library only. Run with python3 -I.
"""
import copy
import json
import os
import re
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
KRAKEN = os.path.normpath(os.path.join(HERE, "..", ".."))

# (id, base file, what, designated check, mutation function)
def _set(path, value):
    def f(d):
        o = d
        for k in path[:-1]:
            o = o[k]
        o[path[-1]] = value(o[path[-1]]) if callable(value) else value
    return f


def _both(*fs):
    def f(d):
        for g in fs:
            g(d)
    return f


MUTANTS = [
    ("m-fixed-size", "Scalars", "wrong fixed size (16 -> 17)", "fixed", _set(["fixed_size"], 17)),
    ("m-offset", "AttestationData", "wrong field offset (field 2: 16 -> 17)", "offset[2]", _set(["fields", 2, "offset"], 17)),
    ("m-width", "Checkpoint", "wrong field width (field 1: 32 -> 31)", "width[1]", _set(["fields", 1, "width"], 31)),
    ("m-head", "Nested", "wrong head size (28 -> 32)", "head", _set(["fixed_part_size"], 32)),
    ("m-variable", "Nested", "variable field claimed fixed (field 2)", "variable[2]", _set(["fields", 2, "variable"], False)),
    ("m-limit-claim", "ListU64", "wrong limit claim (16 -> 17)", "limit[0]", _set(["fields", 0, "limit"], 17)),
    ("m-elem", "ListU64", "wrong element size (8 -> 4)", "elem[0]", _set(["fields", 0, "elem_size"], 4)),
    ("m-limit-spec", "ListU64", "wrong limit against the spec (term and claim 16 -> 17)", "ref",
     _both(_set(["ssz", "fields", 0, "limit"], 17), _set(["fields", 0, "limit"], 17))),
    ("m-kind-spec", "BitL", "wrong kind against the spec (bitList -> byteList, claims follow)", "ref",
     _both(_set(["ssz", "fields", 0, "k"], "byteList"), _set(["fields", 0, "kind"], "byteList"))),
    ("m-uint-width", "Scalars", "wrong uint width against the spec (field 1: 2 -> 4, claims follow)", "ref",
     _both(_set(["ssz", "fields", 1, "w"], 4), _set(["fields", 1, "width"], 4), _set(["fields", 2, "offset"], 5),
           _set(["fields", 3, "offset"], 9), _set(["fields", 4, "offset"], 17), _set(["fixed_size"], 18),
           _set(["fixed_part_size"], 18))),
    ("m-wf", "FixedVec", "ill-formed type (vector length 4 -> 0)", "wf", _set(["ssz", "fields", 1, "n"], 0)),
    ("m-order", "prysm_v1alpha1.BeaconBlockBodyAltair", "wrong variable-field order (reversed)", "order", _set(["variable_order"], lambda o: list(reversed(o)))),
    ("m-kind-claim", "prysm_v1alpha1.StatusV2", "wrong kind claim (field 0 byteVector -> byteList)", "kind[0]", _set(["fields", 0, "kind"], "byteList")),
    ("m-offset-prysm", "prysm_v1alpha1.StatusV2", "wrong field offset (field 3: 44 -> 45)", "offset[3]", _set(["fields", 3, "offset"], 45)),
]


def prepare(work):
    os.makedirs(work, exist_ok=True)
    orig = os.path.join(work, "orig")
    mut = os.path.join(work, "mut")
    os.makedirs(mut, exist_ok=True)
    py = [sys.executable, "-I"]
    subprocess.run(py + [f"{HERE}/producer.py", orig, f"{HERE}/ir-hand.json", f"--refs={HERE}/refs-hand.json"], check=True)
    inv = json.load(open(f"{KRAKEN}/prysm/inventory.json"))
    names = ",".join(sorted(f"{t['package']}.{t['name']}" for t in inv["types"]))
    r = subprocess.run(py + [f"{HERE}/producer.py", orig, f"{KRAKEN}/prysm/ir/ir-mainnet.json", f"--types={names}"],
                       check=True, capture_output=True, text=True)
    prod = json.loads(r.stdout)
    files = sorted(os.listdir(orig))
    expect = {"originals": {}, "mutants": {}, "producer_skipped": prod["skipped"]}
    for f in files:
        expect["originals"][f"{orig}/{f}"] = "PASS"
    for mid, base, what, check, fn in MUTANTS:
        src = f"{orig}/{base}.desc.json"
        d = json.load(open(src))
        fn(d)
        dst = f"{mut}/{mid}.desc.json"
        with open(dst, "w") as fh:
            json.dump(d, fh, indent=1)
        expect["mutants"][dst] = {"id": mid, "twin": src, "what": what, "designated": check}
    with open(f"{work}/list.txt", "w") as fh:
        fh.write("\n".join(list(expect["originals"]) + list(expect["mutants"])) + "\n")
    with open(f"{work}/expect.json", "w") as fh:
        json.dump(expect, fh, indent=1)
    print(json.dumps({"originals": len(expect["originals"]), "mutants": len(expect["mutants"]),
                      "producer_skipped": prod["skipped"]}))


def evaluate(work, log, out):
    exp = json.load(open(f"{work}/expect.json"))
    res, fails = {}, {}
    for line in open(log):
        m = re.match(r"DESCCHECK-FILE (\S+) (PASS|FAIL)\s*(.*)$", line.rstrip("\n"))
        if m:
            res[m.group(1)] = m.group(2)
            fails[m.group(1)] = [x for x in m.group(3).split(",") if x]
    rows, bad = [], 0
    for p in exp["originals"]:
        got = res.get(p, "not run")
        ok = got == "PASS"
        bad += not ok
        rows.append({"file": os.path.basename(p), "role": "original", "result": got, "failed_checks": fails.get(p, []), "as_expected": ok})
    for p, m in exp["mutants"].items():
        got = res.get(p, "not run")
        twin = res.get(m["twin"], "not run")
        ok = got == "FAIL" and m["designated"] in fails.get(p, []) and twin == "PASS"
        bad += not ok
        rows.append({"file": os.path.basename(p), "role": "mutant", "id": m["id"], "what": m["what"],
                     "designated": m["designated"], "result": got, "failed_checks": fails.get(p, []),
                     "twin": os.path.basename(m["twin"]), "twin_result": twin, "as_expected": ok})
    done = [l for l in open(log) if l.startswith("DESCCHECK-DONE")]
    skips = sum(1 for l in open(log) if re.match(r"DESCCHECK \S+ probe SKIP ", l))
    summary = {"originals": len(exp["originals"]), "originals_pass": sum(r["role"] == "original" and r["as_expected"] for r in rows),
               "mutants": len(exp["mutants"]), "mutants_as_expected": sum(r["role"] == "mutant" and r["as_expected"] for r in rows),
               "unexpected": bad, "probe_skipped_files": skips, "done_line": done[-1].strip() if done else None,
               "producer_skipped": exp["producer_skipped"]}
    with open(out, "w") as fh:
        json.dump({"schema": "fvphase1c.desc-test/1", "summary": summary, "rows": rows}, fh, indent=1)
        fh.write("\n")
    print(json.dumps(summary, indent=1))
    return 1 if bad else 0


if __name__ == "__main__":
    if sys.argv[1] == "prepare":
        prepare(sys.argv[2])
    elif sys.argv[1] == "evaluate":
        sys.exit(evaluate(sys.argv[2], sys.argv[3], sys.argv[4]))
    else:
        raise SystemExit(__doc__)
