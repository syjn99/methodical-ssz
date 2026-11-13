#!/usr/bin/env python3
"""Emit-boundary tests.

Usage: test_boundary.py <desc-work-dir> <out.json>
<desc-work-dir> is a gen/desc/test_desc.py work directory after the gated checker run
(main.result.json, scen/*.result.json). Every case calls emit.accept (the only way emit.py
takes a Desc) and records accepted / refused with the reason.

Cases:
- positive: the honest main result and the originals: 9 hand keys (hand_case), every in-scope
  Prysm key (prysm, one run), and the 3 out-of-scope Prysm keys refused.
- boundary: for every emit-boundary scenario of test_desc.py (each wrong hand-type Desc added
  next to the originals, and in place of its base): the scenario's result with a desc dir of
  exactly its list; hand_case for the 9 hand keys, and prysm for the mutant's own key when it
  is a non-hand key; all must be refused.
- forged and extra Desc inputs of desc/review/r3_mutants.py, rebuilt for the result-file protocol.
- own escapes x01-x14 against the result file and its binding, the expected-set source,
  the exception list and path handling.
Python 3 standard library only. Run with python3 -I.
"""
import contextlib
import copy
import hashlib
import io
import json
import os
import shutil
import sys

sys.dont_write_bytecode = True
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import emit  # noqa: E402

KRAKEN = os.path.normpath(os.path.join(HERE, "..", ".."))
TGT = "github.com/OffchainLabs/methodical-ssz/fv/kraken/target"
HAND = [f"{TGT}.{t}" for t in ("Scalars", "FixedVec", "ListU64", "BitVec", "Nested", "ListC", "BitL")] + \
       [f"{TGT}/prysm.Checkpoint", f"{TGT}/prysm.AttestationData"]
PV1 = "github.com/OffchainLabs/prysm/v7/proto/prysm/v1alpha1"


def try_accept(result, ddir, types, mode, th, work=""):
    """Paths under the work dir are stripped before the reason is cut (byte-reproducible output)."""
    err = io.StringIO()
    cut = lambda s: (s.replace(work + "/", "") if work else s)[:300]
    try:
        with contextlib.redirect_stderr(err):
            got = emit.accept(result, ddir, types, mode, th)
        return {"accepted": True, "n": len(got), "reason": ""}
    except SystemExit as e:
        return {"accepted": False, "n": 0, "reason": cut(str(e))}
    except Exception as e:   # any other exception is an uncontrolled crash, never "refused"
        return {"accepted": None, "n": 0, "reason": cut(f"CRASH {type(e).__name__}: {e}")}


def desc_dir(path, files):
    """A desc dir holding exactly the given files (symlinks with unique names)."""
    if os.path.exists(path):
        shutil.rmtree(path)
    os.makedirs(path)
    for i, f in enumerate(files):
        os.symlink(os.path.realpath(f), f"{path}/{i:03d}-{os.path.basename(f)}")
    return path


def main():
    W, out = sys.argv[1], sys.argv[2]
    th = json.load(open(f"{KRAKEN}/gen/frozen/THEOREMS.json"))
    exp = json.load(open(f"{W}/expect.json"))
    tmp = f"{W}/boundary"
    if os.path.exists(tmp):
        shutil.rmtree(tmp)
    os.makedirs(tmp)
    main_res = f"{W}/main.result.json"
    origs = exp["originals"]
    odir = desc_dir(f"{tmp}/orig", origs)
    inv = json.load(open(f"{KRAKEN}/prysm/inventory.json"))
    prysm_in = [f"{t['package']}.{t['name']}" for t in inv["types"] if t["scope"] == "in"]
    prysm_out = [f"{t['package']}.{t['name']}" for t in inv["types"] if t["scope"] == "out"]
    rows = []

    def case(cid, group, what, want, result, ddir, types, mode, th=th):
        r = try_accept(result, ddir, types, mode, th, W)
        got = {True: "accepted", False: "refused", None: "crash"}[r["accepted"]]
        rows.append({"id": cid, "group": group, "what": what, "expected": want, "actual": got, "reason": r["reason"],
                     "as_expected": got == want})

    # positive and mode controls
    case("p1", "positive", "honest result, originals, 9 hand keys, hand_case", "accepted", main_res, odir, HAND, "hand_case")
    case("p2", "positive", f"honest result, originals, all {len(prysm_in)} in-scope Prysm keys, prysm", "accepted",
         main_res, odir, prysm_in, "prysm")
    for i, k in enumerate(prysm_out):
        case(f"p3-{i}", "positive", f"out-of-scope Prysm key {k} (no frozen-list rows), prysm", "refused", main_res, odir, [k], "prysm")
    # boundary: every wrong hand-type Desc, added and replacing
    for sid, sc in exp["scenarios"].items():
        if sc["source"] != "boundary":
            continue
        files = [l for l in open(sc["list"]).read().split("\n") if l]
        dd = desc_dir(f"{tmp}/b", files)
        res = sc["result"]
        try:
            mk = json.load(open(sc["mutant"]))
            mkey = f"{mk.get('package')}.{mk.get('type')}" if isinstance(mk, dict) else None
        except (OSError, ValueError):
            mkey = None
        # a desc dir with two files of one key is itself refused by emit; that is a refusal too
        case(f"{sid}/hand", "boundary", f"{sc['what']}: hand_case, 9 hand keys", "refused", res, dd, HAND, "hand_case")
        if mkey and isinstance(mkey, str) and not any(mkey.startswith(p + ".") for p in emit.HAND_PACKAGES) and "/" in mkey:
            case(f"{sid}/prysm", "boundary", f"{sc['what']}: prysm, the mutant's own key {mkey}", "refused", res, dd, [mkey], "prysm")
    # forged and extra Desc inputs, rebuilt for the result protocol
    r3 = f"{W}/replay/r3"
    scen_res = lambda sid: exp["scenarios"][sid]["result"]
    if "t12-forge" in exp["scenarios"]:
        case("forged-desc-dir-scenario-result", "forged-input", "forge desc dir (wrong Nested never checked) with the result of scenario t12", "refused",
             scen_res("t12-forge"), f"{r3}/forge/descdir", HAND, "hand_case")
        case("forged-desc-dir-main-result", "forged-input", "forge desc dir with the honest main result", "refused", main_res, f"{r3}/forge/descdir", HAND, "hand_case")
    dd7 = desc_dir(f"{tmp}/t07", origs + [f"{r3}/mut/q01-scalars-under-prysm-v1.desc.json"])
    case("extra-desc-hand-case", "forged-input", "q01 next to the originals (scenario t07), hand_case for v1alpha1.Scalars", "refused",
         scen_res("t07-extra-q01"), dd7, [f"{PV1}.Scalars"], "hand_case")
    case("extra-desc-prysm", "forged-input", "q01 next to the originals (scenario t07), prysm for v1alpha1.Scalars", "refused",
         scen_res("t07-extra-q01"), dd7, [f"{PV1}.Scalars"], "prysm")
    case("extra-desc-unknown-key", "forged-input", "q01 desc dir, honest main result, prysm for v1alpha1.Scalars (unknown key)", "refused",
         main_res, dd7, [f"{PV1}.Scalars"], "prysm")
    case("no-types", "forged-input", "no --types (empty selection)", "refused", main_res, odir, [], "prysm")
    case("hand-and-prysm-checkpoint", "forged-input", "hand Checkpoint and Prysm Checkpoint selected together", "refused",
         main_res, odir, [f"{TGT}/prysm.Checkpoint", f"{PV1}.Checkpoint"], "hand_case")
    case("extra-desc-no-types", "forged-input", "q01 desc dir, scenario t07, no --types", "refused", scen_res("t07-extra-q01"), dd7, [], "prysm")
    dd13 = desc_dir(f"{tmp}/t13", [f"{r3}/mut/q51-log-forge-table-ok.desc.json" if p.endswith("/orig/Scalars.desc.json") else p
                                   for p in origs])
    case("forged-table-ok-string", "forged-input", "scenario t13 (q51 forged TABLE OK string in place of Scalars), hand_case for 8 hand keys", "refused",
         scen_res("t13-forge-table-ok"), dd13, HAND[1:], "hand_case")
    q40 = f"{r3}/mut/q40-number-exp.desc.json"
    dd40 = desc_dir(f"{tmp}/q40", [q40 if p.endswith("/orig/Scalars.desc.json") else p for p in origs])
    case("number-exponent-fixed-size", "forged-input", "q40 (fixed_size 1.6e1) in place of Scalars with the honest result", "refused", main_res, dd40, HAND, "hand_case")
    # own escapes against the new design
    res = json.load(open(main_res))
    def forged(name, fn):
        d = copy.deepcopy(res)
        fn(d)
        p = f"{tmp}/{name}.result.json"
        json.dump(d, open(p, "w"), indent=1)
        return p
    # x01 stale result: a hand Desc changed after the check (same path)
    xdir = f"{tmp}/x01"
    shutil.copytree(f"{W}/orig", xdir)
    nd = json.load(open(f"{xdir}/Nested.desc.json"))
    nd["ssz"]["fields"][2]["fields"][0]["limit"] = 17
    json.dump(nd, open(f"{xdir}/Nested.desc.json", "w"), indent=1)
    case("x01", "own", "a Desc changed after the check, result path differs (copied tree)", "refused", main_res, xdir, HAND, "hand_case")
    # x02 whitespace-only change of a checked file (same JSON, other bytes)
    xdir2 = f"{tmp}/x02"
    shutil.copytree(f"{W}/orig", xdir2)
    open(f"{xdir2}/ListU64.desc.json", "w").write(open(f"{W}/orig/ListU64.desc.json").read() + "\n")
    case("x02", "own", "a checked file re-written with one more newline (same JSON value, other sha256)", "refused",
         main_res, xdir2, HAND, "hand_case")
    # x03 symlink swapped to another file under the checked name
    xdir3 = desc_dir(f"{tmp}/x03", [p for p in origs if not p.endswith("/orig/BitL.desc.json")])
    os.symlink(f"{W}/mut/m-kind-spec.desc.json", f"{xdir3}/999-BitL.desc.json")
    case("x03", "own", "symlink named like BitL pointing at a wrong BitL (control m-kind-spec)", "refused", main_res, xdir3, HAND, "hand_case")
    # x04 extra copy of a key in the desc dir (two files claim ListU64)
    xdir4 = desc_dir(f"{tmp}/x04", origs + [f"{W}/mut/m-limit-spec.desc.json"])
    case("x04", "own", "desc dir with the right ListU64 and a wrong one (same key)", "refused", main_res, xdir4, HAND, "hand_case")
    # x05 mixed results: a scenario result (verdict FAIL) with the honest desc dir
    case("x05", "own", "honest desc dir with a FAIL scenario result (mixed results)", "refused",
         scen_res("s-drop-nested"), odir, HAND, "hand_case")
    # x06 result of another inventory: the sha256 does not match the committed inventory
    case("x06", "own", "result whose inventory sha256 differs from the committed inventory", "refused",
         forged("x06", lambda d: d["inventory"].__setitem__("sha256", "0" * 64)), odir, HAND, "hand_case")
    # x07 result with two original records for one key
    case("x07", "own", "result with a second original record for ListU64", "refused",
         forged("x07", lambda d: d["records"].append(next(r for r in d["records"] if r["role"] == "original" and r["type"] == "ListU64"))),
         odir, HAND, "hand_case")
    # x08 result whose verdict field is duplicated (FAIL then OK) in the raw text
    t = open(main_res).read().replace('"verdict": "OK"', '"verdict": "FAIL",\n "verdict": "OK"', 1)
    open(f"{tmp}/x08.result.json", "w").write(t)
    case("x08", "own", "result text with the key verdict twice (FAIL, OK)", "refused", f"{tmp}/x08.result.json", odir, HAND, "hand_case")
    # x09 bare type name / look-alike in --types
    case("x09", "own", "bare type name ListU64 in --types", "refused", main_res, odir, ["ListU64"], "hand_case")
    case("x10", "own", "type name with U+200B in --types", "refused", main_res, odir, [f"{TGT}.ListU64​"], "hand_case")
    # x11 mode mismatch both ways
    case("x11", "own", "hand key in prysm mode", "refused", main_res, odir, [f"{TGT}.ListU64"], "prysm")
    case("x12", "own", "Prysm key in hand_case mode", "refused", main_res, odir, [f"{PV1}.Checkpoint"], "hand_case")
    # x13 a mutant record does not count: the key of a mutant only (r1 control file for v1alpha1? none) -> use a control path
    xdir13 = desc_dir(f"{tmp}/x13", [p for p in origs if not p.endswith("/orig/ListU64.desc.json")] + [f"{W}/mut/m-limit-spec.desc.json"])
    case("x13", "own", "the wrong ListU64 that the main run checked as a mutant (FAIL record) in place of the original", "refused",
         main_res, xdir13, HAND, "hand_case")
    # x14 exception list: hand Scalars content as the real Prysm Checkpoint replaces that original (run s-y1)
    xdir14 = desc_dir(f"{tmp}/x14", [f"{W}/mut/y1-scalars-as-prysm-checkpoint.desc.json" if p.endswith("/orig/prysm_v1alpha1.Checkpoint.desc.json") else p
                                     for p in origs])
    case("x14", "own", "y1 (Scalars as v1alpha1.Checkpoint) with its run s-y1-replace-prysm-cp, prysm mode", "refused",
         scen_res("s-y1-replace-prysm-cp"), xdir14, [f"{PV1}.Checkpoint"], "prysm")
    case("x15", "own", "same desc dir with the honest main result (sha256 differs)", "refused", main_res, xdir14, [f"{PV1}.Checkpoint"], "prysm")
    # x16 result file with a float in a number field
    t = open(main_res).read().replace('"expected_key_count": 144', '"expected_key_count": 144.0', 1)
    open(f"{tmp}/x16.result.json", "w").write(t)
    case("x16", "own", "result text with expected_key_count 144.0", "refused", f"{tmp}/x16.result.json", odir, HAND, "hand_case")
    # inventory pin, malformed input ends in SystemExit, hashed = parsed bytes
    th_pin = copy.deepcopy(th)
    th_pin["sources_sha256"]["fv/kraken/prysm/inventory.json"] = "0" * 64
    case("x17", "own", "frozen-list inventory pin differs from the committed inventory (result and file agree)", "refused",
         main_res, odir, HAND, "hand_case", th=th_pin)
    xdir18 = f"{tmp}/x18"
    shutil.copytree(f"{W}/orig", xdir18)
    sd = json.load(open(f"{xdir18}/Scalars.desc.json"))
    sd.pop("fixed_size")
    json.dump(sd, open(f"{xdir18}/Scalars.desc.json", "w"), indent=1)
    h18 = hashlib.sha256(open(f"{xdir18}/Scalars.desc.json", "rb").read()).hexdigest()
    def f18(d):
        for r in d["records"]:
            if r["role"] == "original" and r["type"] == "Scalars" and r["package"] == TGT:
                r["sha256"], r["path"] = h18, f"{xdir18}/Scalars.desc.json"
    case("x18", "own", "Scalars without fixed_size, forged record sha256 (only the Desc shape check is left)", "refused",
         forged("x18", f18), xdir18, HAND, "hand_case")
    case("x19", "own", "result whose records list holds a number", "refused",
         forged("x19", lambda d: d["records"].insert(0, 1)), odir, HAND, "hand_case")
    case("x20", "own", "result whose list field is a string", "refused",
         forged("x20", lambda d: d.__setitem__("list", "none")), odir, HAND, "hand_case")
    case("x21", "own", "result whose table_keys holds a string", "refused",
         forged("x21", lambda d: d["table_keys"].append("x")), odir, HAND, "hand_case")
    case("x22", "own", "result whose inventory field is a list", "refused",
         forged("x22", lambda d: d.__setitem__("inventory", [])), odir, HAND, "hand_case")
    xdir23 = f"{tmp}/x23"
    shutil.copytree(f"{W}/orig", xdir23)
    open(f"{xdir23}/ListU64.desc.json", "wb").write(b"\xff\xfe" + open(f"{W}/orig/ListU64.desc.json", "rb").read())
    case("x23", "own", "a Desc with two non-UTF-8 bytes in front", "refused", main_res, xdir23, HAND, "hand_case")
    bad = [r for r in rows if not r["as_expected"]]
    summary = {"cases": len(rows), "as_expected": len(rows) - len(bad),
               "by_group": {g: sum(r["group"] == g for r in rows) for g in sorted({r["group"] for r in rows})},
               "accepted_cases": [r["id"] for r in rows if r["actual"] == "accepted"], "unexpected": [r["id"] for r in bad]}
    strip = lambda s: s.replace(W + "/", "")
    full = json.loads(strip(json.dumps({"schema": "fvphase1c.emit-boundary/1", "summary": summary, "rows": rows})))
    json.dump(full, open(out, "w"), indent=1)
    md = ["# Emit boundary: every case through emit.accept", "", "Generated by `gen/first-generator/test_boundary.py`. Do not edit.", "",
          "```", json.dumps(summary, indent=1), "```", "", "| id | group | expected | actual | reason |", "| --- | --- | --- | --- | --- |"]
    for r in full["rows"]:
        md.append(f"| {r['id']} | {r['group']} | {r['expected']} | {r['actual']} | {r['reason'][:160].replace('|', '/')} |")
    open(out[:-5] + ".md", "w").write("\n".join(md) + "\n")
    print(json.dumps(summary, indent=1))
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
