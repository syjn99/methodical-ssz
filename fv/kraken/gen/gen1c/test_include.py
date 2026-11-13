#!/usr/bin/env python3
"""Cross-check of the include adapter with the real data files and TestTarget.Data.

Usage:
  test_include.py prepare <work-dir>                     Python checks + <work>/IncludeCheck.lean
  test_include.py evaluate <work-dir> <lean-log> <control-log> <out.json>

Python side, per item of the approved API (api_version 2, 22 items):
  - link/out/data/<id>.data exists (adapter file_name), its first directive is `at <label> <offset>`
    of the item (adapter render of the at-line);
  - rodata-string items: the adapter's render of the ELF bytes at (label, offset, length) has the
    same directives as the real file (comments ignored);
  - every item: TestTarget/Data.lean or Runtime/StaticUint64s.lean has the line the adapter's LEAN_INCLUDE gives.
Lean side (IncludeCheck.lean, run in the gate): for every item, the adapter's address term equals
`<id>_addr` by rfl; for rodata strings the ELF bytes equal the adapter's bytes name by rfl.
Control (IncludeControl.lean): the first rodata item with its last byte + 1 and the first address
with offset + 1; both must fail to elaborate.
Python 3 standard library only. Run with python3 -I.
"""
import json
import os
import re
import sys

sys.dont_write_bytecode = True
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import elf as elfmod  # noqa: E402
import include_adapter as inc  # noqa: E402

KRAKEN = os.path.normpath(os.path.join(HERE, "..", ".."))
# namespace of an item that is not in TestTarget/Data.lean
DATA_NS = {"staticuint64s": "Runtime.Data"}
REPO = os.path.normpath(os.path.join(KRAKEN, "..", ".."))


def directives(text):
    return [l.split() for l in text.split("\n") if l.strip() and not l.lstrip().startswith("#")]


def prepare(work):
    os.makedirs(work, exist_ok=True)
    api = inc.check_api()
    e = elfmod.Elf(f"{KRAKEN}/link/out/p1bin-amd64")
    nm = elfmod.read_nm(f"{KRAKEN}/link/out/p1bin-amd64.nm")
    gs_addr, gs_size = elfmod.extent(nm, inc.RODATA_SYMBOL)
    gs = e.read(gs_addr, gs_size)
    data_lean = open(f"{KRAKEN}/lean/TestTarget/Data.lean").read() + open(f"{KRAKEN}/lean/Runtime/StaticUint64s.lean").read()
    rows, lean = [], ["import TestTarget.Data\nimport Runtime.StaticUint64s", "", "open Fk", "", "set_option maxRecDepth 100000", ""]
    for it in api["items"]:
        iid, label, off = it["id"], it["label"], it["offset"]
        path = os.path.join(REPO, inc.DATA_DIR_IN_REPO, inc.file_name(iid))
        r = {"id": iid, "kind": it["kind"], "file": os.path.relpath(path, REPO), "checks": {}}
        ok_file = os.path.exists(path)
        r["checks"]["file exists"] = ok_file
        real = directives(open(path).read()) if ok_file else []
        r["checks"]["at-line = adapter render"] = bool(real) and real[0] == directives(inc.render(iid, label, off))[0]
        r["checks"]["TestTarget/Data.lean or Runtime/StaticUint64s.lean includes it"] = re.search(r"^" + re.escape(inc.LEAN_INCLUDE.format(id=iid)) + r"$",
                                                             data_lean, re.M) is not None
        lean.append(f"example [Host] : {DATA_NS.get(iid, 'TestTarget.Data')}.{iid}_addr = {inc.addr_term(label, off)} := rfl")
        if it["kind"] == "rodata-string":
            bs = gs[off:off + it["length"]]
            r["checks"]["bytes: adapter render of ELF = file"] = directives(inc.render(iid, label, off, bs)) == real
            lean.append(f"example : {inc.bytes_name(iid)} = [{', '.join(str(b) for b in bs)}] := rfl")
        r["ok"] = all(r["checks"].values())
        rows.append(r)
    lean.append('#eval IO.println "INCLUDE-CHECK-END"')
    it = next(i for i in api["items"] if i["kind"] == "rodata-string")
    bs = list(gs[it["offset"]:it["offset"] + it["length"]])
    bs[-1] = (bs[-1] + 1) % 256
    ctl = lean[:6] + [f"example : {inc.bytes_name(it['id'])} = [{', '.join(str(b) for b in bs)}] := rfl",
                      f"example [Host] : {inc.addr_name(it['id'])} = {inc.addr_term(it['label'], it['offset'] + 1)} := rfl"]
    open(f"{work}/IncludeControl.lean", "w").write("\n".join(ctl) + "\n")
    open(f"{work}/IncludeCheck.lean", "w").write("\n".join(lean) + "\n")
    res = {"api_version": api["api_version"], "status": api["status"], "fix3_commit": api["fix3_commit"],
           "items": len(api["items"]), "rows": rows, "python_ok": all(r["ok"] for r in rows),
           "lean_examples": sum(l.startswith("example") for l in lean)}
    json.dump(res, open(f"{work}/prepare.json", "w"), indent=1)
    print(json.dumps({k: v for k, v in res.items() if k != "rows"}))
    return 0 if res["python_ok"] else 1


def evaluate(work, log, ctl_log, out):
    res = json.load(open(f"{work}/prepare.json"))
    txt = open(log).read()
    errs = [l for l in txt.split("\n") if ": error" in l]
    res["lean_errors"] = errs
    res["lean_end_seen"] = "INCLUDE-CHECK-END" in txt
    cerr = [l.replace(work + "/", "") for l in open(ctl_log).read().split("\n") if ": error" in l]
    res["control_errors"] = cerr
    res["all_ok"] = res["python_ok"] and not errs and res["lean_end_seen"] and len(cerr) == 2
    json.dump(res, open(out, "w"), indent=1)
    print(json.dumps({k: v for k, v in res.items() if k != "rows"}))
    return 0 if res["all_ok"] else 1


if __name__ == "__main__":
    if sys.argv[1] == "prepare":
        sys.exit(prepare(sys.argv[2]))
    sys.exit(evaluate(*sys.argv[2:6]))
