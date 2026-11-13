#!/usr/bin/env python3
"""Go differential of the capacity-reserving generator option: old (698c202) vs new (reserve) Checkpoint.MarshalSSZTo (Python 3 stdlib only).

  checkpoint_marshal_differential.py cases <cases.json>
  checkpoint_marshal_differential.py check <cases.json> <old.json> <new.json> <result.json>
The Go program is differential-main.go.txt, built twice in the temporary Prysm tree (old and new phase0 files,
identical flags) and run natively on linux/arm64 with Go 1.26.10. It checks Go semantics, not the amd64 ELF.
Expected values are computed here, independently of the code under test:
 - returned value (contract items 1-2): ok -> prefix ++ struct.pack('<Q', epoch) ++ root; len(root) != 32 ->
   (nil, ssz.ErrBytesLength); old and new must agree byte for byte.
 - caller's backing array and allocations (written before the change):
   old: valid root writes [L, L+8) when 8 <= spare < 40 and [L, L+40) when spare >= 40; invalid root writes
   [L, L+8) when spare >= 8 (the epoch is written before the root length test); 0 allocations when nothing grows.
   new: [L, L+40) (valid) or [L, L+8) (invalid) only when spare >= 40, else the caller's array is unchanged;
   allocations 0 when spare >= 40, else exactly 1.
 - receiver and root unchanged; a nil receiver panics in both (the panic text must be equal).
Old allocation counts for spare < 40 (valid) are recorded, not asserted (1 or 2 by Go's growth rule).
Exit 1 on any mismatch.
"""
import json
import struct
import sys

PREFIX_30_BYTES = bytes(range(0x40, 0x40 + 30))
FILL = 0xEE
ROOT = bytes(range(32))


def cases():
    cs = []
    for pn, pre in (("empty", b""), ("pre30", PREFIX_30_BYTES)):
        for sp in (0, 7, 8, 39, 40, 41):
            cs.append({"id": f"{pn}-spare{sp}-valid", "epoch": 0x0123456789ABCDEF, "root": ROOT.hex(), "prefix": pre.hex(),
                       "spare": sp, "fill": FILL})
            cs.append({"id": f"{pn}-spare{sp}-root31", "epoch": 7, "root": (b"\x22" * 31).hex(), "prefix": pre.hex(),
                       "spare": sp, "fill": FILL})
    for rl in (0, 33):
        cs.append({"id": f"empty-spare16-root{rl}", "epoch": 7, "root": (b"\x22" * rl).hex(), "prefix": "", "spare": 16,
                   "fill": FILL})
    cs.append({"id": "nil-dst-valid", "epoch": 9, "root": ROOT.hex(), "prefix": "", "spare": -1, "fill": FILL})
    cs.append({"id": "nil-dst-root31", "epoch": 9, "root": (b"\x22" * 31).hex(), "prefix": "", "spare": -1, "fill": FILL})
    cs.append({"id": "pre30-spare1000-valid", "epoch": 2 ** 64 - 1, "root": (b"\xff" * 32).hex(), "prefix": PREFIX_30_BYTES.hex(),
               "spare": 1000, "fill": FILL})
    for sp in (0, 40):
        cs.append({"id": f"nilrecv-spare{sp}", "epoch": 0, "root": "", "prefix": "", "spare": sp, "fill": FILL,
                   "nil_recv": True})
    return cs


def expect(c, new):
    pre = bytes.fromhex(c["prefix"])
    root = bytes.fromhex(c["root"])
    sp = max(c["spare"], 0)
    L = len(pre)
    ok = len(root) == 32
    le = struct.pack("<Q", c["epoch"])
    orig = pre + bytes([c["fill"]]) * sp
    if ok:
        w = 40 if sp >= 40 else (8 if (not new and sp >= 8) else 0)
        written = (le + root)[:w]
    else:
        w = 8 if (sp >= 40 or (not new and sp >= 8)) else 0
        written = le[:w]
    backing = pre + written + orig[L + len(written):]
    e = {"ok": ok, "out": (pre + le + root).hex() if ok else "", "out_nil": not ok, "backing": backing.hex()}
    if ok and sp >= 40:
        e.update(aliases=True, out_cap=L + sp, allocs=0)
    elif ok:
        e.update(aliases=False)
        if new:
            e["allocs"] = 1
    else:
        e["allocs"] = 0 if (sp >= 40 or (not new and sp >= 8)) else 1
    return e


def match(g, x):
    bad = []
    if g["panic"]:
        return ["panic: " + g["panic"]]
    if (g["err"] == "") != x["ok"]:
        bad.append("err")
    if not x["ok"] and not (g["err_is_ErrBytesLength"] and g["err_is_the_ErrBytesLength_value"]):
        bad.append("err identity")
    for k in ("out", "out_nil", "backing"):
        if g[k if k != "out_nil" else "out_nil"] != x[k]:
            bad.append(k)
    if "aliases" in x and g["out_aliases_dst"] != x["aliases"]:
        bad.append("aliases")
    if "out_cap" in x and g["out_cap"] != x["out_cap"]:
        bad.append("out_cap")
    if "allocs" in x and g["allocs"] != x["allocs"]:
        bad.append("allocs")
    if not g["recv_unchanged"]:
        bad.append("recv")
    return bad


def check(cp, op, np, rp):
    cs = json.load(open(cp))
    old = {r["id"]: r for r in json.load(open(op))}
    new = {r["id"]: r for r in json.load(open(np))}
    rows, bad = [], 0
    for c in cs:
        o, n = old[c["id"]], new[c["id"]]
        row = {"id": c["id"], "spare": c["spare"], "prefix_len": len(c["prefix"]) // 2, "root_len": len(c["root"]) // 2}
        if c.get("nil_recv"):
            row["panic_old"], row["panic_new"] = o["panic"], n["panic"]
            row["mismatch"] = [] if (o["panic"] and o["panic"] == n["panic"]) else ["nil receiver: panics differ or none"]
        else:
            row["mismatch_old"] = match(o, expect(c, False))
            row["mismatch_new"] = match(n, expect(c, True))
            same = [k for k in ("err", "out", "out_nil", "out_len") if o[k] != n[k]]
            row["returned_identical_old_new"] = not same
            row["mismatch"] = row["mismatch_old"] + row["mismatch_new"] + (["returned value differs: " + ",".join(same)] if same else [])
            row["allocs_old"], row["allocs_new"] = o["allocs"], n["allocs"]
            row["out_cap_old"], row["out_cap_new"] = o["out_cap"], n["out_cap"]
            row["caller_written_old"] = o["backing"] != (bytes.fromhex(c["prefix"]) + bytes([c["fill"]]) * max(c["spare"], 0)).hex()
            row["caller_written_new"] = n["backing"] != (bytes.fromhex(c["prefix"]) + bytes([c["fill"]]) * max(c["spare"], 0)).hex()
        bad += bool(row["mismatch"])
        rows.append(row)
    res = {"go": "go1.26.10 linux/arm64 (native; Go semantics, not the amd64 ELF)", "cases": len(rows),
           "mismatches": bad, "rows": rows}
    json.dump(res, open(rp, "w"), indent=1)
    print(json.dumps({"cases": len(rows), "mismatches": bad}))
    return 1 if bad else 0


if __name__ == "__main__":
    if sys.argv[1] == "cases":
        json.dump(cases(), open(sys.argv[2], "w"), indent=1)
        print(len(cases()))
    else:
        sys.exit(check(*sys.argv[2:6]))
