#!/usr/bin/env python3
"""Go differential of the v1alpha1.Eth1Data decoder (Python 3 standard library only).

  eth1_data_differential.py cases <cases.json>                      write the cases
  eth1_data_differential.py check <cases.json> <go-out.json> <result.json>
The Go program is the scratch package fve2e/e1check of the temporary Prysm tree (run natively with Go 1.26.10
through the gate; this is a Go-semantics check, not an execution of the amd64 ELF). Every expected value is
computed here, independently of the code under test, from consensus-specs: Eth1Data = Bytes32 deposit_root
++ uint64 LE deposit_count ++ Bytes32 block_hash; decoding accepts exactly 72 bytes. The error identity
ssz.ErrSize comes from the Go source. Exit 1 on any mismatch. (Text of beacon_block_header_differential.py with the Eth1Data cases.)
"""
import json
import struct
import sys

VALS = [0, 0x0123456789ABCDEF, 2 ** 64 - 1]
ROOTS = [(bytes(32), bytes(32)), (bytes(range(32)), b"\x22" * 32), (b"\xff" * 32, b"\xff" * 32)]


def cases():
    cs = []
    for i, (c, (r1, r2)) in enumerate(zip(VALS, ROOTS)):
        b = r1 + struct.pack("<Q", c) + r2
        cs.append({"id": f"e1-accept-{i}", "op": "e1_u", "in": b.hex(),
                   "exp": {"err": "", "count": c, "roots": [r1.hex(), r2.hex()], "lens": [32, 32], "caps": [32, 32]}})
    for n in (0, 71, 73):
        cs.append({"id": f"e1-size-{n}", "op": "e1_u", "in": (b"\x01" * n).hex(), "exp": {"err_is_ErrSize": True}})
    return cs


def check(cp, op, rp):
    cs = {c["id"]: c for c in json.load(open(cp))}
    # the memory_limit.py wrapper appends one "MEMCAP ..." line to stdout; it is not part of the Go output
    txt = "".join(l for l in open(op) if not l.startswith("MEMCAP "))
    got = {r["id"]: r for r in json.loads(txt)}
    rows, bad = [], 0
    for i, c in cs.items():
        g, ok = got.get(i), True
        if g is None:
            ok = False
        else:
            for k, v in c["exp"].items():
                ok &= g.get(k) == v
        bad += not ok
        rows.append({"id": i, "ok": ok})
    res = {"cases": len(cs), "match": len(cs) - bad, "mismatch": bad, "rows": rows}
    json.dump(res, open(rp, "w"), indent=1)
    print(json.dumps({k: res[k] for k in ("cases", "match", "mismatch")}))
    return 1 if bad else 0


if __name__ == "__main__":
    if sys.argv[1] == "cases":
        json.dump(cases(), open(sys.argv[2], "w"), indent=1)
        sys.exit(0)
    if sys.argv[1] == "check":
        sys.exit(check(*sys.argv[2:5]))
    sys.exit(2)
