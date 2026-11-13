#!/usr/bin/env python3
"""Go differential of the BeaconBlockHeader hold-out (BeaconBlockHeader, ValidatorIndex) (Python 3 standard library only).

  beacon_block_header_differential.py cases <cases.json>                      write the cases
  beacon_block_header_differential.py check <cases.json> <go-out.json> <result.json>
The Go program is `prysm/go1.26.10/evidence/beacon-block-header/differential-main.go.txt`, built as a scratch package of the
temporary Prysm tree (run natively with Go 1.26.10
through the gate; this is a Go-semantics check, not an execution of the amd64 ELF). Every expected value is
computed here, independently of the code under test, from consensus-specs: BeaconBlockHeader = uint64 LE slot
++ uint64 LE proposer_index ++ three Bytes32; decoding accepts exactly 112 bytes; ValidatorIndex = uint64 LE,
exactly 8 bytes. The error identity ssz.ErrSize comes from the Go source. Exit 1 on any mismatch.
"""
import json
import struct
import sys

VALS = [(0, 0), (0x0123456789ABCDEF, 7), (2 ** 64 - 1, 2 ** 64 - 1)]
ROOTS = [(bytes(32), bytes(32), bytes(32)), (bytes(range(32)), b"\x11" * 32, b"\x22" * 32),
         (b"\xff" * 32, b"\xff" * 32, b"\xff" * 32)]


def cases():
    cs = []
    for i, ((s, p), rs) in enumerate(zip(VALS, ROOTS)):
        b = struct.pack("<QQ", s, p) + b"".join(rs)
        cs.append({"id": f"beacon-block-header-accept-{i}", "op": "BeaconBlockHeader.UnmarshalSSZ", "in": b.hex(),
                   "exp": {"err": "", "slot": s, "proposer": p, "roots": [r.hex() for r in rs],
                           "lens": [32] * 3, "caps": [32] * 3}})
    for n in (0, 111, 113):
        cs.append({"id": f"beacon-block-header-size-{n}", "op": "BeaconBlockHeader.UnmarshalSSZ", "in": (b"\x01" * n).hex(), "exp": {"err_is_ErrSize": True}})
    for i, (v, _) in enumerate(VALS):
        cs.append({"id": f"validator-index-accept-{i}", "op": "ValidatorIndex.UnmarshalSSZ", "in": struct.pack("<Q", v).hex(), "exp": {"err": "", "vi": v}})
    for n in (0, 7, 9):
        cs.append({"id": f"validator-index-len-{n}", "op": "ValidatorIndex.UnmarshalSSZ", "in": (b"\x01" * n).hex(), "exp": {"err_nonempty": True}})
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
                if k == "err_nonempty":
                    ok &= g["err"] != ""
                else:
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
