#!/usr/bin/env python3
"""Go differential of the BeaconBlockHeader ENCODER (Python 3 standard library only).

  beacon_block_header_encoder_differential.py cases <cases.json>                      write the cases
  beacon_block_header_encoder_differential.py check <cases.json> <go-out.json> <result.json>
The Go program is `prysm/go1.26.10/evidence/beacon-block-header/differential-encoder-main.go.txt`, run natively with Go 1.26.10 through the gate as
a scratch package of the temporary Prysm tree (by `go run -overlay`; nothing is written into that tree).
This is a Go-semantics check, not an execution of the amd64 ELF. Every expected value is computed here,
independently of the code under test, from consensus-specs: serialize(BeaconBlockHeader) = uint64 LE slot ++
uint64 LE proposer_index ++ parent_root ++ state_root ++ body_root (three Bytes32); MarshalSSZTo(dst) returns
dst ++ serialize. Case groups:
  fast-*   len(dst) + 112 <= cap(dst): the path of `Prysm.BeaconBlockHeader.Encode.fast_path`. Also expected: nil error, the result
           shares the backing array of dst (no growslice), cap unchanged, receiver unchanged.
  grow-*   nil or short dst (runtime.growslice): NOT the proved path; checked for the bytes only.
  rej-*    one root of length 31 or 33 (ssz.ErrBytesLength, nil slice): NOT the proved path.
Exit 1 on any mismatch.
"""
import json
import struct
import sys

VALS = [(0, 0), (0x0123456789ABCDEF, 7), (2 ** 64 - 1, 2 ** 64 - 1)]
ROOTS = [(bytes(32), bytes(32), bytes(32)), (bytes(range(32)), b"\x11" * 32, b"\x22" * 32),
         (b"\xff" * 32, b"\xff" * 32, b"\xff" * 32)]
PRE = [(b"", 0), (b"\xaa\xbb\xcc", 5), (bytes(range(1, 41)), 0)]


def ser(s, p, rs):
    return struct.pack("<QQ", s, p) + b"".join(rs)


def cases():
    cs = []
    for i, ((s, p), rs) in enumerate(zip(VALS, ROOTS)):
        for j, (pre, spare) in enumerate(PRE):
            cs.append({"id": f"fast-{i}-{j}", "slot": s, "proposer": p, "roots": [r.hex() for r in rs],
                       "pre": pre.hex(), "cap": len(pre) + 112 + spare, "nil_dst": False,
                       "exp": {"err": "", "out": (pre + ser(s, p, rs)).hex(), "same_array": True,
                               "out_cap": len(pre) + 112 + spare, "recv_unchanged": True}})
        cs.append({"id": f"grow-nil-{i}", "slot": s, "proposer": p, "roots": [r.hex() for r in rs],
                   "pre": "", "cap": 0, "nil_dst": True,
                   "exp": {"err": "", "out": ser(s, p, rs).hex(), "recv_unchanged": True}})
        cs.append({"id": f"grow-short-{i}", "slot": s, "proposer": p, "roots": [r.hex() for r in rs],
                   "pre": "aabbcc", "cap": 3 + 111, "nil_dst": False,
                   "exp": {"err": "", "out": (b"\xaa\xbb\xcc" + ser(s, p, rs)).hex(), "recv_unchanged": True}})
    (s, p), rs = VALS[1], ROOTS[1]
    for k in range(3):
        for n in (31, 33):
            r2 = list(rs)
            r2[k] = b"\x33" * n
            cs.append({"id": f"rej-root{k}-len{n}", "slot": s, "proposer": p, "roots": [r.hex() for r in r2],
                       "pre": "", "cap": 200, "nil_dst": False,
                       "exp": {"err_is_ErrBytesLength": True, "out_nil": True, "recv_unchanged": True}})
    return cs


def check(cp, op, rp):
    cs = {c["id"]: c for c in json.load(open(cp))}
    # the memory_limit.py wrapper appends one "MEMCAP ..." line to stdout; it is not part of the Go output
    txt = "".join(l for l in open(op) if not l.startswith("MEMCAP "))
    got = {r["id"]: r for r in json.loads(txt)}
    rows, bad = [], 0
    for i, c in cs.items():
        g = got.get(i)
        ok = g is not None and all(g.get(k) == v for k, v in c["exp"].items())
        bad += not ok
        rows.append({"id": i, "ok": ok})
    groups = {}
    for r in rows:
        g = r["id"].split("-")[0]
        groups.setdefault(g, [0, 0])
        groups[g][0] += 1
        groups[g][1] += r["ok"]
    res = {"cases": len(cs), "match": len(cs) - bad, "mismatch": bad,
           "groups": {g: {"cases": a, "match": b} for g, (a, b) in groups.items()},
           "proved_path_group": "fast", "rows": rows}
    json.dump(res, open(rp, "w"), indent=1)
    print(json.dumps({k: res[k] for k in ("cases", "match", "mismatch", "groups")}))
    return 1 if bad else 0


if __name__ == "__main__":
    if len(sys.argv) == 3 and sys.argv[1] == "cases":
        json.dump(cases(), open(sys.argv[2], "w"), indent=1)
    elif len(sys.argv) == 5 and sys.argv[1] == "check":
        sys.exit(check(*sys.argv[2:]))
    else:
        sys.exit(__doc__)
