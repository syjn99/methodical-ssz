#!/usr/bin/env python3
"""prysm-e2e E6 Go differential check (Python 3 standard library only).

  differential.py cases <cases.json>                write the cases
  differential.py check <cases.json> <go-out.json> <result.json>
The Go program is the scratch package fve2e/cpcheck of the temporary Prysm tree (run natively with
Go 1.26.10 through the gate). Every expected value is computed here, independently of the code under
test: encoding = struct.pack('<Q', epoch) + root (consensus-specs uint64 little endian ++ Bytes32);
decoding accepts exactly 40 bytes; the error identities come from the Go source (ssz.ErrSize,
ssz.ErrBytesLength). Exit 1 on any mismatch.
"""
import json
import struct
import sys

EPOCHS = [0, 0x0123456789ABCDEF, 2 ** 64 - 1]
ROOTS = {"zero": bytes(32), "pattern": bytes(range(32)), "ff": b"\xff" * 32}


def enc(e, r):
    return struct.pack("<Q", e) + r


def cases():
    cs = []
    for e in EPOCHS:
        for rn, r in ROOTS.items():
            b = enc(e, r)
            cs.append({"id": f"dec-{e:x}-{rn}", "op": "unmarshal", "in": b.hex(), "exp": {"ok": True, "epoch": e, "root": r.hex()}})
            cs.append({"id": f"enc-empty-cap40-{e:x}-{rn}", "op": "marshal", "epoch": e, "root": r.hex(), "prefix": "", "spare": 40,
                       "exp": {"ok": True, "out": b.hex(), "path": "fast (cap = len + 40)"}})
            cs.append({"id": f"enc-prefix3-spare45-{e:x}-{rn}", "op": "marshal", "epoch": e, "root": r.hex(), "prefix": "aabbcc",
                       "spare": 45, "exp": {"ok": True, "out": "aabbcc" + b.hex(), "path": "fast (cap > len + 40)"}})
            cs.append({"id": f"roundtrip-{e:x}-{rn}", "op": "roundtrip", "in": b.hex(), "exp": {"ok": True, "out": b.hex()}})
    for n in (0, 39, 41, 80):
        cs.append({"id": f"dec-len{n}", "op": "unmarshal", "in": (b"\x11" * n).hex(), "sentinel": True,
                   "exp": {"ok": False, "ErrSize": True, "not_ErrBytesLength": True, "recv_unchanged": True}})
    for n in (0, 31, 33):
        cs.append({"id": f"enc-rootlen{n}", "op": "marshal", "epoch": 7, "root": (b"\x22" * n).hex(), "prefix": "", "spare": 48,
                   "exp": {"ok": False, "ErrBytesLength": True, "not_ErrSize": True, "out_nil": True,
                           # C-1: the 8 epoch bytes are already in the caller's spare capacity
                           "backing": (struct.pack("<Q", 7) + bytes(40)).hex()}})
    cs.append({"id": "enc-grow-cap0", "op": "marshal", "epoch": 5, "root": bytes(range(32)).hex(), "prefix": "", "spare": 0,
               "exp": {"ok": True, "out": enc(5, bytes(range(32))).hex(), "path": "growslice"}})
    # the growslice witness shape of cp_e2e_marshal_grow_main: len 30, cap 36
    pre30 = bytes(range(0x40, 0x40 + 30))
    cs.append({"id": "enc-grow-len30-cap36", "op": "marshal", "epoch": 0x0123456789ABCDEF, "root": (b"\xff" * 32).hex(),
               "prefix": pre30.hex(), "spare": 6,
               "exp": {"ok": True, "out": (pre30 + enc(0x0123456789ABCDEF, b"\xff" * 32)).hex(), "path": "growslice"}})
    # INBOX 009: every capacity range of the encoder (prefix 30 bytes, cap = 30 + spare) and the reject after growth
    rp = bytes(range(32))
    for sp, path in ((0, "cap = len: growslice, then (real Go: 64 < 70) a second growslice"),
                     (3, "cap < len + 8: growslice, then a second growslice"),
                     (8, "cap = len + 8: first fits, second grows"), (20, "first fits, second grows"),
                     (39, "cap = len + 39: first fits, second grows"), (40, "fast (cap = len + 40)")):
        cs.append({"id": f"enc-w-len30-spare{sp}", "op": "marshal", "epoch": 9, "root": rp.hex(), "prefix": pre30.hex(),
                   "spare": sp, "exp": {"ok": True, "out": (pre30 + enc(9, rp)).hex(), "path": path}})
    pre10 = bytes(range(0x60, 0x60 + 10))
    cs.append({"id": "enc-w-len10-spare0", "op": "marshal", "epoch": 9, "root": rp.hex(), "prefix": pre10.hex(), "spare": 0,
               "exp": {"ok": True, "out": (pre10 + enc(9, rp)).hex(), "path": "cap = len: growslice x2"}})
    for sp, rl in ((0, 31), (3, 33), (0, 0)):
        cs.append({"id": f"enc-w-rej-len30-spare{sp}-rootlen{rl}", "op": "marshal", "epoch": 7, "root": (b"\x22" * rl).hex(),
                   "prefix": pre30.hex(), "spare": sp,
                   "exp": {"ok": False, "ErrBytesLength": True, "not_ErrSize": True, "out_nil": True,
                           # cap < len + 8: the epoch bytes go to the growslice block; the caller's array is unchanged
                           "backing": (pre30 + bytes(sp)).hex()}})
    cs.append({"id": "enc-w-rej-len30-spare8-rootlen33", "op": "marshal", "epoch": 7, "root": (b"\x22" * 33).hex(),
               "prefix": pre30.hex(), "spare": 8,
               "exp": {"ok": False, "ErrBytesLength": True, "not_ErrSize": True, "out_nil": True,
                       "backing": (pre30 + struct.pack("<Q", 7)).hex()}})
    for n in (7, 9):
        cs.append({"id": f"epoch-len{n}", "op": "epoch_unmarshal", "in": (b"\x01" * n).hex(),
                   "exp": {"ok": False, "err_text": f"expected buffer of length 8 received {n}", "epoch": 0x77}})
    cs.append({"id": "epoch-len8", "op": "epoch_unmarshal", "in": struct.pack("<Q", 0x0102030405060708).hex(),
               "exp": {"ok": True, "epoch": 0x0102030405060708}})
    return cs


def check(cases_path, out_path, res_path):
    cs = {c["id"]: c for c in json.load(open(cases_path))}
    got = {r["id"]: r for r in json.load(open(out_path))}
    rows, bad = [], 0
    for i, c in cs.items():
        g, x = got.get(i), c["exp"]
        ok = g is not None
        if ok:
            ok &= (g["err"] == "") == x["ok"]
            if "epoch" in x:
                ok &= g["epoch"] == x["epoch"]
            if "root" in x:
                ok &= g["root"] == x["root"] and g["root_len"] == 32 and g["root_cap"] == 32
            if "out" in x:
                ok &= g["out"] == x["out"]
            if x.get("ErrSize"):
                ok &= g["err_is_ErrSize"]
            if x.get("not_ErrBytesLength"):
                ok &= not g["err_is_ErrBytesLength"]
            if x.get("not_ErrSize"):
                ok &= not g["err_is_ErrSize"]
            if x.get("recv_unchanged"):
                ok &= g["recv_unchanged"]
            if "backing" in x:
                ok &= g["backing"] == x["backing"]
            if "err_text" in x:
                ok &= g["err"] == x["err_text"]
            if x.get("ErrBytesLength"):
                ok &= g["err_is_ErrBytesLength"] and g["out_nil"] == x["out_nil"]
        bad += not ok
        rows.append({"id": i, "op": c["op"], "expected": x, "observed": g, "match": ok})
    res = {"go": "go1.26.10 linux/arm64 (native)", "cases": len(rows), "mismatches": bad, "rows": rows,
           "oracle": "struct.pack('<Q', epoch) + root; 40-byte acceptance; ErrSize / ErrBytesLength identities (and not the other); "
                     "decoder reject leaves a sentinel receiver unchanged; encoder reject leaves LE(epoch) in the caller's backing "
                     "array (C-1); Epoch reject error text and receiver unchanged"}
    json.dump(res, open(res_path, "w"), indent=1)
    print(json.dumps({"cases": len(rows), "mismatches": bad}))
    return 1 if bad else 0


if __name__ == "__main__":
    if sys.argv[1] == "cases":
        json.dump(cases(), open(sys.argv[2], "w"), indent=1)
        print(len(cases()))
    else:
        sys.exit(check(*sys.argv[2:5]))
