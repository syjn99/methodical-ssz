#!/usr/bin/env python3
"""H3 hold-out Go differential of the v1alpha1.BlobIdentifier and v1alpha1.DepositMessage decoders
(Python 3 standard library only; the text of e1diff.py with the H3 cases).

  h3diff.py cases <cases.json>                      write the cases
  h3diff.py check <cases.json> <go-out.json> <result.json>
The Go program is `prysm/go1.26.10/e2e/h3/h3check-main.go.txt`, run natively with Go 1.26.10 through the gate
in a scratch module that replaces the Prysm module by the temporary Prysm tree (read only). This is a
Go-semantics check on the host (linux/arm64), not an execution of the amd64 ELF. Every expected value is
computed here, independently of the code under test, from consensus-specs:
BlobIdentifier = Bytes32 block_root ++ uint64 LE index (40 bytes);
DepositMessage = Bytes48 pubkey ++ Bytes32 withdrawal_credentials ++ uint64 LE amount (88 bytes);
decoding accepts exactly that size. The error identity ssz.ErrSize comes from the Go source. Exit 1 on any
mismatch.
"""
import json
import struct
import sys

VALS = [0, 0x0123456789ABCDEF, 2 ** 64 - 1]


def cases():
    cs = []
    roots = [bytes(32), bytes(range(32)), b"\xff" * 32]
    for i, (v, r) in enumerate(zip(VALS, roots)):
        b = r + struct.pack("<Q", v)
        cs.append({"id": f"bi-accept-{i}", "op": "bi_u", "in": b.hex(),
                   "exp": {"err": "", "u64": v, "bytes": [r.hex()], "lens": [32], "caps": [32]}})
    for n in (0, 39, 41):
        cs.append({"id": f"bi-size-{n}", "op": "bi_u", "in": (b"\x01" * n).hex(), "exp": {"err_is_ErrSize": True}})
    pks = [bytes(48), bytes(range(48)), b"\xff" * 48]
    wcs = [bytes(32), b"\x22" * 32, b"\xff" * 32]
    for i, (v, p, w) in enumerate(zip(VALS, pks, wcs)):
        b = p + w + struct.pack("<Q", v)
        cs.append({"id": f"dm-accept-{i}", "op": "dm_u", "in": b.hex(),
                   "exp": {"err": "", "u64": v, "bytes": [p.hex(), w.hex()], "lens": [48, 32], "caps": [48, 32]}})
    for n in (0, 87, 89):
        cs.append({"id": f"dm-size-{n}", "op": "dm_u", "in": (b"\x01" * n).hex(), "exp": {"err_is_ErrSize": True}})
    return cs


def check(cp, op, rp):
    cs = {c["id"]: c for c in json.load(open(cp))}
    # the memcap wrapper appends one "MEMCAP ..." line to stdout; it is not part of the Go output
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
