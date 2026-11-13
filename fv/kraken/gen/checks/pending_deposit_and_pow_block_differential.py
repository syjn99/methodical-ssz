#!/usr/bin/env python3
"""Hold-out of PendingDeposit and PowBlock Go differential of the v1alpha1.PendingDeposit and v1alpha1.PowBlock decoders
(Python 3 standard library only; the text of pending_consolidation_and_sync_committee_message_differential.py with the hold-out cases).

  pending_deposit_and_pow_block_differential.py cases <cases.json>                      write the cases
  pending_deposit_and_pow_block_differential.py check <cases.json> <go-out.json> <result.json>
The Go program is `prysm/go1.26.10/evidence/pending-deposit-and-pow-block/differential-main.go.txt`, run natively with Go 1.26.10 through the gate
with `go run -overlay` in the temporary Prysm tree (read only). This is a Go-semantics check on the host
(linux/arm64), not an execution of the amd64 ELF. Every expected value is computed here, independently of the
code under test, from consensus-specs:
PendingDeposit = Bytes48 pubkey ++ Bytes32 withdrawal_credentials ++ uint64 LE amount ++ Bytes96 signature
++ uint64 LE slot (192 bytes); PowBlock = Hash32 block_hash ++ Hash32 parent_hash ++ uint256 LE total_difficulty
(96 bytes; Prysm keeps the 32 bytes as they are); decoding accepts exactly that size. The error identity
ssz.ErrSize comes from the Go source. Exit 1 on any mismatch.
"""
import json
import struct
import sys

VALS = [0, 0x0123456789ABCDEF, 2 ** 64 - 1]


def cases():
    cs = []
    pks = [bytes(48), bytes(range(48)), b"\xff" * 48]
    wcs = [bytes(32), b"\x22" * 32, b"\xff" * 32]
    sigs = [bytes(96), bytes(range(100, 196)), b"\xff" * 96]
    slots = [0, 7, 2 ** 64 - 1]
    for i, (pk, wc, a, g, sl) in enumerate(zip(pks, wcs, VALS, sigs, slots)):
        b = pk + wc + struct.pack("<Q", a) + g + struct.pack("<Q", sl)
        cs.append({"id": f"pending-deposit-accept-{i}", "op": "PendingDeposit.UnmarshalSSZ", "in": b.hex(),
                   "exp": {"err": "", "u64s": [a, sl], "bytes": [pk.hex(), wc.hex(), g.hex()],
                           "lens": [48, 32, 96], "caps": [48, 32, 96]}})
    for n in (0, 191, 193):
        cs.append({"id": f"pending-deposit-size-{n}", "op": "PendingDeposit.UnmarshalSSZ", "in": (b"\x01" * n).hex(), "exp": {"err_is_ErrSize": True}})
    tds = [0, 2 ** 255 + 12345, 2 ** 256 - 1]
    for i, td in enumerate(tds):
        bh, ph = bytes(range(i, 32 + i)), bytes(range(200, 232))
        t = td.to_bytes(32, "little")
        b = bh + ph + t
        cs.append({"id": f"pow-block-accept-{i}", "op": "PowBlock.UnmarshalSSZ", "in": b.hex(),
                   "exp": {"err": "", "bytes": [bh.hex(), ph.hex(), t.hex()], "lens": [32, 32, 32],
                           "caps": [32, 32, 32]}})
    for n in (0, 95, 97):
        cs.append({"id": f"pow-block-size-{n}", "op": "PowBlock.UnmarshalSSZ", "in": (b"\x01" * n).hex(), "exp": {"err_is_ErrSize": True}})
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
