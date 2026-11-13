#!/usr/bin/env python3
"""Hold-out of Deposit_Data and PendingPartialWithdrawal Go differential of the v1alpha1.Deposit_Data and v1alpha1.PendingPartialWithdrawal decoders
(Python 3 standard library only; the text of blob_identifier_and_deposit_message_differential.py with the hold-out cases).

  deposit_data_and_pending_partial_withdrawal_differential.py cases <cases.json>                      write the cases
  deposit_data_and_pending_partial_withdrawal_differential.py check <cases.json> <go-out.json> <result.json>
The Go program is `prysm/go1.26.10/evidence/deposit-data-and-pending-partial-withdrawal/h4check-main.go.txt`, run natively with Go 1.26.10 through the gate
with `go run -overlay` in the temporary Prysm tree (read only). This is a Go-semantics check on the host
(linux/arm64), not an execution of the amd64 ELF. Every expected value is computed here, independently of the
code under test, from consensus-specs:
DepositData = Bytes48 pubkey ++ Bytes32 withdrawal_credentials ++ uint64 LE amount ++ Bytes96 signature (184 bytes);
PendingPartialWithdrawal = uint64 LE validator_index ++ uint64 LE amount ++ uint64 LE withdrawable_epoch (24 bytes);
decoding accepts exactly that size. The error identity ssz.ErrSize comes from the Go source. Exit 1 on any
mismatch.
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
    for i, (v, p, w, g) in enumerate(zip(VALS, pks, wcs, sigs)):
        b = p + w + struct.pack("<Q", v) + g
        cs.append({"id": f"dd-accept-{i}", "op": "dd_u", "in": b.hex(),
                   "exp": {"err": "", "u64s": [v], "bytes": [p.hex(), w.hex(), g.hex()], "lens": [48, 32, 96],
                           "caps": [48, 32, 96]}})
    for n in (0, 183, 185):
        cs.append({"id": f"dd-size-{n}", "op": "dd_u", "in": (b"\x01" * n).hex(), "exp": {"err_is_ErrSize": True}})
    trip = [(0, 0, 0), (0x0123456789ABCDEF, 32000000000, 0xFEDCBA9876543210), (2 ** 64 - 1, 2 ** 64 - 1, 2 ** 64 - 1)]
    for i, (x, y, z) in enumerate(trip):
        b = struct.pack("<QQQ", x, y, z)
        cs.append({"id": f"pw-accept-{i}", "op": "pw_u", "in": b.hex(), "exp": {"err": "", "u64s": [x, y, z]}})
    for n in (0, 23, 25):
        cs.append({"id": f"pw-size-{n}", "op": "pw_u", "in": (b"\x01" * n).hex(), "exp": {"err_is_ErrSize": True}})
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
