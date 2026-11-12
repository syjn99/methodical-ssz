#!/usr/bin/env python3
"""E2-C Go differential of the 16 flat development ENCODERS, fast path (Python 3 standard library only).

  e2cdiff.py cases <cases.json>                      write the cases
  e2cdiff.py check <cases.json> <go-out.json> <result.json>
The Go program is `prysm/go1.26.10/e2e/scal/e2c/e2ccheck-main.go.txt`, run natively with Go 1.26.10 through the
gate as package fve2e/e2ccheck of the temporary Prysm tree (by `go run -overlay`; nothing is written into that
tree). This is a Go-semantics check on the host (linux/arm64), not an execution of the amd64 ELF.
Every expected value is computed here, independently of the code under test, from the consensus-specs field
lists (ValidatorBalance: Prysm proto; no consensus-specs container): uint64 fields = 8 bytes little endian, byte
vectors = their bytes, PowBlock total_difficulty = uint256 little endian (32 bytes). MarshalSSZTo(dst) returns
dst ++ serialize. Only the fast path of the generated theorems is exercised: len(dst) + size <= cap(dst), every
byte field of its exact length; prefix lengths 0 and 7, capacity exact and with 5 spare bytes. Also expected:
nil error, the result shares the backing array of dst (no growslice), cap unchanged, receiver unchanged.
Exit 1 on any mismatch.
"""
import json
import struct
import sys

# Go type -> [(Go field, kind, SSZ size)] in SSZ order (consensus-specs field order).
TYPES = {
    "Checkpoint": [("Epoch", "u", 8), ("Root", "b", 32)],
    "BeaconBlockHeader": [("Slot", "u", 8), ("ProposerIndex", "u", 8), ("ParentRoot", "b", 32),
                          ("StateRoot", "b", 32), ("BodyRoot", "b", 32)],
    "Eth1Data": [("DepositRoot", "b", 32), ("DepositCount", "u", 8), ("BlockHash", "b", 32)],
    "BlobIdentifier": [("BlockRoot", "b", 32), ("Index", "u", 8)],
    "DepositMessage": [("PublicKey", "b", 48), ("WithdrawalCredentials", "b", 32), ("Amount", "u", 8)],
    "Deposit_Data": [("PublicKey", "b", 48), ("WithdrawalCredentials", "b", 32), ("Amount", "u", 8),
                     ("Signature", "b", 96)],
    "PendingPartialWithdrawal": [("Index", "u", 8), ("Amount", "u", 8), ("WithdrawableEpoch", "u", 8)],
    "SyncCommitteeMessage": [("Slot", "u", 8), ("BlockRoot", "b", 32), ("ValidatorIndex", "u", 8),
                             ("Signature", "b", 96)],
    "PendingConsolidation": [("SourceIndex", "u", 8), ("TargetIndex", "u", 8)],
    "PendingDeposit": [("PublicKey", "b", 48), ("WithdrawalCredentials", "b", 32), ("Amount", "u", 8),
                       ("Signature", "b", 96), ("Slot", "u", 8)],
    "PowBlock": [("BlockHash", "b", 32), ("ParentHash", "b", 32), ("TotalDifficulty", "n", 32)],
    "HistoricalSummary": [("BlockSummaryRoot", "b", 32), ("StateSummaryRoot", "b", 32)],
    "SigningData": [("ObjectRoot", "b", 32), ("Domain", "b", 32)],
    "SyncAggregatorSelectionData": [("Slot", "u", 8), ("SubcommitteeIndex", "u", 8)],
    "ValidatorBalance": [("Index", "u", 8), ("Balance", "u", 8)],
    "VoluntaryExit": [("Epoch", "u", 8), ("ValidatorIndex", "u", 8)],
}
U64 = [0, 0x0123456789ABCDEF, 2 ** 64 - 1, 7]
DST = [(0, 0), (0, 5), (7, 0), (7, 5)]   # (prefix length, spare capacity)


def values(fields, v):
    out = []
    for i, (name, k, n) in enumerate(fields):
        if k == "u":
            out.append((name, k, U64[(v + i) % 4] if v else 0))
        elif k == "b":
            out.append((name, k, bytes(n) if not v else bytes(((j * 7 + i + v) & 0xFF) for j in range(n))))
        else:  # uint256 number; the Go field holds its 32 little-endian bytes
            out.append((name, k, 0 if not v else (2 ** 256 - 1 if v == 2 else 0x0123456789ABCDEF << 100)))
    return out


def ser(vals):
    b = b""
    for _, k, x in vals:
        b += struct.pack("<Q", x) if k == "u" else (x if k == "b" else x.to_bytes(32, "little"))
    return b


def cases():
    cs = []
    for t, fields in TYPES.items():
        size = sum(n for _, _, n in fields)
        for v in (0, 1, 2):
            vals = values(fields, v)
            for plen, spare in DST:
                pre = bytes((0xA0 + j) & 0xFF for j in range(plen))
                f = [{"name": n, "u": x if k == "u" else 0,
                      "b": (x.hex() if k == "b" else x.to_bytes(32, "little").hex()) if k != "u" else ""}
                     for n, k, x in vals]
                cs.append({"id": f"{t}-v{v}-pre{plen}-spare{spare}", "type": t, "fields": f, "pre": pre.hex(),
                           "cap": plen + size + spare,
                           "exp": {"err": "", "out": (pre + ser(vals)).hex(), "same_array": True,
                                   "out_cap": plen + size + spare, "recv_unchanged": True}})
    return cs


def check(cp, op, rp):
    cs = {c["id"]: c for c in json.load(open(cp))}
    txt = "".join(l for l in open(op) if not l.startswith("MEMCAP "))
    got = {r["id"]: r for r in json.loads(txt)}
    rows, bad = [], 0
    for i, c in cs.items():
        g = got.get(i)
        ok = g is not None and all(g.get(k) == v for k, v in c["exp"].items())
        bad += not ok
        rows.append({"id": i, "ok": ok})
    per = {}
    for r in rows:
        t = r["id"].split("-")[0]
        per.setdefault(t, [0, 0])
        per[t][0] += 1
        per[t][1] += r["ok"]
    res = {"cases": len(cs), "match": len(cs) - bad, "mismatch": bad,
           "types": {t: {"cases": a, "match": b} for t, (a, b) in per.items()}, "rows": rows}
    json.dump(res, open(rp, "w"), indent=1)
    print(json.dumps({k: res[k] for k in ("cases", "match", "mismatch")}))
    return 1 if bad else 0


if __name__ == "__main__":
    if len(sys.argv) == 3 and sys.argv[1] == "cases":
        json.dump(cases(), open(sys.argv[2], "w"), indent=1)
    elif len(sys.argv) == 5 and sys.argv[1] == "check":
        sys.exit(check(*sys.argv[2:]))
    else:
        sys.exit(__doc__)
