#!/usr/bin/env python3
"""Flat-type hold-out (H7): Go differential of the generated decoders (UnmarshalSSZ, 7 types) and encoder fast paths
(MarshalSSZTo, 8 types) closed in this unit (Python 3 standard library only; text of g5cdiff.py + e2cdiff.py).

  f24diff.py cases <cases.json>                      write the cases
  f24diff.py plant <cases.json> <planted.json>       copy with two expected values changed (negative control)
  f24diff.py check <cases.json> <go-out.json> <result.json>
The Go program is `prysm/go1.26.10/e2e/f24/f24check-main.go.txt`, run natively with Go 1.26.10 through the gate
with `go run -overlay` in the parked Prysm tree (read only). This is a Go-semantics check on the host
(linux/arm64), not an execution of the amd64 ELF. Every expected value is computed here, independently of the code
under test, from the field list of the hand Desc (`lean/Prysm/DepositRequest/SpecDescription.lean`, Prysm proto): the encoding is the
concatenation of the fields in order (uint64 little-endian, byte vectors as is); decoding accepts exactly that size
and yields those field values (byte fields with len = cap = size); any other size gives an error that is
ssz.ErrSize. Encoder fast path: output = prefix ++ encoding, same backing array, cap unchanged, receiver unchanged
(prefix lengths 0 / 7, capacity exact / + 5). Exit 1 on any mismatch.
"""
import json
import struct
import sys

# Go type -> [(Go field name, 'u' | 'b', size)] in SSZ order (F24Desc.lean; Go names from the IR go_fields)
TYPES = {
    "DepositRequest": [("Pubkey", "b", 48), ("WithdrawalCredentials", "b", 32), ("Amount", "u", 8),
                       ("Signature", "b", 96), ("Index", "u", 8)],
    "BuilderDepositRequest": [("Pubkey", "b", 48), ("WithdrawalCredentials", "b", 32), ("Amount", "u", 8),
                              ("Signature", "b", 96)],
    "BeaconBlocksByRangeRequest": [("StartSlot", "u", 8), ("Count", "u", 8), ("Step", "u", 8)],
    "BlobSidecarsByRangeRequest": [("StartSlot", "u", 8), ("Count", "u", 8)],
    "ExecutionPayloadEnvelopesByRangeRequest": [("StartSlot", "u", 8), ("Count", "u", 8)],
    "PartialDataColumnGroupID": [("BeaconBlockRoot", "b", 32), ("Slot", "u", 8)],
    "ValidatorIdentity": [("Index", "u", 8), ("Pubkey", "b", 48), ("ActivationEpoch", "u", 8)],
    "BuilderPreferences": [("MaxExecutionPayment", "u", 8)],
}
DEC = ["DepositRequest", "BuilderDepositRequest", "BeaconBlocksByRangeRequest", "BlobSidecarsByRangeRequest",
       "ExecutionPayloadEnvelopesByRangeRequest", "PartialDataColumnGroupID", "ValidatorIdentity"]
ENC = DEC + ["BuilderPreferences"]


def values(t, k):
    """Value set k: 0 = all zero, 1 = representative, 2 = all ones."""
    out = []
    for i, (n, kind, size) in enumerate(TYPES[t]):
        if kind == "u":
            out.append((n, kind, [0, 0x0123456789ABCDEF + i, 2 ** 64 - 1][k]))
        else:
            out.append((n, kind, [bytes(size), bytes((j + 11 * i) % 256 for j in range(size)), b"\xff" * size][k]))
    return out


def enc(vals):
    return b"".join(struct.pack("<Q", v) if kind == "u" else v for _, kind, v in vals)


def size(t):
    return sum(s for _, _, s in TYPES[t])


def cases():
    cs = []
    for t in DEC:
        for k in range(3):
            vs = values(t, k)
            cs.append({"id": f"u-{t}-accept-{k}", "type": t, "op": "u", "in": enc(vs).hex(),
                       "names": [n for n, _, _ in vs],
                       "exp": {"err": "", "vals": [{"name": n, "kind": kind, "u": v if kind == "u" else 0,
                                                   "b": v.hex() if kind == "b" else "",
                                                   "len": len(v) if kind == "b" else 0,
                                                   "cap": len(v) if kind == "b" else 0} for n, kind, v in vs]}})
        n = size(t)
        for m in (0, n - 1, n + 1):
            cs.append({"id": f"u-{t}-size-{m}", "type": t, "op": "u", "in": (b"\x01" * m).hex(), "names": [],
                       "exp": {"err_is_ErrSize": True}})
    for t in ENC:
        for k in range(3):
            vs = values(t, k)
            fields = [{"name": n, "u": v if kind == "u" else 0, "b": v.hex() if kind == "b" else ""} for n, kind, v in vs]
            for pl in (0, 7):
                pre = bytes(0xa0 + j for j in range(pl))
                for spare in (0, 5):
                    cap = pl + size(t) + spare
                    cs.append({"id": f"m-{t}-v{k}-p{pl}-c{spare}", "type": t, "op": "m", "fields": fields,
                               "pre": pre.hex(), "cap": cap,
                               "exp": {"err": "", "out": (pre + enc(vs)).hex(), "out_cap": cap, "same_array": True,
                                       "recv_unchanged": True}})
    return cs


def check(cases_p, out_p, res_p):
    cs = json.load(open(cases_p))
    out = {r["id"]: r for r in json.load(open(out_p))}
    bad = []
    for c in cs:
        r = out.get(c["id"])
        if r is None:
            bad.append((c["id"], "missing"))
            continue
        e = c["exp"]
        if c["op"] == "u":
            if e.get("err_is_ErrSize"):
                if not (r["err"] and r["err_is_ErrSize"]):
                    bad.append((c["id"], "not ErrSize"))
                continue
            if r["err"] != "":
                bad.append((c["id"], "err " + r["err"]))
                continue
            got = [{k: v[k] for k in ("name", "kind", "u", "b", "len", "cap")} for v in (r["vals"] or [])]
            if got != e["vals"]:
                bad.append((c["id"], "vals"))
        else:
            for k in ("err", "out", "out_cap", "same_array", "recv_unchanged"):
                if r[k] != e[k]:
                    bad.append((c["id"], k))
    res = {"cases": len(cs), "pass": len(cs) - len({b[0] for b in bad}), "mismatches": bad,
           "note": "Go semantics on linux/arm64 (go run -overlay, Go 1.26.10), not the amd64 ELF"}
    json.dump(res, open(res_p, "w"), indent=1)
    print(json.dumps({k: v for k, v in res.items() if k != "mismatches"}), "mismatches", len(bad))
    return 1 if bad else 0


def plant(cases_p, out_p):
    cs = json.load(open(cases_p))
    for c in cs:
        if c["id"] == "u-ValidatorIdentity-accept-1":
            c["exp"]["vals"][0]["u"] ^= 1
        if c["id"] == "m-DepositRequest-v1-p7-c5":
            c["exp"]["out"] = c["exp"]["out"][:-2] + "00"
    json.dump(cs, open(out_p, "w"), indent=1)
    return 0


if __name__ == "__main__":
    if sys.argv[1] == "cases":
        json.dump(cases(), open(sys.argv[2], "w"), indent=1)
        sys.exit(0)
    if sys.argv[1] == "plant":
        sys.exit(plant(sys.argv[2], sys.argv[3]))
    if sys.argv[1] == "check":
        sys.exit(check(*sys.argv[2:5]))
    sys.exit("usage")
