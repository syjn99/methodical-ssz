#!/usr/bin/env python3
"""Go differential of the v1alpha1.HistoricalSummary, SigningData, SyncAggregatorSelectionData,
ValidatorBalance and VoluntaryExit decoders (Python 3 standard library only; the text of pending_deposit_and_pow_block_differential.py with these
cases).

  five_flat_types_differential.py cases <cases.json>                      write the cases
  five_flat_types_differential.py check <cases.json> <go-out.json> <result.json>
The Go program is `prysm/go1.26.10/evidence/five-flat-types/differential-main.go.txt`, run natively with Go 1.26.10 through the gate
with `go run -overlay` in the temporary Prysm tree (read only). This is a Go-semantics check on the host
(linux/arm64), not an execution of the amd64 ELF. Every expected value is computed here, independently of the
code under test, from consensus-specs: HistoricalSummary = Root block_summary_root ++ Root state_summary_root;
SigningData = Root object_root ++ Domain domain (both 64 bytes); SyncAggregatorSelectionData = uint64 LE slot ++
uint64 LE subcommittee_index; VoluntaryExit = uint64 LE epoch ++ uint64 LE validator_index (16 bytes);
ValidatorBalance (no consensus-specs container; Prysm proto) = uint64 LE index ++ uint64 LE balance. Decoding
accepts exactly that size. The error identity ssz.ErrSize comes from the Go source. Exit 1 on any mismatch.
"""
import json
import struct
import sys

VALS = [(0, 0), (0x0123456789ABCDEF, 7), (2 ** 64 - 1, 2 ** 64 - 1)]
ROOTS = [(bytes(32), bytes(32)), (bytes(range(32)), b"\x22" * 32), (b"\xff" * 32, b"\xff" * 32)]
# the case id prefix of each operation (the Go type in kebab case)
CASE_PREFIX = {"HistoricalSummary.UnmarshalSSZ": "historical-summary", "SigningData.UnmarshalSSZ": "signing-data", "SyncAggregatorSelectionData.UnmarshalSSZ": "sync-aggregator-selection-data", "ValidatorBalance.UnmarshalSSZ": "validator-balance", "VoluntaryExit.UnmarshalSSZ": "voluntary-exit"}


def cases():
    cs = []
    for op in ("HistoricalSummary.UnmarshalSSZ", "SigningData.UnmarshalSSZ"):
        for i, (a, b) in enumerate(ROOTS):
            cs.append({"id": f"{CASE_PREFIX[op]}-accept-{i}", "op": op, "in": (a + b).hex(),
                       "exp": {"err": "", "bytes": [a.hex(), b.hex()], "lens": [32, 32], "caps": [32, 32]}})
        for n in (0, 63, 65):
            cs.append({"id": f"{CASE_PREFIX[op]}-size-{n}", "op": op, "in": (b"\x01" * n).hex(), "exp": {"err_is_ErrSize": True}})
    for op in ("SyncAggregatorSelectionData.UnmarshalSSZ", "ValidatorBalance.UnmarshalSSZ", "VoluntaryExit.UnmarshalSSZ"):
        for i, (a, b) in enumerate(VALS):
            cs.append({"id": f"{CASE_PREFIX[op]}-accept-{i}", "op": op, "in": (struct.pack("<Q", a) + struct.pack("<Q", b)).hex(),
                       "exp": {"err": "", "u64s": [a, b]}})
        for n in (0, 15, 17):
            cs.append({"id": f"{CASE_PREFIX[op]}-size-{n}", "op": op, "in": (b"\x01" * n).hex(), "exp": {"err_is_ErrSize": True}})
    return cs


def check(cp, op, rp):
    cs = {c["id"]: c for c in json.load(open(cp))}
    # the memory_limit.py wrapper appends one "MEMCAP ..." line to stdout; it is not part of the Go output
    txt = "".join(l for l in open(op) if not l.startswith("MEMCAP ") and not l.startswith("go version"))
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
