#!/usr/bin/env python3
"""Go differential check of the SSZ methods of the Prysm types (Python 3 standard library only).

Usage (from any directory):
  differential.py cases <dir>                         write one case file `<dir>/<package>.<Type>.json` per Go type
  differential.py check <dir> <go-out.json> <result.json>
                                                      compare the output of the Go program with the expected values
  differential.py plant <dir> <planted-dir>           copy the case files and change two expected values
The tracked case files are in fv/kraken/prysm/differential-cases/. `cases` must write the same files.
The Go program is gen/checks/differential-main.go.txt. It reads the case files in its arguments and writes one JSON list.
How to build and run it is in fv/kraken/gen/README.md. `gen/prysm-rebuild-and-check.sh` runs all steps.
This is a check of Go semantics on the host. It does not run the amd64 machine code of the ELF.

Every expected value is computed here, independently of the code under test, from the consensus-specs field lists:
a uint64 field is 8 bytes little endian, a byte vector is its bytes, and the encoding is the fields in order.
PowBlock.total_difficulty is a uint256 (32 bytes little endian). ValidatorBalance has no consensus-specs container.
Its field list is the Prysm proto. The error values ssz.ErrSize and ssz.ErrBytesLength come from the Go source.

A case is a JSON object:
  id        `<type>-<decoder|encoder>-<what the case tests>`, with the type name in lower case words
  type      `<Go package name>.<Go type name>`
  method    `UnmarshalSSZ`, `MarshalSSZTo`, or `roundtrip` (UnmarshalSSZ, then MarshalSSZTo(nil) if it accepts)
  receiver  the receiver fields before the call (a list of {name, uint64 or bytes}). Without it, the zero value
  in        the input of UnmarshalSSZ (hex)
  dst       the destination of MarshalSSZTo: {prefix (hex), cap}, or null for a nil slice
  note      words for the reader only
  exp       the expected observations. Each key is compared:
            error: null for a nil error, else {is: [...], is_not: [...], text: ...} (each part optional)
            fields: the receiver fields after the call ({name, uint64} or {name, bytes, len, cap})
            receiver_unchanged, out, out_nil, out_cap, same_array, backing (the destination array after the call)
Exit 1 if a case has no output or an observation differs.
"""
import json
import pathlib
import re
import struct
import sys

# Go type -> the fields in SSZ order: (Go field name, kind, size). Kind u: uint64. b: byte vector.
# n: a uint256 that the Go field holds as 32 little-endian bytes. A named uint64 type has the one field "value".
FIELDS = {
    "primitives.Epoch": [("value", "u", 8)],
    "primitives.ValidatorIndex": [("value", "u", 8)],
    "v1.BuilderDepositRequest": [("Pubkey", "b", 48), ("WithdrawalCredentials", "b", 32), ("Amount", "u", 8),
                                 ("Signature", "b", 96)],
    "v1.DepositRequest": [("Pubkey", "b", 48), ("WithdrawalCredentials", "b", 32), ("Amount", "u", 8),
                          ("Signature", "b", 96), ("Index", "u", 8)],
    "v1alpha1.BeaconBlockHeader": [("Slot", "u", 8), ("ProposerIndex", "u", 8), ("ParentRoot", "b", 32),
                                   ("StateRoot", "b", 32), ("BodyRoot", "b", 32)],
    "v1alpha1.BeaconBlocksByRangeRequest": [("StartSlot", "u", 8), ("Count", "u", 8), ("Step", "u", 8)],
    "v1alpha1.BlobIdentifier": [("BlockRoot", "b", 32), ("Index", "u", 8)],
    "v1alpha1.BlobSidecarsByRangeRequest": [("StartSlot", "u", 8), ("Count", "u", 8)],
    "v1alpha1.BuilderPreferences": [("MaxExecutionPayment", "u", 8)],
    "v1alpha1.Checkpoint": [("Epoch", "u", 8), ("Root", "b", 32)],
    "v1alpha1.DepositMessage": [("PublicKey", "b", 48), ("WithdrawalCredentials", "b", 32), ("Amount", "u", 8)],
    "v1alpha1.Deposit_Data": [("PublicKey", "b", 48), ("WithdrawalCredentials", "b", 32), ("Amount", "u", 8),
                              ("Signature", "b", 96)],
    "v1alpha1.Eth1Data": [("DepositRoot", "b", 32), ("DepositCount", "u", 8), ("BlockHash", "b", 32)],
    "v1alpha1.ExecutionPayloadEnvelopesByRangeRequest": [("StartSlot", "u", 8), ("Count", "u", 8)],
    "v1alpha1.HistoricalSummary": [("BlockSummaryRoot", "b", 32), ("StateSummaryRoot", "b", 32)],
    "v1alpha1.PartialDataColumnGroupID": [("BeaconBlockRoot", "b", 32), ("Slot", "u", 8)],
    "v1alpha1.PendingConsolidation": [("SourceIndex", "u", 8), ("TargetIndex", "u", 8)],
    "v1alpha1.PendingDeposit": [("PublicKey", "b", 48), ("WithdrawalCredentials", "b", 32), ("Amount", "u", 8),
                                ("Signature", "b", 96), ("Slot", "u", 8)],
    "v1alpha1.PendingPartialWithdrawal": [("Index", "u", 8), ("Amount", "u", 8), ("WithdrawableEpoch", "u", 8)],
    "v1alpha1.PowBlock": [("BlockHash", "b", 32), ("ParentHash", "b", 32), ("TotalDifficulty", "n", 32)],
    "v1alpha1.SigningData": [("ObjectRoot", "b", 32), ("Domain", "b", 32)],
    "v1alpha1.SyncAggregatorSelectionData": [("Slot", "u", 8), ("SubcommitteeIndex", "u", 8)],
    "v1alpha1.SyncCommitteeMessage": [("Slot", "u", 8), ("BlockRoot", "b", 32), ("ValidatorIndex", "u", 8),
                                      ("Signature", "b", 96)],
    "v1alpha1.ValidatorBalance": [("Index", "u", 8), ("Balance", "u", 8)],
    "v1alpha1.ValidatorIdentity": [("Index", "u", 8), ("Pubkey", "b", 48), ("ActivationEpoch", "u", 8)],
    "v1alpha1.VoluntaryExit": [("Epoch", "u", 8), ("ValidatorIndex", "u", 8)],
}
U64_MAX = 2 ** 64 - 1
MIXED = 0x0123456789ABCDEF


# The values of one receiver are a dict: field name -> int (kind u or n) or bytes (kind b).

def size(t):
    return sum(s for _, _, s in FIELDS[t])


def encode(t, vals):
    out = b""
    for name, kind, n in FIELDS[t]:
        v = vals[name]
        out += struct.pack("<Q", v) if kind == "u" else v.to_bytes(32, "little") if kind == "n" else v
    return out


def raw(kind, v):
    return v.to_bytes(32, "little") if kind == "n" else v


def receiver(t, vals):
    """The receiver fields of a case (the input of MarshalSSZTo)."""
    return [{"name": n, "uint64": vals[n]} if k == "u" else {"name": n, "bytes": raw(k, vals[n]).hex()}
            for n, k, _ in FIELDS[t]]


def observed(t, vals):
    """The receiver fields that UnmarshalSSZ must give: byte fields with length = capacity = size."""
    return [{"name": n, "uint64": vals[n]} if k == "u" else
            {"name": n, "bytes": raw(k, vals[n]).hex(), "len": s, "cap": s} for n, k, s in FIELDS[t]]


def word(t):
    """The id form of a Go type: `v1alpha1.Deposit_Data` -> `deposit-data`."""
    name = t.split(".")[1].replace("_", "")
    return re.sub(r"(?<=[a-z0-9])(?=[A-Z])|(?<=[A-Z])(?=[A-Z][a-z])", "-", name).lower()


def case(t, what, method, exp, **inputs):
    return {"id": f"{word(t)}-{what}", "type": t, "method": method, **inputs, "exp": exp}


def decoder_cases(t, value_sets, sizes, fill=b"\x01"):
    """Accept: the encoding of each value set. Reject: `fill` repeated to each length of `sizes` (ssz.ErrSize)."""
    cs = [case(t, f"decoder-accept-values-{k}", "UnmarshalSSZ", {"error": None, "fields": observed(t, v)},
               **{"in": encode(t, v).hex()}) for k, v in enumerate(value_sets)]
    cs += [case(t, f"decoder-reject-size-{n}", "UnmarshalSSZ", {"error": {"is": ["ErrSize"]}}, **{"in": (fill * n).hex()})
           for n in sizes]
    return cs


def fast_path_cases(t, value_sets):
    """MarshalSSZTo with capacity for the encoding: prefix lengths 0 and 7, capacity exact and with 5 spare bytes.
    Expected: nil error, prefix ++ encoding in the array of dst, capacity unchanged, receiver unchanged."""
    cs = []
    for k, v in enumerate(value_sets):
        for plen in (0, 7):
            pre = bytes((0xA0 + j) & 0xFF for j in range(plen))
            for spare in (0, 5):
                cap = plen + size(t) + spare
                cs.append(case(t, f"encoder-fast-path-values-{k}-prefix-{plen}-spare-{spare}", "MarshalSSZTo",
                               {"error": None, "out": (pre + encode(t, v)).hex(), "same_array": True, "out_cap": cap,
                                "receiver_unchanged": True},
                               receiver=receiver(t, v), dst={"prefix": pre.hex(), "cap": cap}))
    return cs


def values(t, rows):
    """Value sets from rows of values in SSZ field order."""
    return [dict(zip((n for n, _, _ in FIELDS[t]), r)) for r in rows]


def generated_values_a(t):
    """Three value sets: all zero; uint64 field i = MIXED + i and byte j of byte field i = (j + 11 i) mod 256; all ones."""
    out = []
    for k in range(3):
        v = {}
        for i, (n, kind, s) in enumerate(FIELDS[t]):
            if kind == "u":
                v[n] = [0, MIXED + i, U64_MAX][k]
            else:
                v[n] = [bytes(s), bytes((j + 11 * i) % 256 for j in range(s)), b"\xff" * s][k]
        out.append(v)
    return out


def generated_values_b(t):
    """Three value sets: all zero, then two patterns (v = 1, 2): uint64 field i = [0, MIXED, U64_MAX, 7][(v + i) mod 4],
    byte j of byte field i = (7 j + i + v) mod 256, the uint256 = MIXED << 100 (v = 1) or 2^256 - 1 (v = 2)."""
    u64 = [0, MIXED, U64_MAX, 7]
    out = []
    for v in range(3):
        x = {}
        for i, (n, kind, s) in enumerate(FIELDS[t]):
            if kind == "u":
                x[n] = u64[(v + i) % 4] if v else 0
            elif kind == "b":
                x[n] = bytes(s) if not v else bytes((j * 7 + i + v) & 0xFF for j in range(s))
            else:
                x[n] = 0 if not v else (2 ** 256 - 1 if v == 2 else MIXED << 100)
        out.append(x)
    return out


def checkpoint_and_epoch():
    t, cs = "v1alpha1.Checkpoint", []
    roots = {"zero": bytes(32), "pattern": bytes(range(32)), "ff": b"\xff" * 32}
    for e in (0, MIXED, U64_MAX):
        for rn, r in roots.items():
            v = {"Epoch": e, "Root": r}
            b, tag = encode(t, v), f"epoch-{e:x}-root-{rn}"
            cs.append(case(t, f"decoder-accept-{tag}", "UnmarshalSSZ", {"error": None, "fields": observed(t, v)}, **{"in": b.hex()}))
            cs.append(case(t, f"encoder-fast-path-{tag}-prefix-0-cap-40", "MarshalSSZTo", {"error": None, "out": b.hex()},
                           receiver=receiver(t, v), dst={"prefix": "", "cap": 40}, note="fast (cap = len + 40)"))
            cs.append(case(t, f"encoder-fast-path-{tag}-prefix-3-cap-48", "MarshalSSZTo", {"error": None, "out": "aabbcc" + b.hex()},
                           receiver=receiver(t, v), dst={"prefix": "aabbcc", "cap": 48}, note="fast (cap > len + 40)"))
            cs.append(case(t, f"decoder-round-trip-{tag}", "roundtrip", {"error": None, "out": b.hex()}, **{"in": b.hex()}))
    sentinel = [{"name": "Epoch", "uint64": 0xAAAAAAAAAAAAAAAA}, {"name": "Root", "bytes": (b"\x33" * 32).hex()}]
    for n in (0, 39, 41, 80):
        cs.append(case(t, f"decoder-reject-size-{n}", "UnmarshalSSZ",
                       {"error": {"is": ["ErrSize"], "is_not": ["ErrBytesLength"]}, "receiver_unchanged": True},
                       receiver=sentinel, **{"in": (b"\x11" * n).hex()}))
    reject = {"error": {"is": ["ErrBytesLength"], "is_not": ["ErrSize"]}, "out_nil": True}
    for n in (0, 31, 33):
        # the encoder writes the epoch before it tests the root length: the 8 epoch bytes are already in the spare capacity
        cs.append(case(t, f"encoder-reject-root-length-{n}", "MarshalSSZTo",
                       dict(reject, backing=(struct.pack("<Q", 7) + bytes(40)).hex()),
                       receiver=receiver(t, {"Epoch": 7, "Root": b"\x22" * n}), dst={"prefix": "", "cap": 48}))
    rp = bytes(range(32))
    cs.append(case(t, "encoder-grow-prefix-0-cap-0", "MarshalSSZTo", {"error": None, "out": encode(t, {"Epoch": 5, "Root": rp}).hex()},
                   receiver=receiver(t, {"Epoch": 5, "Root": rp}), dst={"prefix": "", "cap": 0}, note="growslice"))
    # the growslice witness shape of Prysm.Checkpoint.Encode.grow_first_site: len 30, cap 36
    pre30 = bytes(range(0x40, 0x40 + 30))
    v = {"Epoch": MIXED, "Root": b"\xff" * 32}
    cs.append(case(t, "encoder-grow-prefix-30-cap-36", "MarshalSSZTo", {"error": None, "out": (pre30 + encode(t, v)).hex()},
                   receiver=receiver(t, v), dst={"prefix": pre30.hex(), "cap": 36}, note="growslice"))
    # every capacity range of the encoder (prefix 30 bytes, cap = 30 + spare)
    v = {"Epoch": 9, "Root": rp}
    for spare, note in ((0, "cap = len: growslice, then (real Go: 64 < 70) a second growslice"),
                        (3, "cap < len + 8: growslice, then a second growslice"),
                        (8, "cap = len + 8: first fits, second grows"), (20, "first fits, second grows"),
                        (39, "cap = len + 39: first fits, second grows"), (40, "fast (cap = len + 40)")):
        cs.append(case(t, f"encoder-capacity-prefix-30-cap-{30 + spare}", "MarshalSSZTo", {"error": None, "out": (pre30 + encode(t, v)).hex()},
                       receiver=receiver(t, v), dst={"prefix": pre30.hex(), "cap": 30 + spare}, note=note))
    pre10 = bytes(range(0x60, 0x60 + 10))
    cs.append(case(t, "encoder-capacity-prefix-10-cap-10", "MarshalSSZTo", {"error": None, "out": (pre10 + encode(t, v)).hex()},
                   receiver=receiver(t, v), dst={"prefix": pre10.hex(), "cap": 10}, note="cap = len: growslice x2"))
    # the reject after growth: with cap < len + 8 the epoch bytes go to the growslice block, so dst is unchanged
    for spare, n, backing in ((0, 31, pre30), (3, 33, pre30 + bytes(3)), (0, 0, pre30), (8, 33, pre30 + struct.pack("<Q", 7))):
        cs.append(case(t, f"encoder-reject-root-length-{n}-prefix-30-cap-{30 + spare}", "MarshalSSZTo",
                       dict(reject, backing=backing.hex()),
                       receiver=receiver(t, {"Epoch": 7, "Root": b"\x22" * n}), dst={"prefix": pre30.hex(), "cap": 30 + spare}))
    cs += fast_path_cases(t, generated_values_b(t))
    t = "primitives.Epoch"
    start = [{"name": "value", "uint64": 0x77}]
    for n in (7, 9):
        cs.append(case(t, f"decoder-reject-size-{n}", "UnmarshalSSZ",
                       {"error": {"text": f"expected buffer of length 8 received {n}"}, "fields": [{"name": "value", "uint64": 0x77}]},
                       receiver=start, **{"in": (b"\x01" * n).hex()}))
    cs.append(case(t, "decoder-accept", "UnmarshalSSZ", {"error": None, "fields": [{"name": "value", "uint64": 0x0102030405060708}]},
                   receiver=start, **{"in": struct.pack("<Q", 0x0102030405060708).hex()}))
    return cs


def beacon_block_header_and_validator_index():
    t = "v1alpha1.BeaconBlockHeader"
    vs = values(t, [(0, 0, bytes(32), bytes(32), bytes(32)), (MIXED, 7, bytes(range(32)), b"\x11" * 32, b"\x22" * 32),
                    (U64_MAX, U64_MAX, b"\xff" * 32, b"\xff" * 32, b"\xff" * 32)])
    cs = decoder_cases(t, vs, (0, 111, 113))
    for k, v in enumerate(vs):
        for pre, spare in ((b"", 0), (b"\xaa\xbb\xcc", 5), (bytes(range(1, 41)), 0)):
            cap = len(pre) + 112 + spare
            cs.append(case(t, f"encoder-fast-path-header-{k}-prefix-{len(pre)}-cap-{cap}", "MarshalSSZTo",
                           {"error": None, "out": (pre + encode(t, v)).hex(), "same_array": True, "out_cap": cap,
                            "receiver_unchanged": True},
                           receiver=receiver(t, v), dst={"prefix": pre.hex(), "cap": cap}))
        cs.append(case(t, f"encoder-grow-nil-destination-header-{k}", "MarshalSSZTo",
                       {"error": None, "out": encode(t, v).hex(), "receiver_unchanged": True},
                       receiver=receiver(t, v), dst=None))
        cs.append(case(t, f"encoder-grow-short-destination-header-{k}", "MarshalSSZTo",
                       {"error": None, "out": "aabbcc" + encode(t, v).hex(), "receiver_unchanged": True},
                       receiver=receiver(t, v), dst={"prefix": "aabbcc", "cap": 114}))
    for k, name in enumerate(("ParentRoot", "StateRoot", "BodyRoot")):
        for n in (31, 33):
            v = dict(vs[1], **{name: b"\x33" * n})
            cs.append(case(t, f"encoder-reject-{word('x.' + name)}-length-{n}", "MarshalSSZTo",
                           {"error": {"is": ["ErrBytesLength"]}, "out_nil": True, "receiver_unchanged": True},
                           receiver=receiver(t, v), dst={"prefix": "", "cap": 200}))
    cs += fast_path_cases(t, generated_values_b(t))
    t = "primitives.ValidatorIndex"
    cs += [case(t, f"decoder-accept-values-{k}", "UnmarshalSSZ", {"error": None, "fields": [{"name": "value", "uint64": v}]},
                **{"in": struct.pack("<Q", v).hex()}) for k, v in enumerate((0, MIXED, U64_MAX))]
    cs += [case(t, f"decoder-reject-size-{n}", "UnmarshalSSZ", {"error": {}}, **{"in": (b"\x01" * n).hex()}) for n in (0, 7, 9)]
    return cs


def hand_value_decoders():
    """Decoders with value sets written by hand (zero, mixed, ones) and the generated encoders of the same types."""
    z32, p32, f32 = bytes(32), bytes(range(32)), b"\xff" * 32
    pks, wcs, sigs = [bytes(48), bytes(range(48)), b"\xff" * 48], [bytes(32), b"\x22" * 32, b"\xff" * 32], \
        [bytes(96), bytes(range(100, 196)), b"\xff" * 96]
    u = [0, MIXED, U64_MAX]
    rows = {
        "v1alpha1.Eth1Data": [(z32, 0, z32), (p32, MIXED, b"\x22" * 32), (f32, U64_MAX, f32)],
        "v1alpha1.BlobIdentifier": [(r, v) for r, v in zip((z32, p32, f32), u)],
        "v1alpha1.DepositMessage": list(zip(pks, wcs, u)),
        "v1alpha1.Deposit_Data": list(zip(pks, wcs, u, sigs)),
        "v1alpha1.PendingPartialWithdrawal": [(0, 0, 0), (MIXED, 32000000000, 0xFEDCBA9876543210), (U64_MAX,) * 3],
        "v1alpha1.SyncCommitteeMessage": list(zip(u, (z32, p32, f32), (0, 7, U64_MAX), sigs)),
        "v1alpha1.PendingConsolidation": [(0, 0), (MIXED, 0xFEDCBA9876543210), (U64_MAX, U64_MAX)],
        "v1alpha1.PendingDeposit": list(zip(pks, wcs, u, sigs, (0, 7, U64_MAX))),
        "v1alpha1.PowBlock": [(bytes(range(i, 32 + i)), bytes(range(200, 232)), td)
                              for i, td in enumerate((0, 2 ** 255 + 12345, 2 ** 256 - 1))],
        "v1alpha1.HistoricalSummary": [(z32, z32), (p32, b"\x22" * 32), (f32, f32)],
        "v1alpha1.SigningData": [(z32, z32), (p32, b"\x22" * 32), (f32, f32)],
        "v1alpha1.SyncAggregatorSelectionData": [(0, 0), (MIXED, 7), (U64_MAX, U64_MAX)],
        "v1alpha1.ValidatorBalance": [(0, 0), (MIXED, 7), (U64_MAX, U64_MAX)],
        "v1alpha1.VoluntaryExit": [(0, 0), (MIXED, 7), (U64_MAX, U64_MAX)],
    }
    cs = []
    for t, r in rows.items():
        n = size(t)
        cs += decoder_cases(t, values(t, r), (0, n - 1, n + 1))
        cs += fast_path_cases(t, generated_values_b(t))
    return cs


def generated_value_types():
    """Decoders and encoder fast paths with the value sets of generated_values_a."""
    cs = []
    for t in ("v1.DepositRequest", "v1.BuilderDepositRequest", "v1alpha1.BeaconBlocksByRangeRequest",
              "v1alpha1.BlobSidecarsByRangeRequest", "v1alpha1.ExecutionPayloadEnvelopesByRangeRequest",
              "v1alpha1.PartialDataColumnGroupID", "v1alpha1.ValidatorIdentity"):
        n = size(t)
        cs += decoder_cases(t, generated_values_a(t), (0, n - 1, n + 1))
    for t in ("v1.DepositRequest", "v1.BuilderDepositRequest", "v1alpha1.BeaconBlocksByRangeRequest",
              "v1alpha1.BlobSidecarsByRangeRequest", "v1alpha1.ExecutionPayloadEnvelopesByRangeRequest",
              "v1alpha1.PartialDataColumnGroupID", "v1alpha1.ValidatorIdentity", "v1alpha1.BuilderPreferences"):
        cs += fast_path_cases(t, generated_values_a(t))
    return cs


def cases():
    cs = checkpoint_and_epoch() + beacon_block_header_and_validator_index() + hand_value_decoders() + generated_value_types()
    ids = [c["id"] for c in cs]
    assert len(ids) == len(set(ids)), "two cases have the same id"
    by_type = {}
    for c in cs:
        by_type.setdefault(c["type"], []).append(c)
    return by_type


def write(by_type, d):
    d = pathlib.Path(d)
    d.mkdir(parents=True, exist_ok=True)
    for t, cs in sorted(by_type.items()):
        (d / f"{t}.json").write_text(json.dumps(cs, indent=1) + "\n")


def read(d):
    return [c for p in sorted(pathlib.Path(d).glob("*.json")) for c in json.loads(p.read_text())]


def compare(exp, got):
    """The keys of exp whose observation differs."""
    bad = []
    for k, x in exp.items():
        g = got.get(k)
        if k == "error":
            if x is None:
                ok = g is None
            else:
                ok = g is not None and set(x.get("is", [])) <= set(g["is"]) and not set(x.get("is_not", [])) & set(g["is"]) \
                    and x.get("text", g["text"]) == g["text"]
        elif k == "fields":
            have = {f["name"]: f for f in g or []}
            ok = all(have.get(f["name"]) == f for f in x)
        else:
            ok = g == x
        if not ok:
            bad.append(k)
    return bad


def check(d, out_path, res_path):
    cs = read(d)
    got = {r["id"]: r for r in json.loads(pathlib.Path(out_path).read_text())}
    rows, per_type = [], {}
    for c in cs:
        g = got.get(c["id"])
        bad = ["no output"] if g is None else compare(c["exp"], g)
        rows.append({"id": c["id"], "match": not bad, "differs": bad, "observed": g})
        n = per_type.setdefault(c["type"], [0, 0])
        n[0] += 1
        n[1] += not bad
    mismatches = sum(not r["match"] for r in rows)
    res = {"cases": len(rows), "mismatches": mismatches,
           "types": {t: {"cases": a, "match": b} for t, (a, b) in sorted(per_type.items())}, "rows": rows}
    pathlib.Path(res_path).write_text(json.dumps(res, indent=1) + "\n")
    for r in rows:
        if not r["match"]:
            print("MISMATCH", r["id"], r["differs"])
    print(json.dumps({"cases": len(rows), "mismatches": mismatches}))
    return 1 if mismatches else 0


def plant(d, out_dir):
    """The negative control: change one expected field value of a decoder and one expected output byte of an encoder.
    `check` on the planted copy must report exactly these two cases."""
    by_type = {}
    for c in read(d):
        if c["id"] == "validator-identity-decoder-accept-values-1":
            c["exp"]["fields"][0]["uint64"] ^= 1
        if c["id"] == "deposit-request-encoder-fast-path-values-1-prefix-7-spare-5":
            c["exp"]["out"] = c["exp"]["out"][:-2] + "00"
        by_type.setdefault(c["type"], []).append(c)
    write(by_type, out_dir)
    return 0


if __name__ == "__main__":
    a = sys.argv[1:]
    if a[:1] == ["cases"] and len(a) == 2:
        write(cases(), a[1])
        sys.exit(0)
    if a[:1] == ["check"] and len(a) == 4:
        sys.exit(check(*a[1:]))
    if a[:1] == ["plant"] and len(a) == 3:
        sys.exit(plant(*a[1:]))
    sys.exit(__doc__)
