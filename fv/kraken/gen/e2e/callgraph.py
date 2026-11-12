#!/usr/bin/env python3
"""Call graph of the Checkpoint / Epoch SSZ functions in the Go 1.26.10 ELF.

Usage: callgraph.py <objdump> <out.json> [<gcflags-m2.log>]
  <objdump>   `go tool objdump -gnu` of the Go 1.26.10 ELF (c6403c02...911e)
  <gcflags-m2.log>  optional: output of the gated `go build -gcflags=<pkg>=-m=2` (inlining evidence)
Reads only these files. Python 3 standard library only. Writes <out.json>; prints a summary.
"""
import json
import re
import sys

PRIM = "github.com/OffchainLabs/prysm/v7/consensus-types/primitives"
V1A1 = "github.com/OffchainLabs/prysm/v7/proto/prysm/v1alpha1"
FUNCS = [f"{V1A1}.(*Checkpoint).{m}" for m in ("SizeSSZ", "MarshalSSZTo", "UnmarshalSSZ")] + \
        [f"{PRIM}.(*Epoch).{m}" for m in ("UnmarshalSSZ", "MarshalSSZTo", "MarshalSSZ", "SizeSSZ")]
SCOPE = {FUNCS[0]: "in", FUNCS[1]: "in", FUNCS[2]: "in", FUNCS[3]: "in (callee, function spec E2)",
         FUNCS[4]: "record only (inlined into Checkpoint.MarshalSSZTo; out-of-line body unused by it)",
         FUNCS[5]: "record only (inlined)", FUNCS[6]: "record only (inlined)"}
# contract class of every call target: a = proof target (run with the Kraken semantics), b = contract (a theorem
# hypothesis), c = path excluded by a theorem premise
CLASS = {
    "runtime.morestack_noctxt.abi0": ("c", "stack-guard premise g.stackguard0 < rsp: the jbe is proved not taken"),
    "runtime.makeslice": ("b", "MakesliceC (esz 1, uint8 type word)"),
    "runtime.memmove": ("b", "MemmoveC"),
    "runtime.growslice": ("b", "GrowsliceC (esz 1)"),
    "runtime.gcWriteBarrier2": ("c", "writeBarrier = 0 premise: the cmpl/je is proved to skip the call"),
    "runtime.convT64": ("b", "ConvT64C"),
    "runtime.newobject": ("c", "nil-result branch after fmt.errorf: excluded by the contract's rax != 0"),
    "fmt.errorf": ("b", "FmtErrorfWC ('Epoch: %w', Checkpoint) / FmtErrorfDDC ('expected buffer of length %d received %d', Epoch)"),
    f"{PRIM}.(*Epoch).UnmarshalSSZ": ("a", "function spec Prysm.Epoch.Decode.accept_function_spec, proved from machine code (Prysm.Epoch.Decode.accept_function_spec_holds)"),
}


def main(objdump, out, mlog=None):
    want = set(FUNCS)
    cur = None
    res = {f: {"addr": None, "instructions": 0, "calls": []} for f in FUNCS}
    for line in open(objdump):
        if line.startswith("TEXT "):
            name = line.split()[1].removesuffix("(SB)")
            cur = name if name in want else None
            continue
        if cur is None or not line.strip():
            continue
        mm = re.match(r"\s*\S+:\d+\s+0x([0-9a-f]+)\s", line)
        if not mm:
            continue
        addr = int(mm[1], 16)
        r = res[cur]
        if r["addr"] is None:
            r["addr"] = addr
        r["instructions"] += 1
        m = re.search(r"CALL (\S+)\(SB\)", line)
        if m:
            tgt = m[1]
            cls = CLASS.get(tgt)
            r["calls"].append({"site": hex(addr), "target": tgt,
                               "class": cls[0] if cls else "UNCLASSIFIED", "how": cls[1] if cls else ""})
    missing = [f for f in FUNCS if res[f]["addr"] is None]
    inl = {}
    if mlog:
        text = open(mlog, errors="replace").read().splitlines()
        pats = {
            "can_inline_Epoch_MarshalSSZTo": r"epoch\.go:\d+:\d+: can inline \(\*Epoch\)\.MarshalSSZTo",
            "can_inline_Epoch_MarshalSSZ": r"epoch\.go:\d+:\d+: can inline \(\*Epoch\)\.MarshalSSZ\b",
            "can_inline_Epoch_SizeSSZ": r"epoch\.go:\d+:\d+: can inline \(\*Epoch\)\.SizeSSZ",
            "can_inline_Epoch_UnmarshalSSZ": r"epoch\.go:\d+:\d+: can inline \(\*Epoch\)\.UnmarshalSSZ",
            "cannot_inline_Epoch_UnmarshalSSZ": r"epoch\.go:\d+:\d+: cannot inline \(\*Epoch\)\.UnmarshalSSZ",
            "cp_marshal_inlines_Epoch_MarshalSSZTo": r"phase0\.ssz\.go:196\d:\d+: inlining call to primitives\.\(\*Epoch\)\.MarshalSSZTo",
            "cp_marshal_inlines_Epoch_MarshalSSZ": r"phase0\.ssz\.go:196\d:\d+: inlining call to primitives\.\(\*Epoch\)\.MarshalSSZ\b",
            "cp_unmarshal_inlines_Epoch_UnmarshalSSZ": r"phase0\.ssz\.go:19[89]\d:\d+: inlining call to primitives\.\(\*Epoch\)\.UnmarshalSSZ",
            "cp_unmarshal_inlines_Epoch_SizeSSZ": r"phase0\.ssz\.go:19[89]\d:\d+: inlining call to primitives\.\(\*Epoch\)\.SizeSSZ",
        }
        for k, pat in pats.items():
            inl[k] = [l.strip() for l in text if re.search(pat, l)]
    called = {f: sorted({c["target"] for c in res[f]["calls"]}) for f in FUNCS}
    asm_inlined = {
        "Checkpoint.MarshalSSZTo calls Epoch.MarshalSSZTo/MarshalSSZ/SizeSSZ":
            any("Epoch" in t for t in called[FUNCS[1]]),
        "Checkpoint.UnmarshalSSZ calls Epoch.UnmarshalSSZ": FUNCS[3] in called[FUNCS[2]],
    }
    doc = {"elf_sha256": "c6403c02a110ffd6fe6d31a3c89cd395ac457b5d62e60e2e611b8ab9a8dd911e",
           "functions": [{"name": f, "scope": SCOPE[f], **res[f]} for f in FUNCS],
           "missing": missing, "asm_call_evidence": asm_inlined, "gcflags_m2": inl,
           "unclassified_calls": sum(c["class"] == "UNCLASSIFIED" for f in FUNCS for c in res[f]["calls"])}
    json.dump(doc, open(out, "w"), indent=1)
    for f in FUNCS:
        print(f"{f}: {res[f]['instructions']} instructions, {len(res[f]['calls'])} calls -> {called[f]}")
    print(json.dumps({"missing": missing, "asm": asm_inlined, "unclassified": doc["unclassified_calls"],
                      "m2_lines": {k: len(v) for k, v in inl.items()}}))
    return 1 if missing or doc["unclassified_calls"] else 0


if __name__ == "__main__":
    sys.exit(main(*sys.argv[1:4]))
