#!/usr/bin/env python3
"""Instruction and runtime-call classification of the target ELF.

Usage: mnemonics.py <objdump> <kraken Parser/Basic.lean> <convert_objdump.py> <inventory.json> <out.json>

<objdump> is `go tool objdump -gnu -s RE` of the Go 1.26.10 ELF
(fv/kraken/gen/prysm-elf.sh). For each function: instruction count, GNU
mnemonic set, the mnemonics that the Kraken runtime parser does not accept, and
the call targets grouped by kind.

How "Kraken supports a mnemonic" is decided (mnemonic level only):
  1. The accepted mnemonic names are the string literals of the match arms of
     `parseInstr` in the pinned Kraken package (Kraken/X64/Parser/Basic.lean),
     plus the prefix forms `j<cc>`, `set<cc>`, `cmov<cc>[wlq]` with the
     condition codes of `parseCondCode?`. This is the parser that
     `include_x64_code` (Machine/Include.lean) runs.
  2. A whole GNU instruction text in the NORM table of link/convert_objdump.py counts as
     "norm" (convert_objdump.py --norm rewrites it to `nop`).
  3. Anything else is "unsupported".
Operand forms are not checked here. A real parse of every function is a
separate gated Lean run (fv/kraken/gen/kraken-parser/).
Python 3 standard library only. Run with python3 -I.
"""
import importlib.util
import json
import re
import sys
from collections import Counter, OrderedDict

PRYSM = "github.com/OffchainLabs/prysm/v7/"
GEN_PKGS = {PRYSM + "proto/prysm/v1alpha1", PRYSM + "proto/engine/v1"}
HAND_PKG = PRYSM + "consensus-types/primitives"


def kraken_mnemonics(path):
    src = open(path).read().split("\n")
    start = next(i for i, l in enumerate(src) if l.startswith("def parseInstr"))
    end = next(i for i in range(start, len(src)) if src[i].startswith("-- Label Parsing"))
    names = set()
    # An arm line is `| "a" | "b"` optionally followed by `=> ...`; only the
    # part before `=>` is read.
    arm = re.compile(r'^\s*\|(\s*"[A-Za-z0-9]+"\s*\|?)+\s*$')
    for l in src[start:end]:
        head = l.split("=>", 1)[0]
        if arm.match(head):
            names.update(re.findall(r'"([A-Za-z0-9]+)"', head))
    cs = next(i for i, l in enumerate(src) if l.startswith("def parseCondCode?"))
    ccs = set()
    for l in src[cs:cs + 40]:
        m = re.match(r'^\s*\|((\s*"[a-z]+"\s*\|?)+)\s*=>\s*some', l)
        if m:
            ccs.update(re.findall(r'"([a-z]+)"', m.group(1)))
    prefix_ok = [l for l in src[start:end] if 'mn.startsWith "' in l]
    prefixes = re.findall(r'mn\.startsWith "([a-z]+)"', "\n".join(prefix_ok))
    return names, ccs, prefixes


def load_norm(conv_path):
    sys.dont_write_bytecode = True  # do not leave __pycache__ in link/ (not ours)
    spec = importlib.util.spec_from_file_location("fk_conv", conv_path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return dict(mod.NORM)


def supported(mn, names, ccs):
    if mn in names:
        return True
    if mn.startswith("j") and mn[1:] in ccs:
        return True
    if mn.startswith("set") and mn[3:] in ccs:
        return True
    if mn.startswith("cmov"):
        r = mn[4:]
        return r in ccs or (r[-1:] in "wlq" and r[:-1] in ccs)
    return False


def call_kind(target):
    if target is None:
        return "indirect"
    t = target.removesuffix(".abi0")
    if t.startswith("runtime.panic") or t.startswith("runtime.goPanic"):
        return "panic*"
    if t.startswith("runtime.gcWriteBarrier"):
        return "write barrier"
    if t.startswith("runtime.moveSlice"):
        return "moveSlice* (stack-backed result to heap)"
    for k in ("makeslice", "growslice", "memmove", "newobject", "convT64", "morestack_noctxt", "memclrNoHeapPointers",
              "mallocgc", "convT", "convTslice", "convTstring", "typedmemmove", "makeslicecopy", "memequal"):
        if t == "runtime." + k:
            return k
    if t.startswith("fmt."):
        return "fmt"
    if t.endswith("ssz.ValidateBitlist"):
        return "ValidateBitlist"
    if t.endswith("ssz.ValidateBitvector"):
        return "ValidateBitvector"
    pkg = t.rsplit(".", 2)[0] if ".(" in t else t.rsplit(".", 1)[0]
    if pkg in GEN_PKGS:
        return "generated method"
    if pkg == HAND_PKG:
        return "hand-written primitives method"
    if t.startswith("runtime."):
        return "runtime other"
    return "other"


def parse_objdump(path):
    fns, cur = [], None
    for line in open(path):
        if line.startswith("TEXT "):
            cur = {"symbol": line.split()[1].removesuffix("(SB)"), "ins": []}
            fns.append(cur)
            continue
        if not line.strip():
            continue
        parts = line.rstrip("\n").split("\t")
        parts = [p for p in parts if p != ""]
        # file:line, addr, hex, "GOASM // GNU"
        if len(parts) < 4 or "//" not in parts[3]:
            raise SystemExit(f"unrecognized objdump line: {line!r}")
        goasm, gnu = parts[3].split("//", 1)
        cur["ins"].append((int(parts[1], 16), parts[2].strip(), goasm.strip(), re.sub(r"\s+", " ", gnu).strip()))
    return fns


def split_symbol(sym):
    m = re.match(r"^(.*)\.\(\*([A-Za-z0-9_]+)\)\.([A-Za-z0-9_]+)$", sym)
    if m:
        return m.group(1), m.group(2), m.group(3)
    pkg, name = sym.rsplit(".", 1)
    return pkg, None, name


def main():
    objdump, basic, conv, inv_path, out_path = sys.argv[1:6]
    names, ccs, prefixes = kraken_mnemonics(basic)
    norm = load_norm(conv)
    inv = json.load(open(inv_path))
    funcs = []
    for fn in parse_objdump(objdump):
        pkg, typ, meth = split_symbol(fn["symbol"])
        mns, unsup, normed, calls, wb_reads = Counter(), Counter(), Counter(), Counter(), 0
        targets = Counter()
        for _, _, goasm, gnu in fn["ins"]:
            toks = gnu.split(" ")
            mn = toks[0]
            if mn in ("lock", "rep", "repz", "repnz", "data16", "cs", "ds") and len(toks) > 1:
                mn = f"{toks[0]} {toks[1]}"
            mns[mn] += 1
            if gnu in norm:
                normed[mn] += 1
            elif not supported(mn, names, ccs):
                unsup[mn] += 1
            if "runtime.writeBarrier(SB)" in goasm:
                wb_reads += 1
            if goasm.startswith("CALL "):
                m = re.match(r"CALL ([^ ]+)\(SB\)", goasm)
                tgt = m.group(1) if m else None
                calls[call_kind(tgt)] += 1
                targets[tgt or goasm] += 1
        kind = ("generated" if pkg in GEN_PKGS else "hand-written" if pkg == HAND_PKG else "runtime/ssz")
        funcs.append(OrderedDict(symbol=fn["symbol"], package=pkg, type=typ, method=meth, kind=kind,
                                 instructions=len(fn["ins"]), mnemonics=dict(sorted(mns.items())),
                                 unsupported=dict(sorted(unsup.items())), norm=dict(sorted(normed.items())),
                                 calls=dict(sorted(calls.items())), call_targets=dict(sorted(targets.items())),
                                 write_barrier_flag_reads=wb_reads))
    have = {(f["package"], f["type"], f["method"]) for f in funcs}
    expected = [(t["package"], t["name"], m) for t in inv["types"] for m in ("MarshalSSZTo", "SizeSSZ", "UnmarshalSSZ")]
    missing = [f"{p}.{t}.{m}" for p, t, m in expected if (p, t, m) not in have]
    inv_keys = {(t["package"], t["name"]) for t in inv["types"]}
    gen = [f for f in funcs if f["kind"] == "generated" and (f["package"], f["type"]) in inv_keys
           and f["method"] in ("MarshalSSZTo", "SizeSSZ", "UnmarshalSSZ")]
    extra = [f["symbol"] for f in funcs if f["kind"] == "generated" and f not in gen]
    hand = [f for f in funcs if f["kind"] == "hand-written"]
    unsup_all, call_fn = Counter(), Counter()
    for f in gen:
        for k, v in f["unsupported"].items():
            unsup_all[k] += v
        for k in f["calls"]:
            call_fn[k] += 1
    per_type = OrderedDict()
    for t in inv["types"]:
        fs = {f["method"]: f for f in gen if f["package"] == t["package"] and f["type"] == t["name"]}
        per_type[f"{t['package']}.{t['name']}"] = OrderedDict(
            (m, None if m not in fs else OrderedDict(
                instructions=fs[m]["instructions"], mnemonic_count=len(fs[m]["mnemonics"]),
                unsupported=sorted(fs[m]["unsupported"]), calls=fs[m]["calls"],
                write_barrier_flag_reads=fs[m]["write_barrier_flag_reads"]))
            for m in ("MarshalSSZTo", "SizeSSZ", "UnmarshalSSZ"))
    out = OrderedDict(
        schema="fvphase1c.mnemonics/1",
        method="Kraken runtime parser (parseInstr match arms + j/set/cmov with parseCondCode?) at the pinned package; "
               "convert_objdump.py NORM forms count as norm; operand forms not checked",
        kraken_accepted_names=sorted(names), kraken_condition_codes=sorted(ccs), kraken_prefix_forms=prefixes,
        conv_norm_forms=sorted(norm),
        counts=OrderedDict(
            functions_dumped=len(funcs), generated_functions_inventory=len(gen),
            generated_functions_not_inventory=len(extra),
            hand_written_functions=sum(f["kind"] == "hand-written" for f in funcs),
            runtime_ssz_functions=sum(f["kind"] == "runtime/ssz" for f in funcs),
            expected_generated=len(expected), missing_generated=len(missing),
            generated_instructions=sum(f["instructions"] for f in gen),
            generated_functions_with_unsupported=sum(bool(f["unsupported"]) for f in gen),
            generated_functions_all_supported=sum(not f["unsupported"] for f in gen),
            unsupported_mnemonic_occurrences=dict(sorted(unsup_all.items())),
            functions_per_call_kind=dict(sorted(call_fn.items())),
            types_all_three_supported=sum(all(v and not v["unsupported"] for v in r.values()) for r in per_type.values()),
            max_instructions=max((f["instructions"] for f in gen), default=0),
            hand_written_instructions=sum(f["instructions"] for f in hand),
            hand_written_with_unsupported=sum(bool(f["unsupported"]) for f in hand),
            all_dumped_unsupported=dict(sorted(Counter(k for f in funcs for k in f["unsupported"]).items())),
            all_dumped_unsupported_in=sorted(f["symbol"] for f in funcs if f["unsupported"]),
            mnemonic_occurrences_inventory=dict(sorted(Counter({k: sum(f["mnemonics"].get(k, 0) for f in gen)
                                                                for f0 in gen for k in f0["mnemonics"]}).items())),
        ),
        generated_not_inventory=extra,
        missing=missing, per_type=per_type, functions=funcs)
    with open(out_path, "w") as f:
        json.dump(out, f, indent=1)
        f.write("\n")
    print(json.dumps(out["counts"], indent=1))


if __name__ == "__main__":
    main()
