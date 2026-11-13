#!/usr/bin/env python3
"""Compare the Go 1.26.3 and Go 1.26.10 sources of the runtime functions behind the contracts.

Usage: runtime_diff.py <goroot-1.26.3> <goroot-1.26.10> <out.json>
For every contract (or excluded path) the function bodies it rests on are extracted (from `\nfunc <name>(`
to the next `\n}\n`) and compared; whole files are compared for the assembly and the ABI document.
Python 3 standard library only.
"""
import difflib
import hashlib
import json
import sys

G3, G10, OUT = sys.argv[1:4]
# contract -> [(file, function or None for the whole file)]
ROWS = {
    "MakesliceContract (esz 1)": [("src/runtime/slice.go", "makeslice"), ("src/runtime/malloc.go", "mallocgc")],
    "GrowsliceContract (esz 1)": [("src/runtime/slice.go", "growslice"), ("src/runtime/slice.go", "nextslicecap"),
                           ("src/runtime/malloc.go", "mallocgc"), ("src/runtime/msize.go", "roundupsize")],
    "MemmoveContract": [("src/runtime/memmove_amd64.s", None)],
    "NewobjectContract": [("src/runtime/malloc.go", "newobject"), ("src/runtime/malloc.go", "mallocgc")],
    "ConvT64Contract": [("src/runtime/iface.go", "convT64"), ("src/runtime/malloc.go", "mallocgc")],
    "FmtErrorfWrapContract / FmtErrorfDecimalDecimalContract (fmt.errorf)": [("src/fmt/errors.go", None), ("src/fmt/print.go", None),
                                                ("src/fmt/format.go", None), ("src/errors/errors.go", None)],
    "writeBarrier = 0 (gcWriteBarrier2 excluded)": [("src/runtime/mbarrier.go", None), ("src/runtime/mwbbuf.go", None),
                                                   ("src/runtime/asm_amd64.s", None)],
    "stack guard (morestack excluded)": [("src/runtime/asm_amd64.s", None), ("src/runtime/stack.go", "newstack")],
    "ABIInternal amd64": [("src/cmd/compile/abi-internal.md", None), ("src/internal/abi/abi_amd64.go", None),
                          ("src/internal/abi/type.go", None)],
    # changed functions that no contract rests on (recorded so that the change is accounted for)
    "not used: moveSliceNoCap": [("src/runtime/slice.go", "moveSliceNoCap")],
    "not used: itabInit": [("src/runtime/iface.go", "itabInit")],
    "not used: adjustframe (morestack path, excluded)": [("src/runtime/stack.go", "adjustframe")],
}


def body(root, f, fn):
    s = open(f"{root}/{f}", encoding="utf-8").read()
    if fn is None:
        return s
    i = s.index(f"\nfunc {fn}(")
    j = s.index("\n}\n", i)
    return s[i:j + 3]


out = {"go_1_26_3": G3, "go_1_26_10": G10, "rows": []}
for c, parts in ROWS.items():
    items = []
    for f, fn in parts:
        a, b = body(G3, f, fn), body(G10, f, fn)
        d = list(difflib.unified_diff(a.splitlines(), b.splitlines(), lineterm="", n=0))
        items.append({"file": f, "function": fn, "same": a == b,
                      "sha256_1_26_3": hashlib.sha256(a.encode()).hexdigest(),
                      "sha256_1_26_10": hashlib.sha256(b.encode()).hexdigest(),
                      "diff": d[2:] if d else []})
    out["rows"].append({"contract": c, "unchanged": all(i["same"] for i in items), "parts": items})
json.dump(out, open(OUT, "w"), indent=1)
for r in out["rows"]:
    print(("UNCHANGED" if r["unchanged"] else "CHANGED  "), r["contract"])
