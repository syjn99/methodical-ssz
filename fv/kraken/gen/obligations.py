#!/usr/bin/env python3
"""Enumerate the error return sites of generated SSZ functions (Go source).

Usage: obligations.py sites <file.ssz.go>...      -> JSON on stdout

A reject path is one `return` with a non-nil error in UnmarshalSSZ or
MarshalSSZTo (the final `return err` / `return dst, err` is the accept path).
This is the counting rule of REPORT.md section 2 ("Go 소스 기준"). The site
kind is read from the guarding `if` line and the returned error.
This program does not share code with the generator. It reads gofmt'ed
generator output only. Python 3 standard library only. Run with python3 -I.
"""
import json
import re
import sys

KINDS = [  # (kind, regex on "<if line> => <return expr>")
    ("size-fixed", r"if size != \d+ \{ => ssz\.ErrSize$"),
    ("size-short", r"if size < \d+ \{ => ssz\.ErrSize$"),
    ("offset-first", r"if sszVarOffset\d+ != \d+ \{ => ssz\.ErrInvalidVariableOffset$"),
    ("offset-order", r"if sszVarOffset\d+ > sszVarOffset\d+ \{ => ssz\.ErrOffset$"),
    ("offset-past-size", r"if sszVarOffset\d+ > size \{ => ssz\.ErrOffset$"),
    ("offset-past-or-order", r"if sszVarOffset\d+ > size \|\| sszVarOffset\d+ < sszVarOffset\d+ \{ => ssz\.ErrOffset$"),
    ("bool-range", r"if sszSlice\d+\[0\] > 1 \{ => ssz\.ErrInvalidSerialization$"),
    ("list-misaligned", r'=> fmt\.Errorf\("misaligned bytes: '),
    ("list-too-big", r'=> fmt\.Errorf\("ssz-max exceeded: '),
    ("bytes-too-big", r"if len\(\w+\) > \d+ \{ => ssz\.ErrBytesLength$"),
    ("listc-offset-zero", r'=> fmt\.Errorf\("encountered invalid offset of 0'),
    ("listc-offset-misaligned", r'=> fmt\.Errorf\("misaligned list bytes'),
    ("listc-first-offset-past", r'if totalVarBytes < startOffset \{ => fmt\.Errorf\("list bytes too short to contain an offset'),
    ("listc-tail", r'if len\(sszSlice\d+\) > 0 \{ => fmt\.Errorf\("list bytes too short to contain an offset'),
    ("listc-offset-past", r'=> fmt\.Errorf\("offset %d points past the end'),
    ("listc-offset-order", r'=> fmt\.Errorf\("offset %d is not greater than start offset'),
    ("bitlist-invalid", r"ssz\.ValidateBitlist\(.* => (nil, )?fmt\.Errorf\(\"\w+: %w\", err\)$"),
    ("bitvector-padding", r"ssz\.ValidateBitvector\(.* => (nil, )?fmt\.Errorf\(\"\w+: %w\", err\)$"),
    ("callee-error", r"\.(UnmarshalSSZ|MarshalSSZTo)\(.* => (nil, )?fmt\.Errorf\(\"\w+: %w\", err\)$"),
    ("vector-length", r"if len\(.*\) != \d+ \{ => nil, ssz\.Err(BytesLength|VectorLength)$"),
    ("list-length", r"if len\(.*\) > \d+ \{ => nil, ssz\.ErrListTooBig$"),
    ("nil-pointer", r"== nil \{ => nil, "),
]


def functions(path):
    src = open(path).read().split("\n")
    i = 0
    while i < len(src):
        m = re.match(r"^func \(c \*(\w+)\) (UnmarshalSSZ|MarshalSSZTo)\(", src[i])
        if not m:
            i += 1
            continue
        j, body = i + 1, []
        while src[j] != "}":
            body.append((j + 1, src[j]))
            j += 1
        yield m.group(1), m.group(2), i + 1, body
        i = j + 1


def sites(paths):
    out = []
    for p in paths:
        for typ, meth, line, body in functions(p):
            rets = [(n, l.strip()) for n, l in body if re.match(r"^\s*return ", l)]
            final = rets[-1] if rets else None
            ss = []
            for k, (n, l) in enumerate(rets):
                if (n, l) == final:
                    continue
                expr = l[len("return "):]
                guard = next((g.strip() for m2, g in reversed(body) if m2 < n and re.match(r"^\s*(if|\} else if) ", g)), "")
                key = f"{guard} => {expr}"
                kind = next((kd for kd, rx in KINDS if re.search(rx, key)), "other")
                ss.append({"site": len(ss) + 1, "line": n, "guard": guard, "return": expr, "kind": kind})
            out.append({"file": p.rsplit("/", 1)[-1], "type": typ, "method": meth, "func_line": line,
                        "final_return": final[1] if final else None, "reject_sites": ss})
    return out


if __name__ == "__main__":
    if len(sys.argv) < 3 or sys.argv[1] != "sites":
        raise SystemExit(__doc__)
    json.dump(sites(sys.argv[2:]), sys.stdout, indent=1)
    sys.stdout.write("\n")
