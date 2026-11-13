#!/usr/bin/env python3
"""Summarize a log of ParserRun.lean (the Kraken parser run) into JSON.

Usage: summarize_parser_log.py <parser log> <functions.json> <out.json>
Maps each parsed file (convert_objdump.py-cleaned name) back to the ELF symbol of
functions.json and counts OK / ERR per function kind. A function of
functions.json with no KPARSE line is "not run".
Python 3 standard library only. Run with python3 -I.
"""
import json
import os
import re
import sys
from collections import Counter, OrderedDict


def clean(name):
    # same rule as link/convert_objdump.py clean() for names outside methodical-ssz/fv/kraken
    out = name.replace("github.com/OffchainLabs/methodical-ssz/", "")
    out = re.sub(r"\(\*(\w+)\)", r"\1", out)
    return re.sub(r"[^A-Za-z0-9_.]", "_", out)


def main():
    log, fpath, out_path = sys.argv[1:4]
    res = {}
    done = None
    for line in open(log):
        m = re.match(r"KPARSE (OK|ERR) (\S+) (.*)$", line.rstrip("\n"))
        if m:
            res[os.path.basename(m.group(2)).removesuffix(".S")] = (m.group(1), m.group(3))
        m = re.match(r"KPARSE DONE (\d+) (\d+)", line)
        if m:
            done = (int(m.group(1)), int(m.group(2)))
    funcs = json.load(open(fpath))["functions"]
    inv = set()
    for t, ms in json.load(open(fpath))["per_type"].items():
        pkg, name = t.rsplit(".", 1)
        for m in ms:
            inv.add(f"{pkg}.(*{name}).{m}")
    rows, cnt = [], Counter()
    for f in funcs:
        status, detail = res.get(clean(f["symbol"]), ("not run", ""))
        group = "inventory" if f["symbol"] in inv else f["kind"] + (" (not inventory)" if f["kind"] == "generated" else "")
        cnt[(group, status)] += 1
        rows.append(OrderedDict(symbol=f["symbol"], group=group, status=status,
                                directives=int(detail) if status == "OK" else None,
                                error=detail if status == "ERR" else None))
    out = OrderedDict(schema="fvphase1c.kparse/1", log_done_line=done,
                      counts={f"{g}: {s}": n for (g, s), n in sorted(cnt.items())},
                      errors=[r for r in rows if r["status"] == "ERR"], functions=rows)
    with open(out_path, "w") as fh:
        json.dump(out, fh, indent=1)
        fh.write("\n")
    print(json.dumps({"done": done, "counts": out["counts"],
                      "errors": [(r["symbol"], r["error"]) for r in out["errors"]]}, indent=1))


if __name__ == "__main__":
    main()
