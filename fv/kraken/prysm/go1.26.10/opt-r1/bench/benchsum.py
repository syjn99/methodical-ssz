#!/usr/bin/env python3
"""OPT-R1 benchmark summary (stdlib only; benchstat is not in the pinned toolchain cache).

  benchsum.py <out.json> <variant>=<go test -bench output file>...
Per benchmark and variant: n samples, ns/op median / min / max, spread = (max - min) / median, B/op and
allocs/op (all samples; a value set with more than one element is reported as a list)."""
import json
import re
import statistics
import sys

LINE = re.compile(r"^(Benchmark\S+?)(?:-\d+)?\s+(\d+)\s+([\d.]+) ns/op\s+(\d+) B/op\s+(\d+) allocs/op")


def main():
    out, rows = sys.argv[1], {}
    for arg in sys.argv[2:]:
        var, path = arg.split("=", 1)
        for l in open(path):
            m = LINE.match(l)
            if m:
                r = rows.setdefault(m[1], {}).setdefault(var, {"ns": [], "B": set(), "allocs": set()})
                r["ns"].append(float(m[3]))
                r["B"].add(int(m[4]))
                r["allocs"].add(int(m[5]))
    res = {}
    for name, vs in sorted(rows.items()):
        res[name] = {}
        for var, r in sorted(vs.items()):
            med = statistics.median(r["ns"])
            one = lambda s: sorted(s)[0] if len(s) == 1 else sorted(s)
            res[name][var] = {"n": len(r["ns"]), "ns_median": med, "ns_min": min(r["ns"]), "ns_max": max(r["ns"]),
                              "spread": round((max(r["ns"]) - min(r["ns"])) / med, 4), "B_op": one(r["B"]),
                              "allocs_op": one(r["allocs"])}
    json.dump(res, open(out, "w"), indent=1)
    for name, vs in res.items():
        print(name, " | ".join(f"{v}: n={x['n']} med={x['ns_median']:.2f} [{x['ns_min']:.2f},{x['ns_max']:.2f}] "
                               f"spread={x['spread']:.3f} B={x['B_op']} allocs={x['allocs_op']}" for v, x in vs.items()))


if __name__ == "__main__":
    main()
