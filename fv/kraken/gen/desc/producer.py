#!/usr/bin/env python3
"""Generator-side Desc producer (P3). Input: reduced sszgen IR. Output: one Desc JSON per type.

Usage: producer.py <out-dir> <reduced-ir.json>... [--types T1,pkg.T2] [--refs refs.json]

Desc format (schema fvphase1c.desc/1):
  type, package       Go type
  ssz                 the EthLib `Desc` term the type stands for, as JSON:
                      {"k":"bool"} {"k":"uint","w":<bytes>} {"k":"byteVector","n":N}
                      {"k":"byteList","limit":L} {"k":"bitVector","n":bits} {"k":"bitList","limit":bits}
                      {"k":"vector","elem":T,"n":N} {"k":"list","elem":T,"limit":L}
                      {"k":"container","names":[...],"fields":[...]}
  fixed_size          the generator's fixed size (null if variable)
  fixed_part_size     bytes of the container head (fixed fields + 4 per variable field)
  fields[i]           name, offset (in the head), width (in the head), variable, kind,
                      length / limit / elem_size (null = variable elements) where they apply.
                      Every field claim is checked by the checker; claims it cannot
                      check (delegated callee, element variability) are not in the format.
  variable_order      indices of the variable fields in head order
  reference           Lean constant of the hand-written EthLib Desc (or null). The checker
                      owns its own (package, type) table and FAILs a file whose
                      reference differs from it; this field never selects the spec.
All layout numbers come from the generator IR (its FixedSize/IsVariableSized), not from EthLib.
The checker (fv/kraken/gen/desccheck) shares no code with this file.
Python 3 standard library only. Run with python3 -I.
"""
import json
import os
import re
import sys


class Unsupported(Exception):
    pass


def index_ir(paths):
    idx = {}
    for p in paths:
        for c in json.load(open(p))["configs"]:
            for t in c["types"]:
                idx.setdefault((c["package"], t["name"]), t)
    return idx


def term(n, idx, depth=0):
    """EthLib Desc term of an IR node."""
    if depth > 64:
        raise Unsupported("nesting > 64")
    k = n["k"]
    if "delegated_to" in n:
        d = n["delegated_to"]
        if d["k"] == "container":
            t = idx.get((d["pkg"], d["name"]))
            if t is None:
                raise Unsupported(f"delegated container {d['pkg']}.{d['name']} has no IR")
            return container_term(t["ir"], idx, depth + 1)
        if k == "overlay" and "underlying" in n:
            return term(n["underlying"], idx, depth + 1)
        raise Unsupported(f"delegated {d['k']} {d['name']} without underlying")
    if k == "pointer":
        return term(n["referent"], idx, depth)
    if k == "bool":
        return {"k": "bool"}
    if k == "byte":
        return {"k": "uint", "w": 1}
    if k == "uint":
        return {"k": "uint", "w": n["bits"] // 8}
    if k == "overlay":
        if n.get("bitfield"):
            u = n["underlying"]
            if u["k"] == "list":
                if u.get("progressive"):
                    raise Unsupported("progressive bitlist")
                return {"k": "bitList", "limit": u["max"]}
            m = re.fullmatch(r"Bitvector(\d+)", n["name"])
            if not m:
                raise Unsupported(f"bitfield {n['name']}")
            return {"k": "bitVector", "n": int(m.group(1))}
        return term(n["underlying"], idx, depth)
    if k == "vector":
        if n["elem"]["k"] == "byte":
            return {"k": "byteVector", "n": n["size"]}
        return {"k": "vector", "elem": term(n["elem"], idx, depth + 1), "n": n["size"]}
    if k == "list":
        if n.get("progressive"):
            raise Unsupported("progressive list")
        if n["elem"]["k"] == "byte":
            return {"k": "byteList", "limit": n["max"]}
        return {"k": "list", "elem": term(n["elem"], idx, depth + 1), "limit": n["max"]}
    if k == "container":
        return container_term(n, idx, depth + 1)
    raise Unsupported(f"kind {k}")


def container_term(ir, idx, depth):
    if ir.get("active_fields"):
        raise Unsupported("progressive container")
    return {"k": "container", "names": [f["key"] for f in ir["fields"]],
            "fields": [term(f["v"], idx, depth) for f in ir["fields"]]}


def field_info(i, name, n, off, idx):
    w = n["fixed_size"]
    var = n["variable"]
    t = term(n, idx)
    info = {"name": name, "index": i, "offset": off, "width": w, "variable": var, "kind": t["k"]}
    if t["k"] in ("byteVector", "bitVector", "vector"):
        info["length"] = t["n"]
    if t["k"] in ("byteList", "bitList", "list"):
        info["limit"] = t["limit"]
    if t["k"] in ("vector", "list"):
        e = n
        while e["k"] in ("pointer", "overlay") and "delegated_to" not in e:
            e = e["referent"] if e["k"] == "pointer" else e["underlying"]
        el = e.get("elem")
        if el is not None:
            elem_var = el.get("variable") if "delegated_to" not in el else el["delegated_to"]["variable"]
            info["elem_size"] = None if elem_var else \
                (el.get("fixed_size") if "delegated_to" not in el else el["delegated_to"]["fixed_size"])
    return info


def produce(t, idx, ref=None):
    ir = t["ir"]
    if ir["k"] != "container":
        raise Unsupported("non-struct top-level type")
    fields, off, order = [], 0, []
    for i, f in enumerate(ir["fields"]):
        info = field_info(i, f["key"], f["v"], off, idx)
        fields.append(info)
        if info["variable"]:
            order.append(i)
        off += info["width"]
    return {"schema": "fvphase1c.desc/1", "type": t["name"], "package": t["package"],
            "ssz": container_term(ir, idx, 0),
            "fixed_size": None if ir["variable"] else ir["fixed_size"],
            "fixed_part_size": off, "fields": fields, "variable_order": order, "reference": ref}


def main():
    args = [a for a in sys.argv[1:] if not a.startswith("--")]
    opts = dict(a[2:].split("=", 1) for a in sys.argv[1:] if a.startswith("--"))
    out, irs = args[0], args[1:]
    idx = index_ir(irs)
    refs = json.load(open(opts["refs"])) if "refs" in opts else {}
    want = set(opts["types"].split(",")) if "types" in opts else None
    os.makedirs(out, exist_ok=True)
    done, skipped = [], []
    for (pkg, name), t in sorted(idx.items()):
        if want is not None and name not in want and f"{pkg}.{name}" not in want:
            continue
        try:
            d = produce(t, idx, refs.get(name))
        except Unsupported as e:
            skipped.append({"type": name, "package": pkg, "reason": str(e)})
            continue
        parts = pkg.split("/")
        fn = f"{name}.desc.json" if pkg.endswith(("/target", "/target/prysm")) else f"{parts[-2]}_{parts[-1]}.{name}.desc.json"
        with open(f"{out}/{fn}", "w") as f:
            json.dump(d, f, indent=1)
            f.write("\n")
        done.append(fn)
    print(json.dumps({"written": len(done), "skipped": skipped}))


if __name__ == "__main__":
    main()
