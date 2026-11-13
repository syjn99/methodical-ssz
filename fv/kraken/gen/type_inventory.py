#!/usr/bin/env python3
"""Prysm Fulu type inventory from the sszgen 698c202 IR.

  type_inventory.py reduce <raw-ir.json> <out-ir.json>
      Cut the raw inventory-tool dump: a field whose type delegates (the generated
      code calls that type's own SSZ methods) keeps only its name, package,
      sizes and delegation flags. The result is committed under
      fv/kraken/prysm/ir/ and is the only input of `build`.
  type_inventory.py build <prysm-dir>
      Read <prysm-dir>/ir/ir-{mainnet,minimal}.json and write
      <prysm-dir>/inventory.json. Every count in TYPES.md comes from there.

Definitions (see TYPES.md "Method"):
  fork configs  phase0..fulu yaml of proto/prysm/v1alpha1.
  set A         every type configured in a fork config.
  set B         named types reached from the fulu.yaml roots through fields,
                following a delegated field into the type's own IR
                (Fulu-reachable in the strict sense).
  set I         generated types in the field closure of A (inventory set).
                Named types in a closure that no config generates are the
                hand-written delegates (their SSZ methods are hand-written Go).
Python 3 standard library only. Run with python3 -I.
"""
import json
import sys
from collections import Counter, OrderedDict

FORKS = ["phase0", "altair", "bellatrix", "capella", "deneb", "electra", "fulu"]
LATER = {"gloas": "later fork (after Fulu)", "heze": "later fork (after Fulu)"}
V1 = "proto/prysm/v1alpha1/"


def cfg_name(path):
    return path.rsplit("/", 1)[-1].removesuffix(".yaml")


# ---------------------------------------------------------------- reduce

def cut(n):
    """Copy an IR node; stop below a node whose type delegates marshaling."""
    out = {k: v for k, v in n.items() if k not in ("fields", "elem", "underlying", "referent")}
    d = n.get("deleg")
    if d and d["marshaler"]:
        ref = n
        while ref["k"] == "pointer":
            ref = ref["referent"]
        out["delegated_to"] = {"k": ref["k"], "name": ref.get("name"), "pkg": ref.get("pkg"),
                               "fixed_size": ref.get("fixed_size"), "variable": ref.get("variable"),
                               "progressive": bool(ref.get("active_fields"))}
        if n["k"] == "overlay":
            # keep the (small) underlying type of a delegated named basic type, e.g. Slot -> uint64
            out["underlying"] = cut(n["underlying"])
        return out
    if "fields" in n:
        out["fields"] = [{"key": f["key"], "v": cut(f["v"])} for f in n["fields"]]
    for k in ("elem", "underlying", "referent"):
        if k in n:
            out[k] = cut(n[k])
    return out


def reduce_ir(raw_path, out_path):
    raw = json.load(open(raw_path))
    out = {"schema": "fvphase1c.ir-reduced/1", "tags": raw["tags"], "source_schema": raw["schema"], "configs": []}
    for c in raw["configs"]:
        co = {k: c[k] for k in ("file", "sha256", "package")}
        if c.get("error"):
            co["error"] = c["error"]
        co["types"] = []
        for t in c.get("types") or []:
            to = {k: v for k, v in t.items() if k not in ("ir", "package")}
            to["package"] = c["package"]
            if t.get("ir"):
                ir = t["ir"]
                top = {k: v for k, v in ir.items() if k != "fields"}
                top["fields"] = [{"key": f["key"], "v": cut(f["v"])} for f in ir.get("fields", [])]
                if ir["k"] != "container":
                    top = cut(ir)
                to["ir"] = top
            co["types"].append(to)
        out["configs"].append(co)
    with open(out_path, "w") as f:
        json.dump(out, f, indent=1, sort_keys=True)
        f.write("\n")


# ---------------------------------------------------------------- classify

def is_bytes_n(n):
    """Fixed byte vector (bytesN): copied as one block, counted as an atom."""
    return n["k"] == "vector" and n["elem"]["k"] == "byte"


def shape(n):
    """(label, inline depth, out-of-scope reason or None, callee or None) of one field.

    Inline depth counts list/vector levels that the type's own code walks.
    A bytesN vector is an atom (depth 0). A delegated field is a call (depth 0).
    """
    k = n["k"]
    if "delegated_to" in n:
        d = n["delegated_to"]
        callee = (d["pkg"], d["name"])
        if d["progressive"]:
            return "delegated progressive container", 0, "progressive", callee
        if d["k"] == "container":
            return f"delegated container ({'variable' if d['variable'] else 'fixed'})", 0, None, callee
        return f"delegated {d['k']} {d['name']}", 0, None, callee
    if k == "pointer":
        return shape(n["referent"])
    if k == "uint":
        if n["bits"] > 64:
            return f"uint{n['bits']}", 0, "uint>64", None
        return f"uint{n['bits']}", 0, None, None
    if k in ("bool", "byte"):
        return k, 0, None, None
    if k == "union":
        return "union", 0, "union", None
    if k == "overlay":
        if n.get("bitfield"):
            u = n["underlying"]
            if u["k"] == "list":
                if u.get("progressive"):
                    return "progressive bitlist", 1, "progressive", None
                return "bitlist", 1, None, None
            return "bitvector", 0, None, None
        return shape(n["underlying"])
    if k == "container":
        if n.get("active_fields"):
            return "inline progressive container", 0, "progressive", None
        return "inline container", 0, "inline container (not delegated)", None
    if k in ("vector", "list"):
        e = n["elem"]
        if k == "list" and n.get("progressive"):
            return "progressive list", 1, "progressive", None
        if k == "vector" and e["k"] == "byte":
            return "bytesN", 0, None, None
        if k == "list" and e["k"] == "byte":
            return "list[byte]", 1, None, None
        el, ed, er, callee = shape(e)
        if is_bytes_n(e):
            el = "bytesN"
        elif el.startswith("delegated container"):
            el = "container"
        elif el.startswith("delegated "):
            el = el.removeprefix("delegated ").split(" ", 1)[-1]
        label = f"{k}[{el}]"
        depth = ed + 1
        reason = er
        if reason is None and depth > 1:
            reason = "deep nesting"
        if reason is None and k == "list" and e["k"] == "uint" and e["bits"] != 64:
            reason = "list of non-uint64 basic"
        return label, depth, reason, callee
    return f"unknown:{k}", 0, f"unknown kind {k}", None


def classify(t):
    ir = t["ir"]
    res = OrderedDict()
    if ir["k"] != "container":
        lab, depth, reason, callee = shape(ir)
        res.update(kind=f"non-struct {lab}", fields=[], field_count=0, depth=depth,
                   reasons=[reason] if reason else [], callees=[callee] if callee else [])
    else:
        fields, reasons, callees, depth = [], [], [], 0
        if ir.get("active_fields"):
            reasons.append("progressive")
        for f in ir["fields"]:
            lab, d, r, callee = shape(f["v"])
            fields.append({"name": f["key"], "shape": lab, "depth": d, "out_reason": r,
                           "callee": "/".join(callee) if callee else None,
                           "fixed_size": f["v"].get("fixed_size"), "variable": f["v"].get("variable")})
            depth = max(depth, d)
            if r and r not in reasons:
                reasons.append(r)
            if callee and "/".join(callee) not in callees:
                callees.append("/".join(callee))
        kind = "progressive container" if ir.get("active_fields") else (
            "variable container" if ir["variable"] else "fixed container")
        res.update(kind=kind, fields=fields, field_count=len(fields), depth=depth, reasons=reasons, callees=callees)
    res["fixed_size"] = ir.get("fixed_size")
    res["variable"] = ir.get("variable")
    res["scope"] = "out" if res["reasons"] else "in"
    return res


def walk_refs(n, acc):
    if "delegated_to" in n:
        d = n["delegated_to"]
        acc.add((d["pkg"], d["name"]))
        return
    for f in n.get("fields", []):
        walk_refs(f["v"], acc)
    for k in ("elem", "underlying", "referent"):
        if k in n:
            walk_refs(n[k], acc)


def build(pdir):
    irs = {p: json.load(open(f"{pdir}/ir/ir-{p}.json")) for p in ("mainnet", "minimal")}
    out = OrderedDict(schema="fvphase1c.inventory/1", inputs={}, definitions={}, configs=[], sets={}, types=[],
                      hand_written_delegates=[], minimal_differences=[], counts={})
    out["inputs"] = {p: {"file": f"ir/ir-{p}.json", "tags": irs[p]["tags"]} for p in irs}
    out["definitions"] = {
        "fork_configs": [V1 + c + ".yaml" for c in FORKS],
        "set_A": "every type configured in a fork config (phase0..fulu)",
        "set_B": "named types reached from the fulu.yaml roots through fields; a delegated field is followed into its type's own IR",
        "set_I": "inventory set: generated types in the closure of A (A is closed under fields only through I; B is a subset because the fulu.yaml roots are in A)",
        "fulu_reachable": "strict sense: B. The classification covers I and marks in_B per type",
        "hand_written_delegate": "a named type in the field closure of A with SSZ methods that no config generates (its methods are hand-written Go)",
        "inline_depth": "list/vector levels the type's own code walks; bytesN and delegated fields count 0",
        "scope_in": "first-pass rule: not excluded, i.e. not progressive, no union, inline depth <= 1, and every field one of: "
                    "uint8..64, bool, bytesN, bitvector, bitlist (ValidateBitlist contract), vector of a uint/bool, of bytesN or "
                    "of a delegated type, list[byte], list[uint64] (a list of another uint is out), list of bytesN or of a delegated "
                    "container, a delegated container or a delegated hand-written type. Depth is the inline depth (delegated "
                    "fields are not followed). 'in' is neither provability nor a match with a hand proof pattern (see SCOPE-P6)",
        "preset": "mainnet is primary; minimal differences are listed separately",
    }
    main = irs["mainnet"]
    by_key, by_cfg = {}, {}
    for c in main["configs"]:
        name = cfg_name(c["file"])
        group = ("fork" if name in FORKS and c["file"].startswith(V1) else
                 "engine" if c["file"] == "proto/engine/v1/engine.yaml" else
                 "later fork" if name in LATER else "other")
        names = [t["name"] for t in c["types"]]
        out["configs"].append({"file": c["file"], "sha256": c["sha256"], "package": c["package"], "group": group,
                               "type_count": len(names), "error": c.get("error"), "types": names})
        for t in c["types"]:
            key = (c["package"], t["name"])
            by_key.setdefault(key, []).append((c["file"], t))
            by_cfg.setdefault(c["file"], []).append(key)
    set_a = sorted({k for c in out["configs"] if c["group"] == "fork" for k in by_cfg[c["file"]]})
    roots = sorted(by_cfg[V1 + "fulu.yaml"])

    def closure(start):
        seen, stack = set(), list(start)
        while stack:
            k = stack.pop()
            if k in seen:
                continue
            seen.add(k)
            if k in by_key:
                refs = set()
                walk_refs(by_key[k][0][1]["ir"], refs)
                stack.extend(sorted(refs - seen))
        return seen

    set_b = sorted(closure(roots))
    gen_b = sorted(k for k in set_b if k in by_key)
    clo_a = closure(set_a)
    hand = {k for k in clo_a if k not in by_key}
    reach = sorted(k for k in clo_a if k in by_key)
    fmt = lambda ks: [f"{p}.{n}" for p, n in ks]
    out["sets"] = {
        "A": fmt(set_a), "B": fmt(set_b), "B_generated": fmt(gen_b), "B_hand_written": fmt(sorted(k for k in set_b if k not in by_key)),
        "A_minus_B": fmt(sorted(set(set_a) - set(set_b))), "B_generated_minus_A": fmt(sorted(set(gen_b) - set(set_a))),
        "I_minus_A": fmt(sorted(set(reach) - set(set_a))), "I_hand_written": fmt(sorted(hand)),
        "I": fmt(reach), "roots": fmt(roots),
    }
    later = {}
    for c in out["configs"]:
        if c["group"] in ("later fork", "other"):
            for t in c["types"]:
                k = (c["package"], t)
                if k not in set(reach):
                    later.setdefault(c["file"], []).append(t)
    out["not_fulu"] = [{"config": f, "reason": (LATER.get(cfg_name(f)) or "not a fork config and no type reached from the Fulu roots"),
                        "types": sorted(ts)} for f, ts in later.items()]
    mins = {}
    for c in irs["minimal"]["configs"]:
        for t in c["types"]:
            mins[(c["package"], t["name"])] = t
    for k in reach:
        cfgs = by_key[k]
        f, t = cfgs[0]
        row = OrderedDict(name=k[1], package=k[0], config=f, also_in=[x for x, _ in cfgs[1:]],
                          in_A=k in set(set_a), in_B=k in set(set_b), is_root=k in set(roots),
                          go_file=t["go_file"], go_file_kind=t["go_file_kind"],
                          go_size_gc_amd64=t["go_size_gc_amd64"])
        row.update(classify(t))
        mt = mins.get(k)
        if mt is None:
            row["minimal"] = "missing"
        elif mt["ir"] != t["ir"]:
            row["minimal"] = "differs"
            out["minimal_differences"].append({"type": f"{k[0]}.{k[1]}", "mainnet_fixed_size": t["ir"].get("fixed_size"),
                                               "minimal_fixed_size": mt["ir"].get("fixed_size"),
                                               "minimal_scope": classify(mt)["scope"], "mainnet_scope": row["scope"]})
        else:
            row["minimal"] = "same"
        out["types"].append(row)
    for k in sorted(hand):
        users = sorted(f"{r['package']}.{r['name']}" for r in out["types"] if f"{k[0]}/{k[1]}" in r["callees"])
        out["hand_written_delegates"].append({"type": f"{k[0]}.{k[1]}", "used_by_count": len(users), "used_by": users})
    rows = out["types"]
    cnt = Counter()
    for r in rows:
        for x in r["reasons"]:
            cnt[x] += 1
    out["counts"] = OrderedDict(
        configs_parsed=len(out["configs"]),
        set_A=len(set_a), set_B=len(set_b), set_B_generated=len(gen_b), set_B_hand_written=len(set_b) - len(gen_b),
        A_minus_B=len(out["sets"]["A_minus_B"]), B_generated_minus_A=len(out["sets"]["B_generated_minus_A"]),
        set_I=len(reach), I_minus_A=len(out["sets"]["I_minus_A"]), I_hand_written=len(hand), roots=len(roots),
        B_scope_in=sum(r["scope"] == "in" and r["in_B"] for r in rows),
        B_scope_out=sum(r["scope"] == "out" and r["in_B"] for r in rows),
        scope_in=sum(r["scope"] == "in" for r in rows), scope_out=sum(r["scope"] == "out" for r in rows),
        out_reason_types=dict(sorted(cnt.items())),
        out_primary_reason=dict(sorted(Counter(r["reasons"][0] for r in rows if r["reasons"]).items())),
        kind=dict(sorted(Counter(r["kind"] for r in rows).items())),
        go_file_kind=dict(sorted(Counter(r["go_file_kind"] for r in rows).items())),
        field_shape=dict(sorted(Counter(f["shape"] for r in rows for f in r["fields"]).items())),
        types_calling_hand_written=sum(any(c.split("/")[-1] in {h[1] for h in hand} and c.rsplit("/", 1)[0] in {h[0] for h in hand}
                                           for c in r["callees"]) for r in rows),
        scope_in_calling_hand_written=sum(r["scope"] == "in" and any(tuple(c.rsplit("/", 1)) in hand for c in r["callees"]) for r in rows),
        minimal_differs=sum(r["minimal"] == "differs" for r in rows),
        minimal_scope_changes=sum(d["minimal_scope"] != d["mainnet_scope"] for d in out["minimal_differences"]),
        not_fulu_types=sum(len(x["types"]) for x in out["not_fulu"]),
    )
    with open(f"{pdir}/inventory.json", "w") as fh:
        json.dump(out, fh, indent=1)
        fh.write("\n")
    print(json.dumps(out["counts"], indent=1))


if __name__ == "__main__":
    if sys.argv[1] == "reduce":
        reduce_ir(sys.argv[2], sys.argv[3])
    elif sys.argv[1] == "build":
        build(sys.argv[2])
    else:
        raise SystemExit(__doc__)
