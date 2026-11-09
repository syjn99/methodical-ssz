#!/usr/bin/env python3
"""phase1c proof generator skeleton (P4): emits per-type files into a scratch directory.

Usage:
  emit.py --out DIR --desc-dir DIR --go F.ssz.go[,F2...] --elf ELF --nm NM --norm DIR
          --obligations hand_case|prysm --desccheck-result RESULT.json --types pkg.T1,pkg.T2
          [--code-prefix PKGSUFFIX=Prefix,...]
          [--theorems THEOREMS.json]

Per selected key (package, T) it writes <out>/<package with / -> _>/<T>/:
  desc.json        the producer Desc (checked by gen/desccheck)
  statements.lean  Lean statements as `def ... [Host] : Prop` (no proofs, no sorry);
                   templates exist for: size of a fixed-size type. Other obligations of
                   the frozen list are listed with "no template yet".
  witness.json     witness configuration (lengths empty/1/max, inner lengths)
  negative.json    negative cases (mutation + control) for the emitted statements
and <out>/data/<id>.data (through gen1c/include_adapter.py only) for every format
literal and error global the type's decoder/encoder uses, plus <out>/manifest.json.

The generator never writes into fv/kraken/lean/Fk, fv/kraken/link or
fv/kraken/gen/frozen (checked before any write). It reads the frozen lists only.
Python 3 standard library only. Run with python3 -I.
"""
import argparse
import hashlib
import json
import os
import re
import sys

sys.dont_write_bytecode = True
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import elf as elfmod  # noqa: E402
import include_adapter as inc  # noqa: E402

KRAKEN = os.path.normpath(os.path.join(HERE, "..", ".."))
FORBIDDEN = [os.path.join(KRAKEN, "lean", "Fk"), os.path.join(KRAKEN, "link"), os.path.join(KRAKEN, "gen", "frozen")]
METHODS = ("UnmarshalSSZ", "MarshalSSZTo", "SizeSSZ")


def guard_out(out):
    real = os.path.realpath(out)
    for f in FORBIDDEN:
        fr = os.path.realpath(f)
        if real == fr or real.startswith(fr + os.sep):
            raise SystemExit(f"refusing to write into {f}")
    return real


def sha(p):
    return hashlib.sha256(open(p, "rb").read()).hexdigest()


def go_functions(paths):
    """(type, method) -> body text of the gofmt'ed generated method."""
    out = {}
    for p in paths:
        src = open(p).read().split("\n")
        i = 0
        while i < len(src):
            m = re.match(r"^func \(c \*(\w+)\) (UnmarshalSSZ|MarshalSSZTo|SizeSSZ)\(", src[i])
            if m:
                j = i + 1
                while src[j] != "}":
                    j += 1
                out[(m.group(1), m.group(2))] = "\n".join(src[i:j + 1])
                i = j
            i += 1
    return out


def go_string_literal(lit):
    """Bytes of a Go interpreted string literal (the forms generated code uses)."""
    body = lit[1:-1]
    out, i = bytearray(), 0
    esc = {"n": 10, "t": 9, "\\": 92, '"': 34, "r": 13}
    while i < len(body):
        c = body[i]
        if c == "\\":
            nx = body[i + 1]
            if nx not in esc:
                raise ValueError(f"unsupported escape \\{nx} in {lit}")
            out.append(esc[nx])
            i += 2
        else:
            out += c.encode()
            i += 1
    return bytes(out)


HAND_PACKAGES = ("github.com/OffchainLabs/methodical-ssz/fv/kraken/target",
                 "github.com/OffchainLabs/methodical-ssz/fv/kraken/target/prysm")
INVENTORY = os.path.join(KRAKEN, "prysm", "inventory.json")
RESULT_SCHEMA = "fvphase1c.desccheck-result/1"


def _no_dup(pairs):
    keys = [k for k, _ in pairs]
    if len(keys) != len(set(keys)):
        raise ValueError(f"duplicate JSON key in {sorted(k for k in set(keys) if keys.count(k) > 1)}")
    return dict(pairs)


def _no_float(x):
    raise ValueError(f"non-integer number form {x!r}")


def strict_load(path):
    """JSON with the checker's strictness: no duplicate keys, integers only, no NaN/Infinity."""
    return json.loads(open(path, "rb").read().decode("utf-8"), object_pairs_hook=_no_dup,
                      parse_float=_no_float, parse_constant=_no_float)


def pkg_ok(p):
    return isinstance(p, str) and re.fullmatch(r"[A-Za-z0-9._/-]+", p) is not None and \
        all(seg not in ("", ".", "..") for seg in p.split("/"))


def accept(result_path, desc_dir, types, mode, th):
    """The emit boundary. Returns [(key, desc, path, sha256, record)] or raises SystemExit.

    A Desc is accepted only if (1) the checker result has schema RESULT_SCHEMA, verdict OK,
    empty list-level findings and the sha256 of the committed inventory; (2) it has exactly
    one `original` record for the key and one per path; (3) the sha256 of the bytes read here
    equals that record's sha256 and the record is PASS; (4) the status fits the mode: hand_case
    = a table key with status SPEC; prysm = not a table key, not a hand package, status NONE,
    and the type has rows in the frozen list. Selection is explicit (pkg.Type), never implied.
    """
    try:
        res = strict_load(result_path)
    except (OSError, ValueError) as e:
        raise SystemExit(f"{result_path}: not a strict JSON checker result ({e})")
    if res.get("schema") != RESULT_SCHEMA:
        raise SystemExit(f"{result_path}: schema {res.get('schema')!r}, want {RESULT_SCHEMA}")
    if res.get("verdict") != "OK":
        raise SystemExit(f"{result_path}: checker verdict {res.get('verdict')!r}, not OK")
    lst = res.get("list", {})
    if any(lst.get(k) for k in ("missing", "extra", "unkeyed", "duplicate_keys", "duplicate_paths", "failed_originals")) \
            or lst.get("table_self_check") is not True:
        raise SystemExit(f"{result_path}: list-level findings in an OK result: {lst}")
    inv_sha = hashlib.sha256(open(INVENTORY, "rb").read()).hexdigest()
    if res.get("inventory", {}).get("sha256") != inv_sha:
        raise SystemExit(f"{result_path}: inventory sha256 {res.get('inventory', {}).get('sha256')} != committed {inv_sha}")
    table = {(k["package"], k["type"]) for k in res.get("table_keys", [])}
    if {k[0] for k in table} - set(HAND_PACKAGES) or len(table) != 9:
        raise SystemExit(f"{result_path}: unexpected table keys {sorted(table)}")
    by_key, by_path = {}, {}
    for r in res.get("records", []):
        if r.get("role") != "original":
            continue
        k = (r.get("package"), r.get("type"))
        if k in by_key or r.get("path") in by_path:
            raise SystemExit(f"{result_path}: more than one original record for {k} or {r.get('path')}")
        by_key[k], by_path[r.get("path")] = r, k
    files = {}
    for fn in sorted(os.listdir(desc_dir)):
        path = os.path.join(desc_dir, fn)
        try:
            d = strict_load(path)
        except (OSError, ValueError) as e:
            raise SystemExit(f"{path}: not a strict JSON Desc ({e})")
        if not isinstance(d, dict):
            raise SystemExit(f"{path}: not a JSON object")
        k = (d.get("package"), d.get("type"))
        if k in files:
            raise SystemExit(f"two Descs for {k} in {desc_dir}: {files[k][1]} and {path}")
        files[k] = (d, path)
    if not types:
        raise SystemExit("--types is required (explicit pkg.Type list; no implicit selection)")
    want, seen_ns = [], set()
    for q in types:
        if "." not in q or "/" not in q.rsplit(".", 1)[0]:
            raise SystemExit(f"{q}: use a package-qualified name pkg.Type")
        k = tuple(q.rsplit(".", 1))
        if k not in by_key:
            raise SystemExit(f"{q}: no original record in the checker result (unknown key)")
        if k not in files:
            raise SystemExit(f"{q}: no Desc with this key in {desc_dir}")
        d, path = files[k]
        r = by_key[k]
        h = hashlib.sha256(open(path, "rb").read()).hexdigest()
        if r.get("result") != "PASS":
            raise SystemExit(f"{q}: checker record is {r.get('result')}")
        if r.get("sha256") != h:
            raise SystemExit(f"{q}: {path} sha256 {h} != checked {r.get('sha256')} (changed, stale or mixed result)")
        if mode == "hand_case":
            if k not in table or r.get("status") != "SPEC":
                raise SystemExit(f"{q}: hand_case needs a table key with status SPEC (got {r.get('status')})")
        else:
            prysm_types = set(th["prysm"]["types_in"])
            if k in table or k[0] in HAND_PACKAGES or r.get("status") != "NONE" or k[1] not in prysm_types:
                raise SystemExit(f"{q}: prysm mode needs a non-hand key with status NONE and frozen-list rows")
        if not pkg_ok(k[0]):
            raise SystemExit(f"{q}: package is not a plain path")
        if k[1] in seen_ns:
            raise SystemExit(f"{q}: two selected types named {k[1]} (Lean namespace and code name would collide)")
        seen_ns.add(k[1])
        want.append((k, d, path, h, r))
    return want


def code_name(t, pkg, prefixes):
    for suf, pre in prefixes.items():
        if pkg.endswith(suf):
            return pre + t
    return t


def size_stmt(code, n):
    return (f"def size_stmt [Host] : Prop :=\n"
            f"  ∀ (k : Nat) (hk : Fk.Code.{code}SizeSSZ.IsInfixAt Host.prog k) (s : MachineData) (ra : UInt64)\n"
            f"    (R : DataMem → Prop) (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec) ⋆ R),\n"
            f"    Eventually (step1 Host.exe)\n"
            f"      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = {n} ∧ st.data.regs.rsp = s.regs.rsp + 8\n"
            f"        ∧ st.data.dmem = s.dmem)\n"
            f"      ⟨s, Host.addrOf k⟩\n")


def witness_config(desc):
    cfg = {"type": desc["type"], "rule": "variable lengths: empty, 1, max; inner lengths for lists of variable elements",
           "configs": []}
    var = [f for f in desc["fields"] if f["variable"]]
    if not var:
        cfg["configs"].append({"name": "fixed", "lengths": {}})
        return cfg
    for f in var:
        lim = f.get("limit")
        if f["kind"] in ("byteList", "list", "bitList") and lim is not None:
            outer = sorted({0, 1, lim})
            inner = None
            if f["kind"] == "list" and f.get("elem_size") is None:
                inner = "per element: empty, 1, max of the element type's own variable fields"
            for n in outer:
                c = {"name": f"{f['name']}={n}", "field": f["name"], "length": n,
                     "unit": "bits" if f["kind"] == "bitList" else "elements" if f["kind"] == "list" else "bytes"}
                if inner and n > 0:
                    c["inner"] = inner
                cfg["configs"].append(c)
        else:
            cfg["configs"].append({"name": f"{f['name']}=nested", "field": f["name"], "kind": f["kind"],
                                   "length": "from the nested type's own configurations"})
    return cfg


def negative_cases(t, desc, has_size):
    cases = []
    if has_size:
        n = desc["fixed_size"]
        cases.append({"id": f"{t}.size.const", "target": "statements.lean size_stmt",
                      "mutation": f"rax = {n} -> rax = {n + 1}", "expect": "the size theorem fails in its final goal",
                      "control": "unmutated statement proves", "status": "format only (run in X4)"})
    cases.append({"id": f"{t}.code.flip", "target": f"{t} UnmarshalSSZ machine code",
                  "mutation": "one conditional jump of the length check inverted in a scratch copy of the .S",
                  "expect": "the accept theorem fails at that instruction", "control": "original .S proves",
                  "status": "format only (run in X4)"})
    return cases


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", required=True)
    ap.add_argument("--desc-dir", required=True)
    ap.add_argument("--go", required=True)
    ap.add_argument("--elf", required=True)
    ap.add_argument("--nm", required=True)
    ap.add_argument("--norm", required=True)
    ap.add_argument("--types", required=True, help="comma list of package-qualified names pkg.Type")
    ap.add_argument("--desccheck-result", required=True,
                    help="JSON result of a DescCheck.lean run (DESC_RESULT) with verdict OK")
    ap.add_argument("--code-prefix", default="")
    ap.add_argument("--theorems", default=os.path.join(KRAKEN, "gen", "frozen", "THEOREMS.json"))
    ap.add_argument("--obligations", choices=["hand_case", "prysm"], required=True,
                    help="which part of the frozen list the types belong to")
    a = ap.parse_args()
    out = guard_out(a.out)
    api = inc.check_api()
    prefixes = dict(x.split("=", 1) for x in a.code_prefix.split(",") if x)
    th = json.load(open(a.theorems))
    gofiles = a.go.split(",")
    gof = go_functions(gofiles)
    e = elfmod.Elf(a.elf)
    nm = elfmod.read_nm(a.nm)
    gs_addr, gs_size = elfmod.extent(nm, inc.RODATA_SYMBOL)
    gs = e.read(gs_addr, gs_size)
    want = accept(a.desccheck_result, a.desc_dir, a.types.split(","), a.obligations, th)
    os.makedirs(os.path.join(out, "data"), exist_ok=True)
    manifest = {"schema": "fvphase1c.gen-manifest/1", "include_api_version": inc.API_VERSION,
                "include_api_status": api["status"], "include_api_fix3_commit": api.get("fix3_commit"),
                "inputs": {"elf": sha(a.elf), "nm": sha(a.nm), "go": {os.path.basename(g): sha(g) for g in gofiles},
                           "theorems": sha(a.theorems)},
                "types": {}, "data_items": {}}
    obl = th[a.obligations]["obligations"]
    for key, d, dpath, dsha, _rec in want:
        t = key[1]
        td = os.path.join(out, key[0].replace("/", "_"), t)
        os.makedirs(td, exist_ok=True)
        json.dump(d, open(os.path.join(td, "desc.json"), "w"), indent=1)
        code = code_name(t, d["package"], prefixes)
        lines = [f"-- Generated by fv/kraken/gen/gen1c/emit.py for {d['package']}.{t}. Statements only.",
                 f"namespace Gen1c.{t}", "open Fk Fk.Code", ""]
        has_size = d["fixed_size"] is not None
        if has_size:
            lines.append(size_stmt(code, d["fixed_size"]))
        rows = [r for r in obl if r["type"] == t]
        lines.append("/-! Obligations of the frozen list (gen/frozen/THEOREMS.json) for this type:")
        for r in rows:
            tmpl = "template: size_stmt" if (r["obligation"] == "size" and has_size) else "no template yet (X4)"
            lines.append(f"  {r['id']}: {tmpl}")
        lines += ["-/", "", f"end Gen1c.{t}", ""]
        open(os.path.join(td, "statements.lean"), "w").write("\n".join(lines))
        json.dump(witness_config(d), open(os.path.join(td, "witness.json"), "w"), indent=1)
        json.dump(negative_cases(t, d, has_size), open(os.path.join(td, "negative.json"), "w"), indent=1)
        # data items: format literals and error globals of the decoder and encoder
        items = []
        for m in ("UnmarshalSSZ", "MarshalSSZTo"):
            body = gof.get((t, m), "")
            sfile = os.path.join(a.norm, [f for f in os.listdir(a.norm) if f.endswith(f".{t}.{m}.S")][0]) \
                if any(f.endswith(f".{t}.{m}.S") for f in os.listdir(a.norm)) else None
            stext = open(sfile).read() if sfile else ""
            lits = re.findall(r'fmt\.Errorf\(("(?:[^"\\]|\\.)*")', body)
            for k, lit in enumerate(dict.fromkeys(lits)):
                bs = go_string_literal(lit)
                hits = [i for i in range(len(gs)) if gs.startswith(bs, i)]
                refs = sorted({int(x) for x in re.findall(inc.RODATA_REF_RE, stext)})
                ref_hits = [h for h in hits if h in refs]
                iid = f"{t}_{m}_fmt{k}"
                rec = {"kind": "rodata-string", "literal": lit, "length": len(bs), "occurrences": hits,
                       "referenced_by_code": ref_hits, "function": m}
                if len(ref_hits) == 1 or (len(hits) == 1 and not ref_hits):
                    off = (ref_hits or hits)[0]
                    rec["label"], rec["off"] = inc.RODATA_LABEL, off
                    rec["gen_id"] = iid
                    iid, rec["api_id"] = inc.rodata_id(iid, inc.RODATA_LABEL, off, len(bs), api)
                    open(os.path.join(out, "data", inc.file_name(iid)), "w").write(inc.render(iid, inc.RODATA_LABEL, off, bs))
                    rec["file"] = inc.file_name(iid)
                    rec["lean"] = inc.lean_premise(iid)
                else:
                    rec["error"] = "literal not located uniquely in go:string.*"
                manifest["data_items"][iid] = rec
                items.append(iid)
            for g in sorted(set(re.findall(inc.ERR_GLOBAL_LABEL_RE, stext))):
                iid = inc.err_global_id(g)
                if iid not in manifest["data_items"]:
                    open(os.path.join(out, "data", inc.file_name(iid)), "w").write(inc.render(iid, g, 0))
                    manifest["data_items"][iid] = {"kind": "address only", "label": g, "off": 0,
                                                   "file": inc.file_name(iid), "lean": inc.addr_name(iid)}
                items.append(iid)
        manifest["types"][f"{key[0]}.{t}"] = {"desc_sha256": dsha, "out": os.path.relpath(td, out), "code_name": code, "files": sorted(os.listdir(td)), "data_items": sorted(set(items)),
                                "obligations": len(rows), "templates": ["size_stmt"] if has_size else []}
    json.dump(manifest, open(os.path.join(out, "manifest.json"), "w"), indent=1)
    print(json.dumps({"types": len(manifest["types"]), "data_items": len(manifest["data_items"]),
                      "data_errors": [k for k, v in manifest["data_items"].items() if "error" in v]}))


if __name__ == "__main__":
    main()
