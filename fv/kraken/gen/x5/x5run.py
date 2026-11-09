#!/usr/bin/env python3
"""phase1c X5: apply the X4 generator to the in-scope Prysm inventory on the Go 1.26.10 namespace.

Usage (Python 3 standard library only; run with python3 -I -B):
  x5run.py link <outdir>                 link input dir for link/check.py (filtered objdump, ELF, nm links)
  x5run.py gen <outdir> <desccheck-result> <desc-dir> <work>
         after `conv.py <outdir>/target.objdump <outdir>/p1bin-amd64.nm <outdir>/norm --norm` and
         `check.py <outdir>` PASS (both gated): per type and obligation, either a generated Lean
         statement + proof (written to lean/Gen1cX4/X5/, modules Gen1cX4.X5.*, namespace Gen1cX5) or a classified refusal; negative and control files
         for every generated theorem; the forced Lean attempts of the anchored templates (work/).
  x5run.py table <work> <out.json>       after the gated Lean runs: the per-type pass/fail table

What is attempted, per in-scope type (fv/kraken/prysm/SCOPE-P6.json, p1_scope "in"):
- size: the X4 size template (statement from the Desc fixed size, proof walked from the directive list)
  for every fixed-size type whose Go 1.26.10 SizeSSZ is `mov $n,%eax; retq`; other SizeSSZ shapes are a
  refusal (automation limit: no size template for a computed size).
- UnmarshalSSZ/MarshalSSZTo: the template that the X4 generator would pick from the Desc (uint/bool
  fields -> Scalars walk; byte-vector/container/bit fields -> anchored hand template of Checkpoint or
  AttestationData; one list field -> ListU64/ListC templates), checked against the Go 1.26.10 code. A
  template that does not fit is a refusal with the generator's reason. For the two anchored hand types
  the template is also forced onto the new code (anchor check off) and elaborated, so that the Lean
  error is recorded.
Nothing from the Go 1.26.3 proofs is reused: the code constants include the Go 1.26.10 .S files of this
namespace. No hand edit of any generated file.
"""
import json
import os
import re
import shutil
import sys

sys.dont_write_bytecode = True
HERE = os.path.dirname(os.path.abspath(__file__))
KRAKEN = os.path.normpath(os.path.join(HERE, "..", ".."))
sys.path.insert(0, os.path.join(KRAKEN, "gen", "x4"))
sys.path.insert(0, os.path.join(KRAKEN, "gen", "gen1c"))
import anchor  # noqa: E402
import emit  # noqa: E402
import x4gen  # noqa: E402

S_ART = "/workspace/agent-runs/methodical-fv-parallel/streams/phase1c/artifacts"
ELF = os.path.join(S_ART, "elf", "p1cbin-amd64")
OBJDUMP = os.path.join(S_ART, "elf", "p1cbin-amd64.objdump")
NM = os.path.join(S_ART, "elf", "p1cbin-amd64.nm")
NS_DIR = os.path.join(KRAKEN, "prysm", "go1.26.10", "link")       # committed: norm .S, RESULT
LEAN = os.path.join(KRAKEN, "lean")
METHODS = ("SizeSSZ", "UnmarshalSSZ", "MarshalSSZTo")
CLASSES = ("new instruction", "missing contract", "automation limit", "generator defect")


def in_scope():
    rows = json.load(open(os.path.join(KRAKEN, "prysm", "SCOPE-P6.json")))["rows"]
    return [r for r in rows if r["p1_scope"] == "in"]


def fn_name(r, m):
    return f"{r['package']}.(*{r['type']}).{m}"


def norm_name(r, m):
    return re.sub(r"[^A-Za-z0-9_.]", "_", f"{r['package']}.{r['type']}.{m}")


def lean_code(r, m):
    pk = r["package"].rsplit("/", 1)[1]
    return f"X5_{pk}_{r['type']}_{m}"


def desc_of(r, ddir):
    pk = "_".join(r["package"].split("/")[-2:])
    p = os.path.join(ddir, f"{pk}.{r['type']}.desc.json")
    return p if os.path.exists(p) else None


def wanted(rows):
    """Functions in the link set: SizeSSZ of every in-scope type, and the decoder and encoder of the two
    types that have anchored hand templates (forced attempts)."""
    out = []
    for r in rows:
        out.append(fn_name(r, "SizeSSZ"))
        if r["type"] in x4gen.ANCHOR_HAND and r["package"].endswith("/v1alpha1"):
            out += [fn_name(r, "UnmarshalSSZ"), fn_name(r, "MarshalSSZTo")]
    return out


def link(outdir):
    os.makedirs(os.path.join(outdir, "data"), exist_ok=True)
    want = set(wanted(in_scope()))
    keep, cur, seen = [], False, set()
    for line in open(OBJDUMP):
        if line.startswith("TEXT "):
            name = line.split()[1].removesuffix("(SB)")
            cur = name in want
            if cur:
                seen.add(name)
        if cur:
            keep.append(line)
    missing = sorted(want - seen)
    open(os.path.join(outdir, "target.objdump"), "w").write("".join(keep))
    for src, dst in ((ELF, "p1bin-amd64"), (NM, "p1bin-amd64.nm")):
        p = os.path.join(outdir, dst)
        if not os.path.lexists(p):
            os.symlink(src, p)
    print(json.dumps({"functions": len(seen), "missing": missing}))


def size_shape(D):
    return [t for k, t in D if k == "instr"]


def gen(outdir, result, ddir, work):
    os.makedirs(work, exist_ok=True)
    th = json.load(open(os.path.join(KRAKEN, "gen", "frozen", "THEOREMS.json")))
    norm = os.path.join(outdir, "norm")
    rows = in_scope()
    nsd = os.path.join(NS_DIR, "norm")
    os.makedirs(nsd, exist_ok=True)
    table, code_defs, size_thms, mut_thms, mut_codes, forced = [], [], [], [], [], []
    for r in rows:
        t = r["type"]
        rec = {"type": t, "package": r["package"], "p6_first_class": r["first_class"],
               "kparse_M_S_U": r["kraken_parse_M_S_U"], "obligations": {}}
        table.append(rec)
        dp = desc_of(r, ddir)
        key = f"{r['package']}.{t}"
        try:
            [(_k, desc, _p, dsha, _r)] = emit.accept(result, ddir, [key], "prysm", th)
        except SystemExit as e:
            rec["desc"] = f"refused by the emit boundary: {e}"
            continue
        rec["desc_sha256"] = dsha
        rec["frozen_rows"] = sum(o["type"] == t for o in th["prysm"]["obligations"])
        # ---- size
        sp = os.path.join(norm, norm_name(r, "SizeSSZ") + ".S")
        D = x4gen.directives(sp)
        shape = size_shape(anchor.directives(sp))
        fs = desc["fixed_size"]
        if fs is not None and shape == [f"mov ${hex(fs)},%eax", "retq"]:
            code = lean_code(r, "SizeSSZ")
            shutil.copyfile(sp, os.path.join(nsd, norm_name(r, "SizeSSZ") + ".S"))
            code_defs.append(f'def {code} : Program := include_x64_rt "../prysm/go1.26.10/link/norm/{norm_name(r, "SizeSSZ")}.S"')
            st = x4gen.size_stmt(f"Gen1cX5.Code.{code}", fs).replace("def size_stmt", f"def {t}_size_stmt", 1)
            pr = "\n".join("  " + x for x in x4gen.size_proof(D))
            size_thms.append((t, f"{st}\ntheorem {t}_size [Host] : {t}_size_stmt := by\n{pr}\n"))
            mc = code + "_Mut"
            mtext = open(sp).read().replace(f"  mov ${hex(fs)},%eax\n", f"  mov ${hex(fs + 1)},%eax\n", 1)
            mp = os.path.join(work, "mut", norm_name(r, "SizeSSZ") + ".S")
            os.makedirs(os.path.dirname(mp), exist_ok=True)
            open(mp, "w").write(mtext)
            mut_codes.append(f'def {mc} : Program := include_x64_rt "{mp}"')
            mst = x4gen.size_stmt(mc, fs).replace("def size_stmt", f"def {t}_size_stmt", 1)
            mut_thms.append((t, f"{mst}\ntheorem {t}_size [Host] : {t}_size_stmt := by\n{pr}\n"))
            rec["obligations"]["size"] = {"status": "generated", "template": "X4 size (Desc fixed size; directive walk)"}
        elif fs is None:
            rec["obligations"]["size"] = {"status": "refused", "class": "automation limit",
                                          "reason": f"variable-size type: SizeSSZ computes the size ({len(shape)} instructions); X4 has a size template only for the ListU64/ListC shapes and constant sizes"}
        else:
            rec["obligations"]["size"] = {"status": "refused", "class": "automation limit",
                                          "reason": f"SizeSSZ is not `mov ${hex(fs)},%eax; retq`: {shape[:4]}"}
        # ---- decoder / encoder: the template the X4 generator picks from the Desc
        kinds = {f["kind"] for f in desc["fields"]}
        if "list" in kinds:
            why = ("X4 list templates take one list field and nothing else (ListU64/ListC shape: fixed part 4); "
                   f"this Desc has fields {sorted(kinds)}, {len(desc['fields'])} fields")
            rec["obligations"]["decoder/encoder"] = {"status": "refused", "class": "automation limit", "reason": why}
        elif kinds & {"byteVector", "container", "bitList", "bitVector", "vector", "byteList"}:
            if t in ("Checkpoint", "AttestationData") and r["package"].endswith("/v1alpha1"):
                out = {}
                for m in ("UnmarshalSSZ", "MarshalSSZTo"):
                    hand = os.path.join(KRAKEN, "link", "out", "norm", f"target_prysm.{t}.{m}.S")
                    tgt = os.path.join(norm, norm_name(r, m) + ".S")
                    try:
                        anchor.Anchor(hand, tgt)
                        out[m] = {"status": "template fits"}
                    except ValueError as e:
                        calls = lambda f: {x.split()[1] for _, x in anchor.directives(f) if x.startswith("callq ")}
                        new = sorted(calls(tgt) - calls(hand))
                        prim = [c for c in new if "_consensus_types_primitives." in c]
                        out[m] = {"status": "refused", "class": "missing contract" if prim else "automation limit",
                                  "reason": f"anchored hand template of {t} does not fit the Go 1.26.10 code: {e}",
                                  "calls_not_in_hand_code": new,
                                  "why": ("the Prysm code calls hand-written primitive SSZ methods " + ", ".join(prim) +
                                          " (no function spec or contract; user decision open, INBOX 005 item 2) and the "
                                          "Checkpoint methods out of line; the hand code inlines them") if prim else None}
                        forced.append((r, m))
                rec["obligations"]["decoder/encoder"] = out
            else:
                rec["obligations"]["decoder/encoder"] = {"status": "refused", "class": "automation limit",
                    "reason": f"no X4 template for fields {sorted(kinds)}: the anchored templates exist only for the hand "
                              "cases Checkpoint and AttestationData; the Scalars walk takes uint/bool fields only"}
        else:
            nb = sum(f["kind"] == "bool" for f in desc["fields"])
            rec["obligations"]["decoder/encoder"] = {"status": "refused", "class": "automation limit",
                "reason": (f"Scalars walk: accept/marshal templates take exactly one bool field (this type has {nb}); "
                           "reject_size template is for a frameless leaf decoder (Scalars: `mov %rbx,0x10(%rsp)` "
                           "first), the Go 1.26.10 decoders open a frame with a stack check")}
    # ---- Lean modules
    head = ["-- Generated by fv/kraken/gen/x5/x5run.py. Go 1.26.10 namespace (experimental baseline): the code",
            "-- constants include the .S files of fv/kraken/prysm/go1.26.10/link/norm (link/conv.py output of the",
            "-- Go 1.26.10 ELF, link/check.py RESULT next to them). Nothing from the Go 1.26.3 proofs is used. Do not edit."]
    os.makedirs(os.path.join(LEAN, "Gen1cX4", "X5"), exist_ok=True)   # module Gen1cX4.X5.* (library glob), namespace Gen1cX5
    open(os.path.join(LEAN, "Gen1cX4", "X5", "Code.lean"), "w").write("\n".join(
        head + ["import Kraken.X64.Parser", "import Fk.Include", "", "namespace Gen1cX5.Code", "", *code_defs, "", "end Gen1cX5.Code", ""]))
    open(os.path.join(LEAN, "Gen1cX4", "X5", "Size.lean"), "w").write("\n".join(
        head + ["-- Statements: X4 size template with the Desc fixed size; proofs: directive walk (x4gen.size_proof).",
                "import Fk.Step", "import Gen1cX4.X5.Code", "", "namespace Gen1cX5.Size", "open Fk Fk.Code", "",
                *[x for _, x in size_thms], "end Gen1cX5.Size", ""]))
    # negative: every size theorem against its code with `mov $(n+1),%eax`, one file; control = Size.lean itself
    ml = ["import Fk.Step", "import Fk.Include", "", "namespace Gen1cX5.SizeMut", "open Fk Fk.Code", "", *mut_codes, ""]
    ranges = {}
    for t, x in mut_thms:
        lo = len(ml) + 1
        ml += x.split("\n")
        ranges[t] = [lo, len(ml)]
    ml += ["end Gen1cX5.SizeMut", ""]
    open(os.path.join(work, "SizeMut.lean"), "w").write("\n".join(ml))
    json.dump(ranges, open(os.path.join(work, "SizeMut.ranges.json"), "w"), indent=1)
    # forced anchored templates (anchor check off): the hand proof text on the Go 1.26.10 code
    fl = []
    for r, m in forced:
        fl.append(forced_module(r, m, norm, work))
    json.dump({"table": table, "forced": fl}, open(os.path.join(work, "gen.json"), "w"), indent=1)
    print(json.dumps({"types": len(table), "size_generated": len(size_thms), "forced": len(fl)}))


def forced_module(r, m, norm, work):
    """The anchored hand template of the obligation(s) of method m, with the anchor check off: directive
    numbers are kept (not retargeted) and only the code name changes. This is not a generation mode; it only
    records where Lean rejects the hand proof text on the new code."""
    t = r["type"]
    H = x4gen.ANCHOR_HAND[t]
    rows = [(o, h, None, None, None, None) for o, h, mm in H["rows"] if mm == m]
    code = lean_code(r, m)
    tgt = os.path.join(norm, norm_name(r, m) + ".S")

    class Ident(anchor.Anchor):
        def __init__(self):   # no comparison: identity numbers, no symbol map
            self.symmap, self.lt = {}, []

        def num(self, n):
            return n
    old = anchor.Anchor
    anchor.Anchor = lambda hs, ts: Ident()
    try:
        own = [os.path.join(LEAN, "Fk", f"{x}.lean") for x in H["own"]]
        code_of = {f"Prysm{t}{mm}": (None, None, f"Gen1cX5.Forced.{code}") for mm in METHODS}
        text, _ = anchor.build(rows, own, code_of, f"Gen1cX5.Forced.{t}{m}",
                               ["-- forced attempt (x5run.py): hand text of the anchored template on Go 1.26.10 code, anchor check off"])
    finally:
        anchor.Anchor = old
    text = text.replace("open Fk Fk.Code\n", "open Fk Fk.Code\n\n" +
                        f'def Gen1cX5.Forced.{code} : Program := include_x64_rt "{tgt}"\n', 1)
    text = text.replace("\nimport ", "\nimport Fk.Include\nimport ", 1)
    p = os.path.join(work, f"Forced_{t}_{m}.lean")
    open(p, "w").write(text)
    return {"type": t, "method": m, "file": p, "obligations": [x[0] for x in rows]}


def table_cmd(work, out):
    g = json.load(open(os.path.join(work, "gen.json")))
    rc = dict(l.split() for l in open(os.path.join(work, "rc.txt")))
    logs = {n: open(os.path.join(work, f"{n}.log")).read() for n in rc}
    errs = lambda s: [(int(m[1]), m[2]) for m in re.finditer(r"\.lean:(\d+):\d+: error[^:]*: ?(.*)", s)]
    size_ok = rc.get("size") == "0" and not errs(logs["size"])
    ranges = json.load(open(os.path.join(work, "SizeMut.ranges.json")))
    me = errs(logs.get("sizemut", ""))
    rows, counts = [], {}
    for rec in g["table"]:
        t = rec["type"]
        o = rec["obligations"]
        if o.get("size", {}).get("status") == "generated":
            lo, hi = ranges[t]
            mut = any(lo <= a <= hi for a, _ in me)
            o["size"].update({"lean": "pass" if size_ok else "fail", "negative": "mutant fails inside" if mut else "mutant NOT caught"})
            o["size"]["status"] = "generated+proved" if size_ok and mut else "generated, check failed"
        for f in g["forced"]:
            if f["type"] == t and isinstance(o.get("decoder/encoder"), dict) and f["method"] in o["decoder/encoder"]:
                n = f"forced_{t}_{f['method']}"
                e = errs(logs.get(n, ""))
                o["decoder/encoder"][f["method"]]["forced_lean"] = (f"rc {rc.get(n)}; first error line {e[0][0]}: {e[0][1][:160]}"
                                                                    if e else f"rc {rc.get(n)}; no error")
        for k, v in o.items():
            vs = v.values() if k == "decoder/encoder" and "status" not in v else [v]
            for x in vs:
                counts[x["status"]] = counts.get(x["status"], 0) + 1
                if "class" in x:
                    counts["class: " + x["class"]] = counts.get("class: " + x["class"], 0) + 1
        rows.append(rec)
    res = {"schema": "fvphase1c.x5/1", "namespace": "Go 1.26.10 (experimental baseline)", "types": len(rows),
           "types_with_a_proof": sum(r["obligations"].get("size", {}).get("status") == "generated+proved" for r in rows),
           "types_all_obligations_proved": 0, "counts": counts, "rows": rows}
    json.dump(res, open(out, "w"), indent=1)
    print(json.dumps({k: res[k] for k in ("types", "types_with_a_proof", "counts")}))


if __name__ == "__main__":
    c = sys.argv[1]
    if c == "link":
        link(sys.argv[2])
    elif c == "gen":
        gen(*sys.argv[2:6])
    else:
        table_cmd(*sys.argv[2:4])
