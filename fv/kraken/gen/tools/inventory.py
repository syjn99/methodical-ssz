#!/usr/bin/env python3
"""Verified inventory of the pinned target's SSZ functions (unit G5-C). Python 3 standard library only.

  inventory.py names <names.txt>
      write the theorem names of the FIXED mapping table below (input of `inventory_decls.lean`)
  inventory.py run <decls.tsv> <INVENTORY.md> <INVENTORY.json>
      read `prysm/go1.26.10/functions.json` (every function of the pinned target), the committed axioms gate record
      `prysm/go1.26.10/e2e/axioms-gate.json`, the code constants of `lean/{E2e,E2eAd,E2eScal}` (`def X : Program :=
      include_x64_rt "…S"`) and <decls.tsv> (output of `gen/tools/inventory_decls.lean` for the names above, run on the
      built tree), and write the table.
  (cwd = fv/kraken)

Rule. A function's state comes ONLY from the mapping table and the declarations in <decls.tsv>:
  * every theorem named in the table must exist (kind `theorem`) and have only the standard axioms
    (`propext`, `Classical.choice`, `Quot.sound`); otherwise the script FAILS (exit 1) - the table cannot overstate;
  * the accept / reject / spec theorems of a row must have, in their TYPE, the code constant whose included `.S` is
    that function of the target (review g5-r1: key on the code constant, not on a file name or header); else FAIL;
  * a witness must use (in its proof) the row's accept / reject theorem, and `accept_spec_k` the accept theorem,
    `reject_size_spec` the reject theorem; else FAIL;
  * a decoder is "complete" (in this sense only) when accept, size reject, spec alignment (spec_k, reject_size_spec,
    reject_complete), codec equality / correspondence of the Desc, accept witness and reject witness are all present
    under these checks; "partial" when some are; "none" when the type has no row or no theorem.
  * an encoder has a "fast path" theorem when its row names one; growslice paths and encoder rejects are listed.
Types of `functions.json` without a row are "not started". Exit 0 = table written, 1 = a check failed (nothing
written), 2 = usage.
"""
import json
import pathlib
import re
import sys

KR = pathlib.Path(__file__).resolve().parent.parent.parent
STD = {"propext", "Classical.choice", "Quot.sound"}
V1A = "github.com/OffchainLabs/prysm/v7/proto/prysm/v1alpha1"
PRIM = "github.com/OffchainLabs/prysm/v7/consensus-types/primitives"

# The flat fixed-size population of the GEN5 plan (decoders; AttestationData has nested fields and is listed apart).
FLAT16 = ["Checkpoint", "BeaconBlockHeader", "Eth1Data", "BlobIdentifier", "DepositMessage", "Deposit_Data",
          "PendingPartialWithdrawal", "SyncCommitteeMessage", "PendingConsolidation", "PendingDeposit", "PowBlock",
          "HistoricalSummary", "SigningData", "SyncAggregatorSelectionData", "ValidatorBalance", "VoluntaryExit"]
NESTED = ["AttestationData"]


def dec(accept, reject, spec_k, reject_spec, reject_complete, codec, wit_a, wit_r, note=""):
    return dict(accept=accept, reject=reject, spec_k=spec_k, reject_size_spec=reject_spec,
                reject_complete=reject_complete, codec=codec, witness_accept=wit_a, witness_reject=wit_r, note=note)


def std(ns, p, P, wns, codec=None, accept=None, note=""):
    """The usual names: <ns>.<p>_e2e_*, E2e.prysm<P>Desc_deserialize_checker, <wns>.Wit<P>{A,R}."""
    return dec(accept or f"{ns}.{p}_e2e_accept_main", f"{ns}.{p}_e2e_reject_size_main", f"{ns}.{p}_e2e_accept_spec_k",
               f"{ns}.{p}_e2e_reject_size_spec", f"{ns}.{p}_e2e_reject_complete",
               codec or [f"E2e.prysm{P}Desc_deserialize_checker"],
               f"{wns}.Wit{P}A.{p}_accept_runs", f"{wns}.Wit{P}R.{p}_reject_runs", note)


def g5c(p, P, extra=""):
    return dec(f"E2eScal.Gen.{p}_g5dec_accept", f"E2eScal.Gen.{p}_g5dec_reject", f"E2eScal.G5C.{p}_e2e_accept_spec_k",
               f"E2eScal.G5C.{p}_e2e_reject_size_spec", f"E2eScal.G5C.{p}_e2e_reject_complete",
               [f"E2e.prysm{P}Desc_deserialize_checker"], f"E2eScal.Wit{P}GA.{p}_accept_runs",
               f"E2eScal.Wit{P}GR.{p}_reject_runs",
               "generated accept / size-reject theorems (p2dec --gen5; statement = kind instance)" + extra)


# ---------------------------------------------------------------- FIXED mapping table: (package, type) -> methods
DECODERS = {
    (V1A, "Checkpoint"): std("E2e", "cp", "Cp", "E2e"),
    (V1A, "AttestationData"): std("E2eAd", "ad", "Ad", "E2eAd"),
    (V1A, "BeaconBlockHeader"): std("E2eScal.Bh", "bh", "Bh", "E2eScal"),
    (V1A, "Eth1Data"): std("E2eScal.E1", "e1", "E1", "E2eScal"),
    (V1A, "BlobIdentifier"): std("E2eScal.Bi", "bi", "Bi", "E2eScal"),
    (V1A, "DepositMessage"): std("E2eScal.Dm", "dm", "Dm", "E2eScal"),
    (V1A, "Deposit_Data"): std("E2eScal.H4", "dd", "Dd", "E2eScal"),
    (V1A, "PendingPartialWithdrawal"): dec("E2eScal.H4.pw_e2e_accept_main", "E2eScal.H4.pw_e2e_reject_size_main",
                                           "E2eScal.H4.pw_e2e_accept_spec_k", "E2eScal.H4.pw_e2e_reject_size_spec",
                                           "E2eScal.H4.pw_e2e_reject_complete",
                                           ["E2e.prysmPwDesc_deserialize_checker"], "E2eScal.WitPwA.pw_accept_runs",
                                           "E2eScal.WitPwR.pw_reject_runs",
                                           "accept_spec_k added in unit G5-C (PwSpecKA.lean)"),
    (V1A, "SyncCommitteeMessage"): std("E2eScal.H5", "sm", "Sm", "E2eScal"),
    (V1A, "PendingConsolidation"): std("E2eScal.H5", "pc", "Pc", "E2eScal"),
    (V1A, "PendingDeposit"): std("E2eScal.H6", "pd", "Pd", "E2eScal", accept="E2eScal.H6.pd_e2e_accept_g4gen"),
    (V1A, "PowBlock"): std("E2eScal.H6", "pb", "Pb", "E2eScal", accept="E2eScal.H6.pb_e2e_accept_g4gen",
                           codec=["E2e.pb_accepts_same", "E2e.pb_codec_checker"],
                           note="codec: same accepted inputs + number / LE-bytes correspondence (spec uint256)"),
    (V1A, "HistoricalSummary"): g5c("hs", "Hs"),
    (V1A, "SigningData"): g5c("sd", "Sd"),
    (V1A, "SyncAggregatorSelectionData"): g5c("sa", "Sa"),
    (V1A, "ValidatorBalance"): g5c("vb", "Vb", "; spec Desc from the Prysm proto: consensus-specs has no such container"),
    (V1A, "VoluntaryExit"): g5c("ve", "Ve"),
    # primitives (hand-written methods; overlay uint64; no Desc / spec module): accept, length reject, witnesses
    (PRIM, "Epoch"): dec("E2e.ep_unmarshal_accept_main", "E2e.ep_unmarshal_reject_len_main", None, None, None, None,
                         "E2e.WitEp.ep_accept_runs", "E2e.WitEpR.epr_runs"),
    (PRIM, "Slot"): dec("E2eAd.sl_unmarshal_accept_main", None, None, None, None, None, "E2eAd.WitSl.sl_accept_runs",
                        None),
    (PRIM, "CommitteeIndex"): dec("E2eAd.ci_unmarshal_accept_main", None, None, None, None, None,
                                  "E2eAd.WitCi.ci_accept_runs", None),
    (PRIM, "ValidatorIndex"): dec("E2eScal.Gen.vi_unmarshal_accept_main_g", "E2eScal.vi_unmarshal_reject_len_main",
                                  None, None, None, None, "E2eScal.WitVi.vi_accept_runs", "E2eScal.WitViR.vir_runs"),
}
ENCODERS = {  # MarshalSSZTo: sufficient-capacity fast path, rejects, growslice paths, witnesses
    (V1A, "Checkpoint"): dict(fast=["E2e.cp_e2e_marshal_main"],
                              rejects=["E2e.cp_e2e_marshal_reject_main", "E2e.cp_e2e_marshal_reject_cover"],
                              grow=["E2e.cp_e2e_marshal_grow_main", "E2e.cp_e2e_marshal_grow2_main",
                                    "E2e.cp_e2e_marshal_grow_any_main"],
                              witness=["E2e.WitCpM.cpm_runs_empty", "E2e.WitCpMR.cpmr_runs", "E2e.WitCpG.cpg_runs"]),
    (V1A, "BeaconBlockHeader"): dict(fast=["E2eScal.Bh.bh_e2e_marshal_main"],
                                     rejects=["E2eScal.Bh.bh_e2e_marshal_reject1_main",
                                              "E2eScal.Bh.bh_e2e_marshal_reject2_main",
                                              "E2eScal.Bh.bh_e2e_marshal_reject3_main"],
                                     grow=[], witness=["E2eScal.WitBhM.bhm_runs_empty"]),
    (V1A, "Eth1Data"): dict(fast=["E2eScal.E1.e1_e2e_marshal_main"], rejects=[], grow=[],
                            witness=["E2eScal.WitE1M.e1m_runs_empty"]),
}
SIZERS = {(V1A, "Checkpoint"): dict(main=["E2e.cp_e2e_size_main"], witness=["E2e.WitCpS.cps_runs"])}

DEC_PARTS = ["accept", "reject", "spec_k", "reject_size_spec", "reject_complete", "codec", "witness_accept",
             "witness_reject"]
WHAT_COMPLETE_EXCLUDES = [
    "morestack paths (the `jbe` to `runtime.morestack_noctxt` at entry)",
    "`runtime.writeBarrier` != 0 (every accept theorem assumes the flag word is 0)",
    "runtime callee bodies (makeslice / memmove / growslice / newobject / fmt.errorf: contract hypotheses, "
    "MakesliceC / MemmoveC / ...)",
    "callee error returns (the `fmt.Errorf` wrap paths of delegated fields; `reject_complete` covers the size path "
    "condition only)",
    "growslice / T-7 (encoder capacity growth beyond the listed theorems)",
    "x86-64 hardware execution (semantics = Kraken's model of the amd64 instructions; no hardware run)",
]


def names():
    out = []
    for row in DECODERS.values():
        for k in DEC_PARTS:
            v = row[k]
            out += v if isinstance(v, list) else ([v] if v else [])
    for row in list(ENCODERS.values()) + list(SIZERS.values()):
        for v in row.values():
            out += v
    return list(dict.fromkeys(out))


def code_constants():
    """Lean code constant (full name) -> normalized function key `pkg_with_underscores.Type.Method`."""
    m = {}
    pat = re.compile(r'^def (\w+) : Program := include_x64_rt "([^"]+)"', re.M)
    for d in ("E2e", "E2eAd", "E2eScal"):
        for f in sorted((KR / "lean" / d).glob("*.lean")):
            t = f.read_text()
            ns = re.search(r"^namespace ([\w.]+)", t, re.M)
            for name, path in pat.findall(t):
                full = (ns.group(1) + "." if ns else "") + name
                m[full] = pathlib.Path(path).name[:-2] if path.endswith(".S") else pathlib.Path(path).name
    return m


def run(decls_p, md_p, json_p):
    fails = []
    funcs = json.load(open(KR / "prysm/go1.26.10/functions.json"))["functions"]
    gate = json.load(open(KR / "prysm/go1.26.10/e2e/axioms-gate.json"))
    raw = open(decls_p).read().split("\n")
    if not any(l.startswith("# inventory_decls v1") for l in raw):
        print(f"FAIL {decls_p}: no inventory_decls header")
        return 1
    raw = raw[next(i for i, l in enumerate(raw) if l.startswith("# inventory_decls v1")):]
    lines = [l.split("\t") for l in raw if l.strip()]
    bad = [l for l in lines[1:] if len(l) != 5]
    if bad:
        print(f"FAIL {decls_p}: malformed rows {bad[:3]}")
        return 1
    header = lines[0][0] if lines and lines[0][0].startswith("#") else None
    D = {r[0]: dict(kind=r[1], axioms=r[2], programs=r[3], refs=r[4]) for r in lines if not r[0].startswith("#")}
    want = names()
    for n in want:
        if n not in D:
            fails.append(f"{n}: not in {decls_p} (run inventory_decls.lean on the names of `inventory.py names`)")
        elif D[n]["kind"] != "theorem":
            fails.append(f"{n}: {D[n]['kind']} (a theorem named in the mapping is absent from the tree)")
        else:
            ax = set() if D[n]["axioms"] == "-" else set(D[n]["axioms"].split(","))
            if not ax <= STD:
                fails.append(f"{n}: non-standard axioms {sorted(ax - STD)}")
    cc = code_constants()
    fn_by_key = {re.sub(r"\(\*?(\w+)\)", r"\1", f["symbol"]).replace("/", "_").replace("-", "_"): f for f in funcs}

    def progs(n):
        p = D.get(n, {}).get("programs", "-")
        return [] if p == "-" else p.split(",")

    def refs(n):
        r = D.get(n, {}).get("refs", "-")
        return [] if r == "-" else r.split(",")

    def symkey(pkg, typ, meth):
        return f"{pkg}.{typ}.{meth}".replace("/", "_").replace("-", "_")

    def code_ok(n, pkg, typ, meth):
        k = symkey(pkg, typ, meth)
        hits = [c for c in progs(n) if cc.get(c) == k]
        if not hits:
            fails.append(f"{n}: no code constant of {k} in its type (programs: {progs(n)})")
        return bool(hits)

    rows = {}
    for (pkg, typ), r in DECODERS.items():
        st = {}
        for part in DEC_PARTS:
            v = r[part]
            st[part] = bool(v)
        for part in ("accept", "reject", "spec_k", "reject_size_spec"):
            if r[part] and r[part] in D:
                code_ok(r[part], pkg, typ, "UnmarshalSSZ")
        for part, target in (("witness_accept", "accept"), ("witness_reject", "reject"), ("spec_k", "accept"),
                             ("reject_size_spec", "reject")):
            if r[part] and r[target] and r[part] in D and r[target] not in refs(r[part]):
                fails.append(f"{r[part]}: does not use {r[target]} (refs: {refs(r[part])})")
        missing = [p for p in DEC_PARTS if not st[p]]
        state = "complete" if not missing else ("partial" if len(missing) < len(DEC_PARTS) else "none")
        rows[(pkg, typ, "UnmarshalSSZ")] = dict(state=state, missing=missing,
                                                theorems={p: r[p] for p in DEC_PARTS if r[p]}, note=r["note"])
    for (pkg, typ), r in ENCODERS.items():
        for n in r["fast"] + r["rejects"] + r["grow"]:
            if n in D:
                code_ok(n, pkg, typ, "MarshalSSZTo")
        rows[(pkg, typ, "MarshalSSZTo")] = dict(state="fast path" if r["fast"] else "none", missing=[],
                                                theorems=r, note="")
    for (pkg, typ), r in SIZERS.items():
        for n in r["main"]:
            if n in D:
                code_ok(n, pkg, typ, "SizeSSZ")
        rows[(pkg, typ, "SizeSSZ")] = dict(state="proved", missing=[], theorems=r, note="")
    for (pkg, typ, meth) in rows:
        if symkey(pkg, typ, meth) not in fn_by_key:
            fails.append(f"mapping row {pkg}.{typ}.{meth}: no such function in functions.json")
    if gate.get("verdict") != "PASS":
        fails.append(f"committed axioms gate verdict {gate.get('verdict')}")
    if fails:
        for f in fails:
            print("FAIL", f)
        return 1

    # ---------------------------------------------------------------- totals
    meths = {}
    for f in funcs:
        meths.setdefault(f["method"], []).append(f)
    table = []
    started_types = {(p, t) for (p, t, _) in rows}
    for f in funcs:
        if f["type"] is None:
            continue
        key = (f["package"], f["type"], f["method"])
        r = rows.get(key)
        if r is None:
            state = "not started" if (f["package"], f["type"]) not in started_types else "none"
            r = dict(state=state, missing=[], theorems={}, note="")
        table.append(dict(symbol=f["symbol"], package=f["package"], type=f["type"], method=f["method"],
                          kind=f["kind"], **r))
    dec_rows = [t for t in table if t["method"] == "UnmarshalSSZ"]
    tot = dict(
        functions_total=len(funcs),
        by_method={m: len(v) for m, v in sorted(meths.items())},
        hash_tree_root_functions_in_target=sum(1 for f in funcs if f["method"].startswith("HashTreeRoot")),
        decoders=dict(complete=sum(t["state"] == "complete" for t in dec_rows),
                      partial=sum(t["state"] == "partial" for t in dec_rows),
                      none=sum(t["state"] in ("none", "not started") for t in dec_rows)),
        encoders=dict(fast_path=sum(t["method"] == "MarshalSSZTo" and t["state"] == "fast path" for t in table),
                      none=sum(t["method"] == "MarshalSSZTo" and t["state"] != "fast path" for t in table)),
        marshal_ssz=dict(proved=0, none=len(meths.get("MarshalSSZ", []))),
        size_ssz=dict(proved=sum(t["method"] == "SizeSSZ" and t["state"] == "proved" for t in table),
                      none=sum(t["method"] == "SizeSSZ" and t["state"] != "proved" for t in table)),
        hash_tree_root=dict(proved=0),
    )
    flat = {t: rows[(V1A, t, "UnmarshalSSZ")]["state"] for t in FLAT16}
    tot["flat_population"] = FLAT16
    tot["flat_population_decoders_complete"] = f"{sum(v == 'complete' for v in flat.values())}/{len(FLAT16)}"
    tot["flat_population_not_complete"] = {t: rows[(V1A, t, "UnmarshalSSZ")]["missing"] for t, v in flat.items()
                                           if v != "complete"}
    tot["m_flat_dec_reached"] = all(v == "complete" for v in flat.values())
    tot["nested"] = {t: rows[(V1A, t, "UnmarshalSSZ")]["state"] for t in NESTED}
    out = dict(schema="fvkraken.inventory/1", source="gen/tools/inventory.py", decls_header=header,
               axioms_gate=dict(verdict=gate["verdict"], declarations=gate["declarations"]),
               definition_complete="decoder: accept + size reject + spec alignment (accept_spec_k, reject_size_spec, "
               "reject_complete) + Desc codec equality / correspondence + accept witness + reject witness, all "
               "kernel-checked theorems with standard axioms; accept / reject / spec theorems keyed to the function by "
               "the code constant in their type; witnesses and spec theorems use the mapped accept / reject theorem",
               complete_does_not_include=WHAT_COMPLETE_EXCLUDES, totals=tot, functions=table)
    json.dump(out, open(json_p, "w"), indent=1)
    md = ["# Verified inventory of the pinned target's SSZ functions", "",
          "Generated by `gen/tools/inventory.py` (do not edit); input: `prysm/go1.26.10/functions.json`, the "
          "committed axioms gate record, the code constants of `lean/`, and the output of "
          "`gen/tools/inventory_decls.lean` on the built tree. Target: the Go 1.26.10 ELF of `prysm/go1.26.10/` "
          "(sha256 in `build-ids.txt`). The Go 1.26.3 phase work is a different binary and is not counted here.", "",
          f"Declarations header: `{header}`. Axioms gate: {gate['verdict']}, {gate['declarations']} declarations.", "",
          "## Totals", "",
          f"- Functions in the target (`functions.json`): {tot['functions_total']} "
          f"({', '.join(f'{m} {n}' for m, n in tot['by_method'].items())}).",
          f"- Decoders (`UnmarshalSSZ`): complete {tot['decoders']['complete']}, partial {tot['decoders']['partial']}, "
          f"none {tot['decoders']['none']}.",
          f"- Encoders (`MarshalSSZTo`): with a fast-path theorem {tot['encoders']['fast_path']}, none "
          f"{tot['encoders']['none']}. `MarshalSSZ`: none of {tot['marshal_ssz']['none']}.",
          f"- `SizeSSZ`: proved {tot['size_ssz']['proved']}, none {tot['size_ssz']['none']}.",
          f"- `HashTreeRoot*`: none proved; {tot['hash_tree_root_functions_in_target']} such functions are in "
          "`functions.json` (the dumped function set of the target).",
          f"- Flat fixed-size population (GEN5 plan, {len(FLAT16)} types): decoders complete "
          f"{tot['flat_population_decoders_complete']}; M-flat-dec reached: {tot['m_flat_dec_reached']}.",
          ]
    for t, miss in tot["flat_population_not_complete"].items():
        md.append(f"  - {t}: missing {', '.join(miss)}.")
    md += [f"- Nested: {', '.join(f'{t} {s}' for t, s in tot['nested'].items())} (not in the flat population).", "",
           "## What \"complete\" means here", "", out["definition_complete"] + ".", "",
           "It does NOT include:", ""] + [f"- {x}" for x in WHAT_COMPLETE_EXCLUDES] + [
           "", "## Functions with at least one theorem", "",
           "| function | state | missing | theorems |", "| --- | --- | --- | --- |"]
    for t in table:
        if t["state"] in ("not started", "none") and not t["theorems"]:
            continue
        th = "; ".join(f"{k}: {', '.join(v) if isinstance(v, list) else v}" for k, v in t["theorems"].items() if v)
        note = f" ({t['note']})" if t.get("note") else ""
        md.append(f"| `{t['type']}.{t['method']}` ({t['package'].rsplit('/', 1)[-1]}) | {t['state']}{note} | "
                  f"{', '.join(t['missing']) or '-'} | {th} |")
    ns = sorted({(t["package"].rsplit("/", 1)[-1], t["type"]) for t in table if t["state"] == "not started"})
    md += ["", f"## Not started ({len(ns)} types, every method)", "",
           ", ".join(f"{p}.{t}" for p, t in ns), ""]
    open(md_p, "w").write("\n".join(md))
    print(json.dumps({k: tot[k] for k in ("functions_total", "decoders", "encoders", "size_ssz",
                                         "flat_population_decoders_complete", "m_flat_dec_reached")}))
    return 0


if __name__ == "__main__":
    sys.dont_write_bytecode = True
    if len(sys.argv) == 3 and sys.argv[1] == "names":
        open(sys.argv[2], "w").write("\n".join(names()) + "\n")
        sys.exit(0)
    if len(sys.argv) == 5 and sys.argv[1] == "run":
        sys.exit(run(*sys.argv[2:5]))
    print(__doc__)
    sys.exit(2)
