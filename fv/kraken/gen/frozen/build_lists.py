#!/usr/bin/env python3
"""One-time builder of the two frozen lists (P2). Not part of the generator.

Usage: build_lists.py <repo-root> [--out DIR]
Writes fv/kraken/gen/frozen/THEOREMS.json and fv/kraken/gen/frozen/ASSUMPTIONS.json.

After the commit that adds them, the two JSON files are frozen:
- a change is a separate commit, with the reason in the run OUTBOX;
- the generator (fv/kraken/gen/**, P4 on) never writes them and never imports
  this file; gen/tests check that the generator output directory is not here.
Inputs: the generated Go of the 9 hand-made types (fv/kraken/target), the
698c202 Prysm outputs (fv/kraken/prysm/_generated/mainnet), the inventory
(fv/kraken/prysm/inventory.json) and the hand mapping below (read from
AXIOMS.txt names and theorem doc comments; P5 recomputes links from resolved
Lean declarations). Python 3 standard library only. Run with python3 -I.
"""
import hashlib
import json
import os
import sys

sys.dont_write_bytecode = True
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
import obligations  # noqa: E402  (site enumerator; shares no code with the generator)

FUNCS = ("UnmarshalSSZ", "MarshalSSZTo", "SizeSSZ")

KINDS = [
    {"id": "accept", "function": "UnmarshalSSZ",
     "statement": "EthLib -> machine code: for every input bytes b that the EthLib decoder of the type accepts with value v, "
                  "the machine code returns err = nil and the receiver memory holds the Go value of v; frame R preserved.",
     "hand_example": "lu_accept_main"},
    {"id": "reject", "function": "UnmarshalSSZ", "per": "error return site (Go source)",
     "statement": "for every input that reaches the site (its path condition), the machine code returns a non-nil error "
                  "interface (the exact global or the fmt/validator result under its contract); frame R preserved.",
     "hand_example": "lu_reject_toobig_main"},
    {"id": "reject_complete", "function": "UnmarshalSSZ",
     "statement": "decoder soundness (machine code accepts => EthLib accepts): every input that the EthLib decoder "
                  "rejects reaches some error return site (the path conditions of the reject sites cover the EthLib "
                  "reject set), so the machine code returns a non-nil error on it. Together with accept this gives "
                  "accepted set of the machine code = accepted set of EthLib (F1-class defects are visible).",
     "hand_example": "bv_spec_accepts_iff (EthLib side only; the join with the reject sites is a doc comment)",
     "added": "review phase1c-r1 S1 (orchestrator decision a), separate commit after P2"},
    {"id": "reject_spec", "function": "UnmarshalSSZ", "per": "error return site whose condition is a spec-level reject",
     "statement": "the EthLib decoder rejects every input that satisfies the site's path condition.",
     "hand_example": "sc_spec_rejects_bool"},
    {"id": "unreachable_mc", "function": "UnmarshalSSZ", "per": "Go-source error return site that the machine code does not contain",
     "statement": "the included machine code of the function has no path to the site's error return (for example the "
                  "callee call was inlined and its only failure is excluded by the caller's own checks): proved from the "
                  "included code. The site's reject row stays in the list (Go-source rule); this row never closes it as a "
                  "reject path and is counted in its own column.",
     "hand_example": None,
     "added": "INBOX 005/009 (orchestrator, provisional until the user confirms; OUTBOX 002 item 1), frozen-list commit after the fix3 stage A rebase"},
    {"id": "marshal", "function": "MarshalSSZTo",
     "statement": "for every Go value in the EthLib domain of the type and every dst, MarshalSSZTo returns "
                  "(dst ++ EthLib.encode v, nil); input, prefix, frame R, rsp after return and preserved registers stated.",
     "hand_example": "lu_marshal_main"},
    {"id": "marshal_reject", "function": "MarshalSSZTo", "per": "error return site (Go source)",
     "statement": "for every Go value that reaches the site, the machine code returns (nil, non-nil error); frame R preserved.",
     "hand_example": "lu_marshal_reject_main"},
    {"id": "size", "function": "SizeSSZ",
     "statement": "SizeSSZ returns the length of EthLib.encode v; memory unchanged (memory identity) and rsp/preserved registers stated.",
     "hand_example": "lu_size_main"},
    {"id": "compose_hupd", "function": "UnmarshalSSZ;MarshalSSZTo",
     "statement": "decode then marshal: the state after a successful UnmarshalSSZ satisfies the MarshalSSZTo premise and the "
                  "result is the input bytes (theorem over the two main theorems).",
     "hand_example": "lu_unmarshal_then_marshal"},
    {"id": "compose_witness", "function": "UnmarshalSSZ;MarshalSSZTo",
     "statement": "one concrete Host that satisfies every premise of compose_hupd (whole composition witness).",
     "hand_example": "WitLuComp"},
    {"id": "compose_caller", "function": "UnmarshalSSZ;MarshalSSZTo",
     "statement": "the two calls run as real caller instructions (not only the hupd glue). REPORT 7.9 item 3.",
     "hand_example": None},
]

PER_THEOREM = [
    "every main theorem has a witness *_runs on a concrete Host that satisfies all premises; variable lengths: empty, 1, max; inner lengths for nested lists (empty, 1, max)",
    "postcondition keeps input, prefix, frame R, rsp after return and preserved registers; never ends in `⋆ True` for live resources; dead callee stack is classified (memory identity / explicit preservation / dropped as True)",
    "label freshness and global addresses are premises (link check confirms them on the real ELF)",
    "no sorry, admit, new axiom, native_decide, bv_decide; axioms only propext, Classical.choice, Quot.sound",
    "statement is produced from the frozen kind text above; it may be stronger, never weaker",
]

COMPLETION = [
    "1 contract or theorem", "2 witness on a concrete Host (empty/1/max)", "3 machine-code theorem",
    "4 link check PASS (on the ELF of this namespace)", "5 negative test: a mutation fails inside the designated theorem and its control passes",
    "6 Go value check of the witness (layout from the ELF's abi.Type when fix3 data include is available)",
]

# Existing hand theorems per (type, function, kind[, site-ordinal-among-same-kind]).
HAND = {
    ("Scalars", "UnmarshalSSZ", "accept"): ["sc_accept_main"],
    # reject_complete: only EthLib-side characterizations exist; such rows get hand_status "partial"
    ("BitVec", "UnmarshalSSZ", "reject_complete"): ["bv_spec_accepts_iff"],
    ("Checkpoint", "UnmarshalSSZ", "reject_complete"): ["cp_spec_accepts_iff"],
    ("AttestationData", "UnmarshalSSZ", "reject_complete"): ["ad_spec_accepts_iff"],
    ("ListU64", "UnmarshalSSZ", "reject_complete"): ["lu_spec_accepts_iff"],
    ("Nested", "UnmarshalSSZ", "reject_complete"): ["ne_spec_accepts_iff"],
    ("Scalars", "UnmarshalSSZ", "size-fixed"): ["sc_reject_size_main"],
    ("Scalars", "UnmarshalSSZ", "bool-range"): ["sc_reject_bool_main", "sc_reject_bool_err"],
    ("Scalars", "UnmarshalSSZ", "reject_spec:bool-range"): ["sc_spec_rejects_bool"],
    ("Scalars", "MarshalSSZTo", "marshal"): ["sc_marshal_main"],
    ("Scalars", "SizeSSZ", "size"): ["sc_size_main"],
    ("Scalars", "-", "compose_hupd"): ["sc_unmarshal_then_marshal"],
    ("Scalars", "-", "compose_witness"): ["WitScComp"],
    ("FixedVec", "UnmarshalSSZ", "accept"): ["fv_accept_main"],
    ("FixedVec", "UnmarshalSSZ", "size-fixed"): ["fv_reject_size_main"],
    ("FixedVec", "MarshalSSZTo", "marshal"): ["fv_marshal_main"],
    ("FixedVec", "MarshalSSZTo", "vector-length#2"): ["fv_marshal_reject_main"],
    ("FixedVec", "SizeSSZ", "size"): ["fv_size_main"],
    ("ListU64", "UnmarshalSSZ", "accept"): ["lu_accept_main"],
    ("ListU64", "UnmarshalSSZ", "size-short"): ["lu_reject_short_main"],
    ("ListU64", "UnmarshalSSZ", "offset-first"): ["lu_reject_offset_main"],
    ("ListU64", "UnmarshalSSZ", "list-misaligned"): ["lu_reject_misaligned_main"],
    ("ListU64", "UnmarshalSSZ", "list-too-big"): ["lu_reject_toobig_main"],
    ("ListU64", "MarshalSSZTo", "marshal"): ["lu_marshal_main"],
    ("ListU64", "MarshalSSZTo", "list-length"): ["lu_marshal_reject_main"],
    ("ListU64", "SizeSSZ", "size"): ["lu_size_main"],
    ("ListU64", "-", "compose_hupd"): ["lu_unmarshal_then_marshal"],
    ("ListU64", "-", "compose_witness"): ["WitLuComp"],
    ("BitVec", "UnmarshalSSZ", "accept"): ["bv_accept_main"],
    ("BitVec", "UnmarshalSSZ", "size-fixed"): ["bv_reject_size_main"],
    ("BitVec", "UnmarshalSSZ", "bitvector-padding"): ["bv_reject_padding_main"],
    ("BitVec", "MarshalSSZTo", "marshal"): ["bv_marshal_main"],
    ("BitVec", "SizeSSZ", "size"): ["bv_size_main"],
    ("BitVec", "-", "compose_hupd"): ["bv_unmarshal_then_marshal"],
    ("Nested", "UnmarshalSSZ", "accept"): ["ne_accept_main"],
    ("Nested", "UnmarshalSSZ", "size-short"): ["ne_reject_short_main"],
    ("Nested", "UnmarshalSSZ", "offset-first"): ["ne_reject_offset_main"],
    ("Nested", "MarshalSSZTo", "marshal"): ["ne_marshal_main"],
    ("Nested", "SizeSSZ", "size"): ["ne_size_main"],
    ("ListC", "UnmarshalSSZ", "accept"): ["lc_accept_main", "lc_accept_empty_main"],
    ("ListC", "UnmarshalSSZ", "size-short"): ["lc_reject_short_main"],
    ("ListC", "UnmarshalSSZ", "offset-first"): ["lc_reject_offset_main"],
    ("ListC", "UnmarshalSSZ", "listc-offset-zero"): ["lc_reject_zero_main"],
    ("ListC", "UnmarshalSSZ", "listc-first-offset-past"): ["lc_reject_past_main"],
    ("ListC", "UnmarshalSSZ", "listc-tail"): ["lc_reject_tail_main"],
    ("ListC", "UnmarshalSSZ", "listc-offset-order"): ["lc_reject_offset_order_main"],
    ("ListC", "MarshalSSZTo", "marshal"): ["lc_marshal_main"],
    ("ListC", "SizeSSZ", "size"): ["lc_size_main"],
    ("BitL", "UnmarshalSSZ", "accept"): ["bl_accept_main"],
    ("BitL", "UnmarshalSSZ", "size-short"): ["bl_reject_short_main"],
    ("BitL", "UnmarshalSSZ", "offset-first"): ["bl_reject_offset_main"],
    ("BitL", "UnmarshalSSZ", "bitlist-invalid"): ["bl_reject_invalid_main"],
    ("BitL", "MarshalSSZTo", "marshal"): ["bl_marshal_main"],
    ("BitL", "MarshalSSZTo", "bitlist-invalid"): ["bl_marshal_reject_main"],
    ("BitL", "SizeSSZ", "size"): ["bl_size_main"],
    ("Checkpoint", "UnmarshalSSZ", "accept"): ["cp_accept_main"],
    ("Checkpoint", "UnmarshalSSZ", "size-fixed"): ["cp_reject_size_main"],
    ("Checkpoint", "MarshalSSZTo", "marshal"): ["cp_marshal_main"],
    ("Checkpoint", "MarshalSSZTo", "vector-length"): ["cp_marshal_reject_main"],
    ("Checkpoint", "SizeSSZ", "size"): ["cp_size_main"],
    ("AttestationData", "UnmarshalSSZ", "accept"): ["ad_accept_main"],
    ("AttestationData", "UnmarshalSSZ", "size-fixed"): ["ad_reject_size_main"],
    ("AttestationData", "MarshalSSZTo", "marshal"): ["ad_marshal_main"],
    ("AttestationData", "SizeSSZ", "size"): ["ad_size_main"],
}
CALLEE_SPECS = {"ssz.ValidateBitvector": ["vbv_accept_main", "vbv_reject_pad_main"]}
# Go-source sites with no counterpart in the machine code (P5 COMPARE.md: the decoder does not reference
# "Source: %w" / "Target: %w"; Checkpoint.UnmarshalSSZ is inlined and fails only on size, which the caller fixes).
UNREACHABLE_MC = {("AttestationData", "UnmarshalSSZ", 2): "c.Source.UnmarshalSSZ(sszSlice3) on an exact 40-byte slice; inlined, no error path",
                  ("AttestationData", "UnmarshalSSZ", 3): "c.Target.UnmarshalSSZ(sszSlice4) on an exact 40-byte slice; inlined, no error path"}
STATIC_FALSE = {("FixedVec", "MarshalSSZTo", 1): "len(c.R) on a Go array [32]byte is a constant 32; the compiler removes the branch"}
SPEC_LEVEL = {"size-fixed", "size-short", "offset-first", "offset-past-or-order", "offset-order", "offset-past-size",
              "bool-range", "list-misaligned", "list-too-big", "listc-offset-zero", "listc-offset-misaligned",
              "listc-first-offset-past", "listc-offset-past", "listc-offset-order", "listc-tail", "bitlist-invalid",
              "bitvector-padding"}


def instantiate(fn_sites, types, hand=None):
    """Obligation rows for the given types from the enumerated sites."""
    rows = []
    by = {(f["type"], f["method"]): f for f in fn_sites}
    for t in types:
        def add(func, kind, site=None, extra=None):
            r = {"id": f"{t}.{func}.{kind}" + (f".r{site['site']}" if site else ""), "type": t, "function": func,
                 "obligation": kind}
            if site:
                r.update(site=site["site"], line=site["line"], site_kind=site["kind"], guard=site["guard"], ret=site["return"])
            if extra:
                r.update(extra)
            if hand is not None:
                r["hand_theorems"] = []
            rows.append(r)
            return r
        add("UnmarshalSSZ", "accept")
        add("UnmarshalSSZ", "reject_complete")
        u = by.get((t, "UnmarshalSSZ"), {"reject_sites": []})
        for s in u["reject_sites"]:
            add("UnmarshalSSZ", "reject", s)
            if hand is not None and (t, "UnmarshalSSZ", s["site"]) in UNREACHABLE_MC:
                add("UnmarshalSSZ", "unreachable_mc", s, {"reason": UNREACHABLE_MC[(t, "UnmarshalSSZ", s["site"])]})
            if s["kind"] in SPEC_LEVEL:
                add("UnmarshalSSZ", "reject_spec", s)
        add("MarshalSSZTo", "marshal")
        m = by.get((t, "MarshalSSZTo"), {"reject_sites": []})
        for s in m["reject_sites"]:
            extra = {"statically_false": STATIC_FALSE[(t, "MarshalSSZTo", s["site"])]} if (t, "MarshalSSZTo", s["site"]) in STATIC_FALSE else None
            add("MarshalSSZTo", "marshal_reject", s, extra)
        add("SizeSSZ", "size")
        for k in ("compose_hupd", "compose_witness", "compose_caller"):
            add("-", k)
    if hand is not None:
        seen = {}
        for r in rows:
            if r["obligation"] == "unreachable_mc":
                names = hand.get((r["type"], r["function"], f"unreachable_mc#{r['site']}"), [])
            elif r["obligation"] in ("reject", "marshal_reject", "reject_spec"):
                key = r["site_kind"]
                n = seen.setdefault((r["type"], r["function"], r["obligation"], key), 0) + 1
                seen[(r["type"], r["function"], r["obligation"], key)] = n
                if r["obligation"] == "reject_spec":
                    names = hand.get((r["type"], r["function"], "reject_spec:" + key), [])
                else:
                    names = hand.get((r["type"], r["function"], f"{key}#{n}"))
                    if names is None:
                        names = hand.get((r["type"], r["function"], key), []) if n == 1 else []
            else:
                func = r["function"]
                names = hand.get((r["type"], func, r["obligation"]), [])
            r["hand_theorems"] = names
            if r["obligation"] == "reject_complete":
                r["hand_status"] = ("partial: EthLib accepted set characterized; no theorem joins it with the reject sites"
                                    if names else "open")
    return rows


def main():
    root = sys.argv[1]
    # --out DIR writes the two files elsewhere (used by test_frozen.py to compare with the committed bytes)
    out_dir = sys.argv[sys.argv.index("--out") + 1] if "--out" in sys.argv else None
    k = f"{root}/fv/kraken"
    hand_types = ["Scalars", "FixedVec", "ListU64", "BitVec", "Nested", "ListC", "BitL", "Checkpoint", "AttestationData"]
    hs = obligations.sites([f"{k}/target/types.ssz.go", f"{k}/target/types1b.ssz.go", f"{k}/target/prysm/types.ssz.go"])
    hand_rows = instantiate(hs, hand_types, HAND)
    hand_main = [r for r in hand_rows if r["obligation"] != "unreachable_mc"]
    hand_unr = [r for r in hand_rows if r["obligation"] == "unreachable_mc"]
    mapped = sorted({n for r in hand_rows for n in r["hand_theorems"]} | {n for v in CALLEE_SPECS.values() for n in v})
    all_hand = sorted({n for v in HAND.values() for n in v} | {n for v in CALLEE_SPECS.values() for n in v})
    inv = json.load(open(f"{k}/prysm/inventory.json"))
    gen_dir = f"{k}/prysm/_generated/mainnet"
    ps = obligations.sites(sorted(f"{gen_dir}/{f}" for f in os.listdir(gen_dir)))
    in_types = sorted(t["name"] for t in inv["types"] if t["scope"] == "in")
    out_types = sorted(t["name"] for t in inv["types"] if t["scope"] == "out")
    pr_rows = instantiate(ps, in_types)
    src_hash = {os.path.relpath(p, root): hashlib.sha256(open(p, "rb").read()).hexdigest() for p in
                [f"{k}/target/types.ssz.go", f"{k}/target/types1b.ssz.go", f"{k}/target/prysm/types.ssz.go",
                 f"{k}/prysm/inventory.json"] + sorted(f"{gen_dir}/{f}" for f in os.listdir(gen_dir))}
    from collections import Counter
    th = {
        "schema": "fvphase1c.theorems/1",
        "status": "frozen at the commit that adds this file (P2). Change only by a separate commit with the reason in the run OUTBOX. "
                  "The generator never writes this file.",
        "provisional_scope": "the Prysm part covers the types classed 'in' by the first-pass (provisional) inventory; a class change is a list change",
        "counting_rule": "reject = one non-nil error return site of the Go source of UnmarshalSSZ / MarshalSSZTo (REPORT.md section 2 rule); "
                         "site kinds from fv/kraken/gen/obligations.py",
        "obligation_kinds": KINDS,
        "per_theorem_requirements": PER_THEOREM,
        "completion_elements": COMPLETION,
        "callee_function_specs": CALLEE_SPECS,
        "sources_sha256": src_hash,
        "hand_case": {"types": hand_types, "obligations": hand_rows},
        "prysm": {"preset": "mainnet", "types_in": in_types, "types_out_listed_only": out_types, "obligations": pr_rows},
        "counts": {
            "hand_obligations": len(hand_main),
            "hand_obligations_by_kind": dict(sorted(Counter(r["obligation"] for r in hand_main).items())),
            "hand_obligations_with_theorem": sum(bool(r["hand_theorems"]) for r in hand_main),
            "hand_obligations_with_theorem_partial": sum(bool(r["hand_theorems"]) and r.get("hand_status", "").startswith("partial")
                                                         for r in hand_main),
            "hand_obligations_with_full_theorem": sum(bool(r["hand_theorems"]) and not r.get("hand_status", "").startswith("partial")
                                                      for r in hand_main),
            "hand_obligations_open": sum(not r["hand_theorems"] for r in hand_main),
            "hand_unreachable_mc": {"rows": len(hand_unr), "with_theorem": sum(bool(r["hand_theorems"]) for r in hand_unr),
                                    "note": "own column (not in hand_obligations); never a closed reject path"},
            "hand_main_theorems_mapped": len([n for n in mapped if n.endswith("_main")]),
            "hand_names_in_table_not_mapped": sorted(set(all_hand) - set(mapped)),
            "prysm_types_in": len(in_types),
            "prysm_obligations": len(pr_rows),
            "prysm_obligations_by_kind": dict(sorted(Counter(r["obligation"] for r in pr_rows).items())),
            "prysm_reject_sites_by_kind": dict(sorted(Counter(r["site_kind"] for r in pr_rows if r["obligation"] in ("reject", "marshal_reject")).items())),
        },
    }
    asm = {
        "schema": "fvphase1c.assumptions/1",
        "status": th["status"],
        "rule": "A generated theorem may use only these premise classes. A premise outside this list is a new trust assumption: stop and report.",
        "revision": "2: review phase1c-r1 S2 (Go 1.26.10 re-check condition, model per instance, API version). Revision 1 = 0532cbd",
        "classes": [
            {"id": "callee-contract", "what": "runtime callee as a hypothesis in Kraken form (CONTRACTS.md section 2): MakesliceC, MemmoveC, GrowsliceC, NewobjectC, ConvT64C, FmtErrorfNilC, FmtErrorfWC, FmtErrorfDWC, ValidateBitlistC, ValidateBitlistErrC",
             "conditions": "quantified over all states, return addresses and frames; argument conditions, budgets, scratch S and spill as in CONTRACTS.md; joint satisfiability (joint_models)",
             "go_version": "CONTRACTS.md reads every contract against Go 1.26.3 (ABIInternal, nextslicecap, fmt allocation, budgets). In the Go 1.26.10 namespace (fv/kraken/prysm/go1.26.10) each contract is an UNCONFIRMED ASSUMPTION until it is re-read against the Go 1.26.10 runtime source and the re-reading is recorded; until then a theorem that uses it states that",
             "model_per_instance": "a model and a witness are needed per contract instance (each element size esz, object size sz, fmt format string and argument types, type descriptor), as in the hand case (bump_newobject16/24/32). An instance without a model is classed 'missing contract'",
             "new_contract": "a new runtime callee (for example runtime.moveSliceNoCapNoScan, a new fmt format shape) needs its own entry, model and witness; it is a list change"},
            {"id": "function-spec", "what": "a callee that is itself proved (generated method of another type, ssz.ValidateBitvector): a spec derived from its theorem (*_holds)",
             "conditions": "the spec's own contracts propagate to the caller's completion row"},
            {"id": "hand-written-callee", "what": "a hand-written Go method called by generated code (Prysm consensus-types/primitives SSZ methods)",
             "conditions": "allowed only as a function spec proved from its own machine code, or as a named contract listed here with a model; not yet present; adding one is a list change"},
            {"id": "frame", "what": "frame R (any separated resource) preserved by every main theorem", "conditions": "explicit in the conclusion"},
            {"id": "runtime-owned-memory", "what": "heap budget `avail`, runtime-owned blocks in contracts", "conditions": "numbers budgets, not physical address space claims (REPORT 7.2)"},
            {"id": "label-freshness", "what": "LabelsFresh premise", "conditions": "checked on the real layout by the link check; on concrete Hosts by Lean theorems"},
            {"id": "global-addresses", "what": "label addresses of globals (ssz.Err*, runtime.writeBarrier, runtime.staticuint64s, itabs, type descriptors)", "conditions": "premise; link check / fix3 data include confirms on the ELF"},
            {"id": "global-values", "what": "ssz.Err* values after package init: e0 != 0 and the itab word readable", "conditions": "premise; must be connected to the witness (astra finding 4); a nil global is not allowed in a reject witness"},
            {"id": "rodata-data-include", "what": "rodata strings, itabs, type descriptors, staticuint64s as bytes from the ELF (fix3 data include, Fk.Data.<id>)",
             "conditions": "premise shape `Eq (bytes.At addr)`; bytes and addr come from Fk.Data only; hand constants are not allowed"},
            {"id": "stack-guard", "what": "g.stackguard0 (r14 + 16) < rsp", "conditions": "fast-path premise; callee stack growth is outside contracts"},
            {"id": "write-barrier-off", "what": "runtime.writeBarrier = 0 for the whole call", "conditions": "fast-path premise; GC during the call is outside"},
            {"id": "x15-zero", "what": "X15 = 0 (Go ABIInternal)", "conditions": "only where the hand case uses it (ListC empty accept); reject paths do not assume it"},
            {"id": "abi-arguments", "what": "Go ABIInternal amd64 argument registers and return slot", "conditions": "Go 1.26.3 ABIInternal for the hand case; Go 1.26.10 ABIInternal for the phase1c namespace, unconfirmed until re-read against the Go 1.26.10 source (as callee-contract)"},
            {"id": "separation", "what": "input, receiver, stack and output pairwise disjoint (⋆)", "conditions": "aliasing excluded; memmove overlap excluded"},
            {"id": "go-value-invariants", "what": "bool byte in {0,1}, len <= cap < 2^63, object size/alignment/padding", "conditions": "theorems may allow more; witnesses must be Go values (goval / later Lean predicate)"},
            {"id": "size-bounds", "what": "explicit size ranges in contracts", "conditions": "no quantification over all sizes and all frames (fv/AGENTS.md)"},
        ],
        "forbidden": ["sorry", "admit", "new axiom", "native_decide", "bv_decide", "hand-typed rodata/itab/type constants", "a premise that makes the conclusion vacuous (False derivable)", "dropping a live resource into `⋆ True` without classification"],
        "sources": ["fv/kraken/CONTRACTS.md", "fv/kraken/REPORT.md sections 3 and 7", "fv/AGENTS.md", "run shared/INCLUDE-API.json api_version 2 (fix3 d9cdb40, data include, approved stage A); gen/gen1c/include_adapter.py names the version in use"],
    }
    d = out_dir or f"{k}/gen/frozen"
    for name, obj in (("THEOREMS.json", th), ("ASSUMPTIONS.json", asm)):
        with open(f"{d}/{name}", "w") as f:
            json.dump(obj, f, indent=1, ensure_ascii=False)
            f.write("\n")
    print(json.dumps(th["counts"], indent=1))


if __name__ == "__main__":
    main()
