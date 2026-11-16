#!/usr/bin/env python3
"""Write fv/kraken/prysm/TYPES.md from the saved JSON. No number is typed by hand.

Usage: type_list_document.py <prysm-dir>
Inputs: inventory.json, go1.26.10/functions.json, go1.26.10/parser-result.json,
diff/generated-go-diff.json, go1.26.10/build-ids.txt.
Python 3 standard library only. Run with python3 -I.
"""
import json
import re
import sys
from collections import Counter

ABBR = {"ValidateBitlist": "VBl", "ValidateBitvector": "VBv", "convT64": "cT64", "fmt": "fmt",
        "generated method": "gen", "growslice": "grow", "hand-written primitives method": "hand",
        "makeslice": "mks", "memmove": "mm", "morestack_noctxt": "stk", "newobject": "new",
        "panic*": "pan", "write barrier": "wb", "moveSlice* (stack-backed result to heap)": "mvS",
        "runtime other": "rt?", "other": "oth?", "indirect": "ind"}
METHODS = ("MarshalSSZTo", "SizeSSZ", "UnmarshalSSZ")


def short(pkg):
    return pkg.replace("github.com/OffchainLabs/prysm/v7/", "")


def main():
    d = sys.argv[1]
    inv = json.load(open(f"{d}/inventory.json"))
    fn = json.load(open(f"{d}/go1.26.10/functions.json"))
    kp = json.load(open(f"{d}/go1.26.10/parser-result.json"))
    gd = json.load(open(f"{d}/diff/generated-go-diff.json"))
    bid = dict(l.split(": ", 1) for l in open(f"{d}/go1.26.10/build-ids.txt").read().splitlines() if ": " in l)
    c, fc = inv["counts"], fn["counts"]
    kps = {r["symbol"]: r for r in kp["functions"]}
    funcs = {(f["package"], f["type"], f["method"]): f for f in fn["functions"]}
    L = []
    w = L.append
    w("# Prysm Fulu type list")
    w("")
    w("`fv/kraken/gen/type_list_document.py` makes this file from the saved JSON. Do not change it by hand.")
    w("The program counts all numbers. The scope classification is a rule-based classification. It is not a proof.")
    w("")
    w("## 1. Summary")
    w("")
    w(f"- Inventory types: {c['inventory_types']} generated types. Fork config types: {c['fork_config_types']}. Fulu-reachable types: {c['fulu_reachable_types']} (generated {c['fulu_reachable_generated_types']}, hand-written {c['fulu_reachable_hand_written_types']}).")
    w(f"- In scope: {c['scope_in']}, out of scope: {c['scope_out']}. Reasons for out of scope: " +
      ", ".join(f"{k} {v}" for k, v in c["out_primary_reason"].items()) + ".")
    w(f"- For the generated Fulu-reachable types only: in scope {c['fulu_reachable_scope_in']}, out of scope {c['fulu_reachable_scope_out']}.")
    fsh = c["field_shape"]
    w("- \"In scope\" means that the scope rules did not remove the type. It does not mean that a proof is possible. It also does not mean that the type fits the hand proof patterns.")
    w(f"  The in-scope rule accepts these field shapes. The inventory types together have {fsh.get('vector[bytesN]', 0)} `vector[bytesN]` fields, {fsh.get('list[bytesN]', 0)} `list[bytesN]` fields "
      f"and {fsh.get('vector[uint64]', 0)} `vector[uint64]` fields. The depth is the inline depth (it does not follow delegation).")
    w("  The classification by what the proofs need is in `type-scope.md`.")
    w(f"- Hand-written delegate targets (`consensus-types/primitives`): {c['hand_written_delegate_types']}. Types that call them: {c['types_calling_hand_written']}.")
    w(f"- Generated functions: {fc['generated_functions_inventory']} (types × 3), instructions: {fc['generated_instructions']}, maximum for each function: {fc['max_instructions']}.")
    w(f"- Mnemonic level: {fc['generated_functions_all_supported']}/{fc['generated_functions_inventory']} generated functions use only names that the Kraken runtime parser accepts.")
    # an error message without its line number, for example `unsupported instruction: bsr`
    err_kinds = Counter(re.sub(r"^line \d+: ", "", r["error"]) for r in kp["errors"])
    ok_inv = kp["counts"].get("inventory: OK", 0)
    err_inv = kp["counts"].get("inventory: ERR", 0)
    w(f"- Parser run: {ok_inv} generated functions of the inventory types OK, {err_inv} ERR. Errors of all parsed functions by message: "
      + (", ".join(f"`{m}` {n}" for m, n in sorted(err_kinds.items())) or "none") + " (section 4).")
    w(f"- Differences from the committed Prysm files: {gd['totals']['blocks']} changed blocks, {gd['totals']['classified']} classified, {gd['totals']['unclassified']} not classified.")
    w(f"- Types with a different IR in the minimal preset: {c['minimal_differs']}. Types with a changed scope classification: {c['minimal_scope_changes']}.")
    w("")
    w("## 2. Fixed values")
    w("")
    w("| Item | Value |")
    w("| --- | --- |")
    w("| Prysm source, generator and runtime | The pins of `../README.md` section 2 |")
    w(f"| Target compilation | Cross-compiled for linux/amd64 with `{bid['go']}` (host binary), `{bid['target']}` |")
    w(f"| Host | {bid['host']} (generation is arm64 native. No x86-64 hardware) |")
    w(f"| ELF | sha256 `{bid['elf sha256']}`, {bid['elf size']} bytes. Not committed (`../README.md` section 3 tells how to build it again) |")
    w(f"| Reproducibility | Second build with an empty GOCACHE: sha256 `{bid['second build sha256']}` |")
    w("| Kraken / EthLib / Lean | `../lean/lake-manifest.json`, `../lean/lean-toolchain` |")
    w("")
    w("## 3. Method")
    w("")
    w("1. `gen/prysm-gen.sh` runs the generator in a temporary Prysm tree. The flags are the same as in Prysm `build/gen/ssz.go`.")
    w("2. The same script uses `gen/inventory-tool` to extract the IR of the front end of the generator itself (`config`, `TypeDefs`, `ParseTypeDef`, delegate interface set) as JSON.")
    w("3. `gen/type_inventory.py reduce` cuts the parts below delegated fields and makes `ir/ir-{mainnet,minimal}.json`.")
    w("4. `gen/type_inventory.py build` writes the sets, kinds, depths and scopes to `inventory.json`.")
    w("5. `gen/prysm-elf.sh` builds the ELF two times and extracts objdump and nm. `gen/keepalive.py` makes `main`.")
    w("6. `gen/mnemonics.py` counts the instructions, mnemonics and call kinds for each function (`go1.26.10/functions.json`).")
    w("7. `link/convert_objdump.py --norm` (read only) makes the `.S` files, and `gen/kraken-parser/ParserRun.lean` runs the Kraken runtime parser (`go1.26.10/parser-result.json`).")
    w("")
    for k, v in inv["definitions"].items():
        w(f"- `{k}`: {v}")
    w("")
    w("How we decide \"does Kraken accept it\":")
    w("")
    w(f"- Mnemonic level: the {len(fn['kraken_accepted_names'])} branch strings of `parseInstr` in `Kraken/X64/Parser/Basic.lean` of the fixed Kraken, and `j`/`set`/`cmov` + {len(fn['kraken_condition_codes'])} `parseCondCode?` condition codes. The {len(fn['conv_norm_forms'])} `convert_objdump.py` NORM forms count as `nop`.")
    w("- Parser level: `Kraken.X64.Parser.parse`, which `include_x64_code` uses, runs on each file. This is the verdict criterion.")
    w("- The semantics level (`kstep` and theorems) is not examined. This table is a classification, not a proof.")
    w("")
    w("## 4. Numbers")
    w("")
    w("| Item | Value |")
    w("| --- | --- |")
    for k, v in c.items():
        w(f"| `{k}` | {json.dumps(v, ensure_ascii=False)} |")
    for k in ("functions_dumped", "generated_functions_inventory", "generated_functions_not_inventory",
              "hand_written_functions", "missing_generated", "generated_instructions",
              "generated_functions_all_supported", "hand_written_instructions", "all_dumped_unsupported",
              "functions_per_call_kind"):
        w(f"| `{k}` | {json.dumps(fc[k], ensure_ascii=False)} |")
    w(f"| `parser` | {json.dumps(kp['counts'], ensure_ascii=False)} |")
    w("")
    w("Parser ERR list:")
    w("")
    for r in kp["errors"]:
        w(f"- `{short(r['symbol'])}` ({r['group']}): {r['error']}")
    if not kp["errors"]:
        w("- none")
    w("")
    w("Mnemonic frequency of the generated functions (inventory types only):")
    w("")
    w(", ".join(f"`{k}` {v}" for k, v in fc["mnemonic_occurrences_inventory"].items()))
    w("")
    w("## 5. Set differences")
    w("")
    w(f"- {c['fulu_reachable_generated_types_not_fork_config']} generated Fulu-reachable types are not fork config types: "
      + ", ".join(f"`{short(x)}`" for x in inv["sets"]["fulu_reachable_generated_types_not_fork_config"]) + ".")
    w(f"- {c['inventory_types_not_fork_config']} inventory types are not fork config types: "
      + ", ".join(f"`{short(x)}`" for x in inv["sets"]["inventory_types_not_fork_config"]) + ".")
    w(f"- {c['fork_config_types_not_fulu_reachable']} fork config types are not Fulu-reachable."
      " The names are in `inventory.json` `sets.fork_config_types_not_fulu_reachable`.")
    w("")
    w("Configs that are not Fulu:")
    w("")
    w("| Config | Type count | Reason |")
    w("| --- | --- | --- |")
    for x in inv["not_fulu"]:
        w(f"| `{x['config']}` | {len(x['types'])} | {x['reason']} |")
    w("")
    w("Hand-written delegate targets (SSZ methods that the generator does not make):")
    w("")
    w("| Type | Count of calling types |")
    w("| --- | --- |")
    for h in inv["hand_written_delegates"]:
        w(f"| `{short(h['type'])}` | {h['used_by_count']} |")
    w("")
    w("The types with a different IR in minimal are in `inventory.json` `minimal_differences`. The scope classification changes are as in the numbers above.")
    w("")
    w("## 6. Type table")
    w("")
    w("Columns: config, Fulu-reachable, kind, field count, depth, scope (reasons), delegate calls (generated/hand), instruction count M/S/U (MarshalSSZTo/SizeSSZ/UnmarshalSSZ), count of mnemonic kinds, mnemonics that Kraken does not support, parser (M/S/U), runtime calls (union of the three functions).")
    w("Call abbreviations: " + ", ".join(f"{v}={k}" for k, v in ABBR.items()) + ".")
    w("")
    w("| Type | Config | Fulu-reachable | Kind | Fields | Depth | Scope | Delegates | M/S/U | Mnemonics | Not supported | Parser | Calls |")
    w("| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |")
    hand = {tuple(h["type"].rsplit(".", 1)) for h in inv["hand_written_delegates"]}
    for t in sorted(inv["types"], key=lambda t: (t["config"], t["name"])):
        fs = [funcs.get((t["package"], t["name"], m)) for m in METHODS]
        ins = "/".join(str(f["instructions"]) if f else "-" for f in fs)
        mn = set()
        uns = set()
        calls = set()
        kpst = []
        for f in fs:
            if not f:
                kpst.append("-")
                continue
            mn |= set(f["mnemonics"])
            uns |= set(f["unsupported"])
            calls |= set(f["calls"])
            r = kps.get(f["symbol"], {}).get("status", "not run")
            kpst.append(r)
        ng = sum(1 for cc in t["callees"] if tuple(cc.rsplit("/", 1)) not in hand)
        nh = sum(1 for cc in t["callees"] if tuple(cc.rsplit("/", 1)) in hand)
        scope = t["scope"] + (f" ({', '.join(t['reasons'])})" if t["reasons"] else "")
        w(f"| `{t['name']}` | {t['config'].rsplit('/', 1)[-1].removesuffix('.yaml')} | {'yes' if t['fulu_reachable'] else ''} | "
          f"{t['kind']} | {t['field_count']} | {t['depth']} | {scope} | {ng}/{nh} | {ins} | {len(mn)} | "
          f"{', '.join(sorted(uns)) or '-'} | {'/'.join(kpst)} | {' '.join(sorted(ABBR.get(x, x) for x in calls))} |")
    w("")
    w("Field shape frequency (all inventory types): " + ", ".join(f"{k} {v}" for k, v in c["field_shape"].items()) + ".")
    w("")
    open(f"{d}/TYPES.md", "w").write("\n".join(L))
    print(f"TYPES.md: {len(inv['types'])} rows")


if __name__ == "__main__":
    main()
