#!/usr/bin/env python3
"""Write fv/kraken/prysm/TYPES.md from the saved JSON. No number is typed by hand.

Usage: types_md.py <prysm-dir>
Inputs: inventory.json, go1.26.10/functions.json, go1.26.10/kparse.json,
go1.26.10/kparse-riz-diag.json, diff/gendiff.json, go1.26.10/build-ids.txt.
Python 3 standard library only. Run with python3 -I.
"""
import json
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
    kp = json.load(open(f"{d}/go1.26.10/kparse.json"))
    rz = json.load(open(f"{d}/go1.26.10/kparse-riz-diag.json"))
    gd = json.load(open(f"{d}/diff/gendiff.json"))
    bid = dict(l.split(": ", 1) for l in open(f"{d}/go1.26.10/build-ids.txt").read().splitlines() if ": " in l)
    c, fc = inv["counts"], fn["counts"]
    kps = {r["symbol"]: r for r in kp["functions"]}
    rzs = {r["symbol"]: r for r in rz["functions"]}
    funcs = {(f["package"], f["type"], f["method"]): f for f in fn["functions"]}
    L = []
    w = L.append
    w("# TYPES: Prysm Fulu type list (phase1c X1)")
    w("")
    w("`fv/kraken/gen/types_md.py` makes this file from the saved JSON. Do not change it by hand.")
    w("The program counts all numbers. The scope classification is a first pass (provisional). It is not a proof. Gate 1c is not passed.")
    w("")
    w("## 1. Summary")
    w("")
    w(f"- Inventory set I: {c['set_I']} generated types. Config types A: {c['set_A']}, Fulu-reachable B: {c['set_B']} (generated {c['set_B_generated']}, hand-written {c['set_B_hand_written']}).")
    w(f"- In scope: {c['scope_in']}, out of scope: {c['scope_out']} (provisional). Reasons for out of scope: " +
      ", ".join(f"{k} {v}" for k, v in c["out_primary_reason"].items()) + ".")
    w(f"- For B only: in scope {c['B_scope_in']}, out of scope {c['B_scope_out']}.")
    fsh = c["field_shape"]
    w("- \"In scope\" means that the first-pass rules did not remove the type. It does not mean that a proof is possible. It also does not mean that the type fits the hand proof patterns.")
    w(f"  It is wider than the first-pass Gist list: it contains {fsh.get('vector[bytesN]', 0)} `vector[bytesN]` fields, {fsh.get('list[bytesN]', 0)} `list[bytesN]` fields "
      f"and {fsh.get('vector[uint64]', 0)} `vector[uint64]` fields. The depth is the inline depth (it does not follow delegation).")
    w("  The classification by what the proofs need is in `SCOPE-P6.md`.")
    w(f"- Hand-written delegate targets (`consensus-types/primitives`): {c['I_hand_written']}. Types that call them: {c['types_calling_hand_written']}.")
    w(f"- Generated functions: {fc['generated_functions_inventory']} (types × 3), instructions: {fc['generated_instructions']}, maximum for each function: {fc['max_instructions']}.")
    w(f"- Mnemonic level: {fc['generated_functions_all_supported']}/{fc['generated_functions_inventory']} generated functions use only names that the Kraken runtime parser accepts.")
    ok_inv = kp["counts"].get("inventory: OK", 0)
    err_inv = kp["counts"].get("inventory: ERR", 0)
    w(f"- Real parser run: {ok_inv} generated functions OK, {err_inv} ERR. All ERR are `%riz` operands (section 4).")
    w(f"- We ran all files that failed because of `%riz` ({rz['ok'] + rz['err']}, including functions outside I) again as diagnostic copies with only `%riz` removed. {rz['ok']} are OK. This is only a diagnosis, not a conversion result.")
    w(f"- Differences from the committed Prysm files: {gd['totals']['blocks']} changed blocks, {gd['totals']['classified']} classified, {gd['totals']['unclassified']} not classified.")
    w(f"- Types with a different IR in the minimal preset: {c['minimal_differs']}. Types with a changed scope classification: {c['minimal_scope_changes']}.")
    w("")
    w("## 2. Fixed values")
    w("")
    w("| Item | Value |")
    w("| --- | --- |")
    w("| Prysm source | `ab15ff70c72a568c870b2de662474685a95de294` (slice + `ssz-size`). It replaced the old pin `5ac1d028f5`/`45394e5` |")
    w("| Generator and runtime | `698c2025a73a296b55b95744a8408f3b03b2546b` |")
    w(f"| Target compilation | Cross-compiled for linux/amd64 with `{bid['go']}` (host binary), `{bid['target']}` |")
    w(f"| Host | {bid['host']} (generation is arm64 native. No x86-64 hardware) |")
    w(f"| ELF | sha256 `{bid['elf sha256']}`, {bid['elf size']} bytes. Not committed (`go1.26.10/MANIFEST.md`) |")
    w(f"| Reproducibility | Second build with an empty GOCACHE: sha256 `{bid['elf b2 sha256']}` |")
    w("| Kraken / EthLib / Lean | `6064eec` / `8621856` / `nightly-2026-09-21` |")
    w("")
    w("Go 1.26.10 is a new experiment baseline. The 55 theorems for the Go 1.26.3 ELF `9c850c97…c501` do not transfer to this machine code.")
    w("")
    w("## 3. Method")
    w("")
    w("1. `gen/prysm-gen.sh` runs the generator in a temporary Prysm tree. The flags are the same as in Prysm `build/gen/ssz.go`.")
    w("2. The same script uses `gen/invtool` to extract the IR of the front end of the generator itself (`config`, `TypeDefs`, `ParseTypeDef`, delegate interface set) as JSON.")
    w("3. `gen/inventory.py reduce` cuts the parts below delegated fields and makes `ir/ir-{mainnet,minimal}.json`.")
    w("4. `gen/inventory.py build` writes the sets, kinds, depths and scopes to `inventory.json`.")
    w("5. `gen/prysm-elf.sh` builds the ELF two times and extracts objdump and nm. `gen/keepalive.py` makes `main`.")
    w("6. `gen/mnemonics.py` counts the instructions, mnemonics and call kinds for each function (`go1.26.10/functions.json`).")
    w("7. `link/conv.py --norm` (read only) makes the `.S` files, and `gen/kparse/KParse.lean` runs the Kraken runtime parser (`go1.26.10/kparse.json`).")
    w("")
    for k, v in inv["definitions"].items():
        w(f"- `{k}`: {v}")
    w("")
    w("How we decide \"does Kraken accept it\":")
    w("")
    w(f"- Mnemonic level: the {len(fn['kraken_accepted_names'])} branch strings of `parseInstr` in `Kraken/X64/Parser/Basic.lean` of the fixed Kraken, and `j`/`set`/`cmov` + {len(fn['kraken_condition_codes'])} `parseCondCode?` condition codes. The {len(fn['conv_norm_forms'])} `conv.py` NORM forms count as `nop`.")
    w("- Real parser level: we ran `Kraken.X64.Parser.parse`, which `include_x64_rt` uses, on each file (log copy `go1.26.10/kparse-log.txt`). This is the verdict criterion.")
    w("- We did not examine the semantics level (`kstep` and theorems). This table is a classification, not a proof.")
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
    w(f"| `kparse` | {json.dumps(kp['counts'], ensure_ascii=False)} |")
    w(f"| `kparse_riz_diag` | OK {rz['ok']}, ERR {rz['err']} |")
    w("")
    w("Parser ERR list:")
    w("")
    for r in kp["errors"]:
        w(f"- `{short(r['symbol'])}` ({r['group']}): {r['error']}")
    w("")
    w("`%riz` is the spelling that GNU objdump uses for a SIB byte without an index (when `%r12` is the base register). The address is the same as `(%r12)`.")
    w("It is not a generator defect. It is a gap in the converter or in the Kraken parser (`GENERATOR-FINDINGS.md` section 4).")
    w("")
    w("Mnemonic frequency of the generated functions (I only):")
    w("")
    w(", ".join(f"`{k}` {v}" for k, v in fc["mnemonic_occurrences_inventory"].items()))
    w("")
    w("## 5. Set differences")
    w("")
    w(f"- {c['B_generated_minus_A']} generated types in B are not in A: " + ", ".join(f"`{short(x)}`" for x in inv["sets"]["B_generated_minus_A"]) + ".")
    w(f"- {c['I_minus_A']} types in I are not in A: " + ", ".join(f"`{short(x)}`" for x in inv["sets"]["I_minus_A"]) + ".")
    w(f"- {c['A_minus_B']} types in A are not in B. The names are in `inventory.json` `sets.A_minus_B`.")
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
    w("Columns: config, B (Fulu-reachable), kind, field count, depth, scope (reasons), delegate calls (generated/hand), instruction count M/S/U (MarshalSSZTo/SizeSSZ/UnmarshalSSZ), count of mnemonic kinds, mnemonics that Kraken does not support, parser (M/S/U), runtime calls (union of the three functions).")
    w("Call abbreviations: " + ", ".join(f"{v}={k}" for k, v in ABBR.items()) + ".")
    w("")
    w("| Type | Config | B | Kind | Fields | Depth | Scope | Delegates | M/S/U | Mnemonics | Not supported | Parser | Calls |")
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
            if r == "ERR" and rzs.get(f["symbol"], {}).get("status") == "OK":
                r = "ERR(riz)"
            kpst.append(r)
        ng = sum(1 for cc in t["callees"] if tuple(cc.rsplit("/", 1)) not in hand)
        nh = sum(1 for cc in t["callees"] if tuple(cc.rsplit("/", 1)) in hand)
        scope = t["scope"] + (f" ({', '.join(t['reasons'])})" if t["reasons"] else "")
        w(f"| `{t['name']}` | {t['config'].rsplit('/', 1)[-1].removesuffix('.yaml')} | {'B' if t['in_B'] else ''} | "
          f"{t['kind']} | {t['field_count']} | {t['depth']} | {scope} | {ng}/{nh} | {ins} | {len(mn)} | "
          f"{', '.join(sorted(uns)) or '-'} | {'/'.join(kpst)} | {' '.join(sorted(ABBR.get(x, x) for x in calls))} |")
    w("")
    w("Field shape frequency (all of I): " + ", ".join(f"{k} {v}" for k, v in c["field_shape"].items()) + ".")
    w("")
    open(f"{d}/TYPES.md", "w").write("\n".join(L))
    print(f"TYPES.md: {len(inv['types'])} rows")


if __name__ == "__main__":
    main()
