# gen: phase 1c generator and tools

This is the code of 1c (proof generator and all Prysm Fulu types). There are no proofs yet.
At tag `archive/fv-before-workflow`, gate 1c was not passed. No one evaluated gate 1c again on the current tree.
On 2026-11-12, commit `84a4747` removed `gen/x4/`, `gen/x5/`, `gen/complete/` and `gen/wit/`. Tag `archive/fv-before-workflow` holds them.
The Prysm results are in `../prysm/`. For the environment and the gate rules, follow the brief in the run directory.

## 1. Directories

| Path | What | Stage |
| --- | --- | --- |
| `invtool/` | Front-end IR of the generator to JSON (built in a temporary Prysm tree) | P1 |
| `prysm-gen.sh`, `prysm-elf.sh`, `keepalive.py` | Generation, IR, Go 1.26.10 ELF | P1 |
| `inventory.py`, `gendiff.py`, `mnemonics.py`, `kparse/`, `types_md.py` | Inventory, diff classification, instruction statistics, Kraken parser run, `TYPES.md` | P1 |
| `obligations.py` | Enumeration of the error return sites in the Go source | P2 |
| `frozen/` | Frozen lists `THEOREMS.json`, `ASSUMPTIONS.json` (the generator does not write them) | P2 |
| `desc/` | `Desc` producer and tests | P3 |
| `desccheck/` | Independent `Desc` checker (Lean, runs EthLib functions) | P3 |
| `gen1c/` | Generator skeleton, one include adapter | P4 |
| `e2e/enc2link.py`, `e2e/enc2survey.py` | Flat-encoder link table (`prysm/go1.26.10/e2e/enc2/link`) and survey (`prysm/go1.26.10/e2e/scal/enc2-survey.md`) | Flat-encoder preparation unit |

## 2. Output formats

All JSON files have a `schema` key.

| Output | Format | Definition |
| --- | --- | --- |
| Desc | `fvphase1c.desc/1` | Header comment of `desc/producer.py`. EthLib `Desc` term + header layout claims |
| Theorem statement | Lean `def <obl>_stmt [Host] : Prop` (hand case `namespace Gen1c.Hand.<T>`, Prysm `Gen1c.Prysm.<last two segments of the package>.<T>`) | `gen1c/emit.py`. No proofs and no `sorry`. The current template covers only size for fixed-size types |
| Witness configuration | `witness.json` | Lengths 0, 1 and maximum for each variable field. A list of variable elements adds an inner length rule |
| Negative cases | `negative.json` | Mutation, target theorem, expected failure, control. Format only. The X4 runs used them, and `gen/x4/` was removed on 2026-11-12 |
| Data files | `<id>.data` (include API v2, the format is the same as v1) | Only `gen1c/include_adapter.py` knows the API names and syntax |
| Obligation list | `fvphase1c.theorems/1` | `frozen/THEOREMS.json` |
| Permitted assumptions | `fvphase1c.assumptions/1` | `frozen/ASSUMPTIONS.json` |
| Manifest | `fvphase1c.gen-manifest/1` | API version, input hashes, files for each type, data items (offset, whether code refers to it) |

include API: `api_version` 2, status `committed` (fix3 `b6c32c3`, before review). Copy `gen1c/include-api-v2.json`, the v1 copy is history.
If the version changes, change only `gen1c/include_adapter.py`. `check_api` rejects other versions.

## 3. Rules

- The generator does not write to `lean/Fk`, `link/` or `gen/frozen/`. `emit.py` checks this before it writes (the controls in `gen1c/test_emit.py`).
- Before fix3 is approved, do not generate `lean/Fk` or `link/` code. The output goes to scratch and artifacts in the run directory.
- Python uses only the standard library and runs with `python3 -I`. All Go and Lean runs occur in the gate.

## 4. Tests

| Test | Command | Result file |
| --- | --- | --- |
| Desc checker: 144 originals (closed world), controls, replay of review mutations (r1 20, r2 32, r3 40), list scenarios (review t01–t13, mine, add/replace for each wrong hand Desc) | `desc/test_desc.py prepare` → gate `desc/run_desccheck.sh` → `desc/test_desc.py evaluate` | `desc/results/desc-test.{json,md}` |
| emit boundary: all scenarios through `emit.accept`, review E1–E7, my escape attempts x01–x16 | `gen1c/test_boundary.py <desc-work> <out>` | `gen1c/results/boundary.{json,md}` |
| Generator skeleton: controls, data cross-check, statement comparison | `gen1c/test_emit.py prepare <work> <desc-work>` → gate `Compare.lean` → `evaluate` | `gen1c/results/gen-test.json` |
| Frozen list reproduction | `frozen/test_frozen.py <repo-root> <scratch>` | Exit code |
| Prysm tests | gate `prysm-tests.sh` (exit code = verdict of `prysm_tests_classify.py`) | `prysm/tests/` |

## 5. Desc checker and emit boundary

- The checker (`desccheck/DescCheck.lean`) is a closed world. Expected key set = 9 in the checker table + 135 from `prysm/inventory.json` in the work tree (its sha256 goes into the result). The set does not come from the producer output. The originals must be exactly equal to this set. Inventory keys must be only under the two Prysm packages (self-check).
- Before it parses, the checker examines the file size (1 MiB) and the bracket nesting depth (64) (`bounds`). All 9 top-level keys must be present (`required-keys`, `reference` can be null). It matches a Prysm Desc with the inventory, and it matches delegated container fields (and list and vector elements) recursively with the inventory entry of the called type. The two exception keys (v1alpha1 `Checkpoint`, `AttestationData`) must be equal to `Fv1.cpDesc` and `Fv1.adDesc` except for the names (`exception-shape`).
- The result is one JSON file (`fvphase1c.desccheck-result/1`, the Lean JSON encoder writes it). For each file, it has the path, the sha256 of the content (EthLib SHA-256), the key, the status (SPEC/NONE), PASS/FAIL and the failed checks, and it has an overall `verdict`. The human log escapes characters outside printable ASCII.
- `gen1c/emit.py` reads only this result file (it does not read the log). Accept conditions: the result is strict JSON, `verdict` OK, no list-level findings, inventory sha256 = work tree file = pin of the frozen list (`THEOREMS.json` `sources_sha256`). Exactly one original record for each key. sha256 of the read bytes = that record. A status that fits the mode (hand_case = table key + SPEC, prysm = key that is not a hand case + NONE + a frozen list row exists). `--types` (pkg.Type) is required. It reads the Desc one time, hashes those bytes and parses them. It examines the Desc shape (9 top-level keys, `fixed_size` is a natural number or null). All input with a wrong format ends with `SystemExit` (reject). The output is `<out>/<package with / changed to _>/<Type>/`, and two equal type names are an error. `--out` must not exist or must be empty (no merge).

Threat model:
- What it blocks: producer and IR defects of the 9 hand types (specification comparison), Desc files that are wrongly attached, stray, missing or duplicated, look-alike character names, JSON parse differences (duplicate keys, float notation), stale and mixed result files at the emit boundary (sha256 binding, verdict, inventory hash).
- What it does not block: wrong shapes of the 135 Prysm types that agree with the inventory (the inventory does not have bit lengths within the same byte count as the list limit) (there is no offline independent specification. It examines only consistency), result files forged by hand (there is no signature), an inventory committed wrong on purpose.
