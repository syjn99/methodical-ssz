# gen: generators and check tools

This directory holds the programs that write Lean files and records, and the programs that check them.
A path that starts with `lean/`, `link/` or `prysm/` is relative to `fv/kraken/`. Any other path is relative to `fv/kraken/gen/`.
A command that starts with `fv/kraken/` runs from the repository root.
The design principles are in `../../README.md`.

## 1. Principles

- A generator is untrusted. Lean checks every proof that a generator writes.
- The statement of a generated theorem is checked separately, by a frozen kind (section 4) or by an identity with a hand statement.
- A generated Lean file must be equal to the output of its generator. Do not edit a generated file by hand.
  The header comment of a generated file names its generator. Some headers also give the sha256 of the inputs.
- A generator does not write to the shared libraries (`lean/Spec`, `lean/Machine`, `lean/Runtime`, `lean/Codec`) or `link/`.
- The Python programs use only the standard library. Run them with `python3 -I`.
- A generator refuses an input that it does not match. It writes nothing, or it marks a partial output as partial.

## 2. Generators

| Program | Reads | Writes |
| --- | --- | --- |
| `generator/generator.py`, with `generator/whole_accept.py` and `generator/fast_path.py` | A converted `.S` file and the IR entry of one type | `lean/Prysm/<GoTypeName>/Generated*.lean`: segment, accept, size reject and encoder fast path theorems |
| `generator/gen.sh` | | Runs `generator.py` once for each committed generated file |
| `checks/desc_to_lean.py`, `checks/list_desc_to_lean.py` | A `Desc` JSON file that the checker accepted | `*SpecChecker.lean`: the checker `Desc` as Lean |
| `checks/layout.py`, `checks/attestation_data_layout.py` | `prysm/ir/ir-mainnet.json` | `lean/Prysm/Checkpoint/Layout.lean`, `lean/Prysm/AttestationData/Layout.lean` |
| `desc/producer.py` | The reduced IR | One `Desc` JSON file for each type |
| `type_inventory.py` | The raw IR of the generator | `prysm/ir/*.json` (`reduce`) and `prysm/inventory.json` (`build`) |
| `type_list_document.py`, `type_scope.py` | `prysm/inventory.json` | `prysm/TYPES.md`, `prysm/type-scope.json`, `prysm/type-scope.md` |
| `keepalive.py` | `prysm/inventory.json` | The `main.go` of the Prysm target |
| `tools/proof_inventory.py` | The symbol listing of the ELF (`methods`); a declaration list from `tools/inventory_decls.lean` and the JSON of an axioms gate run, both on the built tree (`run`) | `prysm/go1.26.10/ssz-methods.json`, `prysm/proof-inventory.md`, `prysm/proof-inventory.json` |
| `checks/link_set.py` | The Prysm ELF, its disassembly and symbol listing, and the item table `prysm/go1.26.10/link-set.tsv` | The link set `prysm/go1.26.10/link-set`: the filtered disassembly, the `.S` files and the data files (`../link/README.md` section 7) |
| `checks/differential.py` | Nothing (`cases`), or the output of `checks/differential-main.go.txt` (`check`) | The Go differential cases `prysm/differential-cases/<package>.<Type>.json`, and their comparison with the Go output |
| `flat-types/flat_types_spec.py`, `flat-types/flat_types_decode_spec.py`, `flat-types/flat_types_witness.py`, `flat-types/flat_types_encode_spec.py`, `flat-types/encode_spec_emitter.py` | The generated theorems of the flat types | The specification, witness and specification corollary modules of the flat types in `lean/Prysm/<GoTypeName>/` |
| `flat-types/flat_types_negative_cases.py` | The Lean files of the flat types | `checks/negative-cases/negative-cases-flat-types.json` |
| `flat-types/flat_types_hand_list.py` | A declaration dump | New names in the hand list `axioms-lists/flat-fixed-size-types.lean` |
| `flat-types/run_generators.sh` | The `.S` files of the flat types | The generator outputs of the flat types, in a scratch directory |
| `prysm-rebuild-and-check.sh` | A Prysm tree and the generator tree | The Prysm ELF, the link set and the differential results, in a scratch directory (needs Docker) |
| `kraken-parser/summarize_parser_log.py` | A log of `kraken-parser/ParserRun.lean` | `prysm/go1.26.10/parser-result.json`: which functions the Kraken parser reads |
| `prysm-gen.sh`, `prysm-elf.sh` | A Prysm tree and the generator binary | Generated Go, the IR and the Prysm ELF (needs Go) |

`generator/generator.py` has three modes. `uint64`: the accept path of a uint64 primitive decoder. `decoder`: a container
decoder. Without an option it writes the 32-byte field segments. `--field-segments` adds byte vectors of 32, 48 and
96 bytes and inline uint64 fields, `--call-segments` also the fields that a callee decodes, `--steps` the step chain
over windows (a padding `nop` anywhere), and `--whole-accept` the step chain with the whole accept and size-reject
theorems. `encoder --fast-path`: the encoder fast path theorem.

## 3. Check that a generated file is the generator output

Use `regen_check.sh` of the project skill. It runs the generator two times into scratch files and compares them with the tracked file.
Exit 0 means the same bytes. Run it from `fv/kraken`:

```sh
sh ../../.claude/skills/maintaining-methodical-fv/scripts/regen_check.sh lean/Prysm/ValidatorIndex/GeneratedDecodeAccept.lean -- sh -c 'python3 -I gen/generator/generator.py uint64 --assembly prysm/go1.26.10/link-set/norm/github.com_OffchainLabs_prysm_v7_consensus_types_primitives.ValidatorIndex.UnmarshalSSZ.S --const unmarshalSSZ --name Decode.generated_accept --imports Codec.Uint64Decoder,Prysm.BeaconBlockHeader.Code --open Prysm.ValidatorIndex.Code > "$REGEN_OUT"'
```

For the other files, take the command from `generator/gen.sh` or from the file header. Replace the output redirect with `> "$REGEN_OUT"`.
The check compares bytes only. It does not show that the output is correct.

## 4. The kind check

A generated theorem `t` is followed by a line `t_kind`.
It states that the full type of `t`, with all hypotheses, is equal to a frozen kind with parameters.
The kinds are hand text in `lean/Codec/Kind/*.lean`. Each kind has a proof from its lemma.
Lean checks the identity. So a hypothesis that the generator adds, removes or changes makes `t_kind` fail.

Lean does not check which kind the line names. A line that compares `t` with itself also compiles.
`generator/kindcheck.py` closes this gap. It checks by text that every `t_kind` names a frozen kind and has the fixed proof line.
It does not check the kind files and the lemma files themselves. Their git-blob pins were removed when the shared layer moved to `lean/Codec/`.

```sh
python3 -I -B fv/kraken/gen/generator/kindcheck.py --selftest
python3 -I -B fv/kraken/gen/generator/kindcheck.py fv/kraken/lean/Prysm/ValidatorIndex/GeneratedDecodeAccept.lean
python3 -I -B fv/kraken/gen/generator/kindcheck.py --partial fv/kraken/lean/Prysm/BeaconBlockHeader/GeneratedDecodeFieldSegmentsPartial.lean
```

Run Lean and `kindcheck.py` together on every generated file. Each one alone lets a defect through.
`kindcheck.py` does not check the kind parameters. Only the proof checks them, through its code facts.
A partial file gives exit 3, never 0. Exit 3 is not a full-coverage result.
A kind identity is not a witness. It does not show that the premises can hold.

## 5. The independent `Desc` checker

`desc-checker/DescChecker.lean` is a Lean program that runs EthLib functions. It shares no code with `desc/producer.py`.
So a defect in the producer or in the IR does not also hide in the checker.
`desc/run_desc_checker.sh` runs it (needs Lean). The result is `desc/results/main.result.json`.
`desc/test_desc.py prepare` makes its inputs, `desc/run_desc_checker.sh` writes it, and `desc/test_desc.py evaluate` checks it.
They use a relative work directory under `lean/`, so the result holds no machine path.
The result names the `Spec` descriptions, for example `Spec.scalarsDesc` and `Spec.listU64Desc`.
`desc/review_mutants.py` writes the review mutants and 13 list scenarios.
`desc/test_desc.py prepare` runs it.
A mutant or scenario id tells in plain words what the case changes or tests.
An example is `list-uint64-limit-16-to-17-reference-null`.
One mutant holds a forged checker line with a path in the work directory.
No program checks the binding of the result where a `Desc` is used.
The header of each `*SpecChecker.lean` states the sha256 of its `Desc` file as text only.

- The set of expected types is closed. It is the table of hand cases in the checker plus the keys of `prysm/inventory.json`.
- Before it parses a file, the checker limits the file size and the nesting depth.
- For a hand case, the checker compares the `Desc` with the EthLib specification in `lean/Spec/`.
- For a Prysm type, the checker compares the `Desc` only with the inventory. This is a consistency check, not a specification check.

Thus the Prysm theorems use a hand `Desc` written from consensus-specs, and a theorem shows that it has the same codec as the checker `Desc`.

## 6. The axioms gate

`checks/axioms_gate.py` is the one axioms gate. It covers every declaration of every Lean library of the project.

```sh
python3 -I -B fv/kraken/gen/checks/axioms_gate.py run <scratch>/gate.json <scratch>/dump.tsv
python3 -I -B fv/kraken/gen/checks/axioms_gate.py check <scratch>/dump.tsv <scratch>/gate.json
python3 -I -B fv/kraken/gen/checks/axioms_gate.py --selftest
```

- The `run` mode needs Lean and a built tree. It runs `lake build --no-build` on all modules first. If that fails, it stops with exit 2.
- The libraries are the `[[lean_lib]]` blocks of `lean/lakefile.toml`. The gate reads them when it runs.
- Each library must have the glob `<name>.+`. Its modules are the `*.lean` files under `lean/<name>/`. Another glob form stops the gate.
- The hand lists are the `*.lean` files in `axioms-lists/`. Each file has `#print axioms` lines and the imports that the names need.
  The gate checks that each name of a hand list is in the declaration dump.
- A new library or a new hand list needs no change to the gate.
- Each declaration must use only `propext`, `Classical.choice` and `Quot.sound`. `sorryAx` fails.
- The `check` mode reads a dump that `run` wrote. It needs only Python.

### Theorems with the same statement

`tools/duplicate_statements.py` reads the dump of the gate (`run` mode) and the tree. It finds each group of theorems
with the same statement hash and gives the group one class with a reason. The class rules are in its usage text.

```sh
python3 -I -B fv/kraken/gen/checks/regenerate_and_compare.py <scratch>/regen-work > <scratch>/regen.txt
python3 -I -B fv/kraken/gen/tools/duplicate_statements.py <scratch>/dump.tsv --root fv/kraken \
  --regen <scratch>/regen.txt --out <scratch>/groups.tsv
python3 -I -B fv/kraken/gen/tools/duplicate_statements.py --selftest
```

- `checks/regenerate_and_compare.py` runs the Python generators of the Lean files on a copy of the tree and compares each output
  with the tracked file. `duplicate_statements.py` takes the generated files from its result.
- The table has one row per theorem of a group: group id, name, module, class, reason. The counts per class go to
  standard error.
- Exit 1 means a group in the class `delete-candidate` (a hand theorem that can be removed: its twin is visible at
  every use and no check names it) or `unclassified`. Remove the theorem, or record a new rule in the tool.
- The tool reads text. It does not see a name that a macro declares, or a use through a notation.

## 7. Python-only checks

These run without Lean, Go or the Prysm ELF:

- `generator/kindcheck.py`, and the `--selftest` mode of `checks/axioms_gate.py`.
- `tools/duplicate_statements.py`, on a dump of the axioms gate (the dump itself needs Lean).
- `regen_check.sh` with `generator/generator.py`, `checks/desc_to_lean.py`, `checks/list_desc_to_lean.py`, `checks/layout.py` and `checks/attestation_data_layout.py`.
- `type_inventory.py reduce` and `build`, `type_list_document.py`, `type_scope.py`, `keepalive.py`.
- `checks/regenerate_and_compare.py <scratch>/<work dir>`, the regeneration comparison of all Python generators of Lean files.
- `checks/fast_path_layout.py`, an independent recomputation of the layouts of the generated encoder fast-path theorems (cwd `fv/kraken`).
- `checks/differential.py cases <dir>`. Its output must be equal to `prysm/differential-cases/`.
- `checks/python_checks.sh <scratch>/<out dir>`. It runs
  `checks/deposit_data_include_check.py`, the self-tests of `checks/axioms_gate.py`, `checks/deposit_data_include_check.py`,
  `generator/kindcheck.py` and `checks/negative.py`, `checks/fast_path_layout.py`, `kindcheck.py` on the generated files,
  `negative.py --check-cases` and `checks/negative_case_ranges.py` on every case file, and a syntax check of every Python file under `fv/`.
- `desc/test_desc.py prepare` writes the `Desc` files. The checker run after it needs Lean.

These need more than Python:

- `checks/negative.py` and the `run` mode of the axioms gate need Lean.
- `kraken-parser/summarize_parser_log.py` needs a log of `kraken-parser/ParserRun.lean` (Lean) on the `.S` files of the
  Prysm ELF (`../README.md` section 3). The log is not tracked.
- The link checks and the self-test of `link/check.py` need the ELF and the LLVM tools.
- The differential check needs Go and a Prysm tree.
  A Prysm tree at the pinned commit with the generated files of `prysm/_generated/` is enough; nothing is written into it.
  Copy `checks/differential-main.go.txt` to `<scratch>/main.go`.
  Then build it with an overlay that adds it as a package of the Prysm module:
  `go build -overlay <ov.json> -o <scratch>/differential ./fv/differential` in the Prysm tree, with Go 1.26.10.
  `<ov.json>` is `{"Replace": {"<prysm-tree>/fv/differential/main.go": "<scratch>/main.go"}}`.
  The program reads the case files in its arguments: `<scratch>/differential prysm/differential-cases/*.json > <scratch>/go-out.json`.
  Then run `checks/differential.py check prysm/differential-cases <scratch>/go-out.json <scratch>/result.json`.
  For the negative control, run `check` on the output of `checks/differential.py plant`. It must exit 1.
  `prysm-rebuild-and-check.sh` runs all of these steps in Docker.
- `tools/proof_inventory.py methods` needs the symbol listing of the Prysm ELF. Its `run` mode needs Lean: the output of
  `tools/inventory_decls.lean` and the JSON of an axioms gate run on the built tree.

## 8. Known limits

- 11 of the 18 files that `checks/desc_to_lean.py` writes have hand-added or edited header lines.
  So these files do not reproduce from the tracked tree.
- The specification and witness files of five flat types (HistoricalSummary, SyncAggregatorSelectionData, SigningData, ValidatorBalance, VoluntaryExit) have no tracked generator script.
- The commands of 12 generated files are not in `generator/gen.sh`. Their headers give the commands.
- The `Desc` files are in `prysm/go1.26.10/evidence/`. `desc_to_lean.py` names this directory in its headers.
  `list_desc_to_lean.py` names a subdirectory `lists-and-vectors/desc/` that does not exist, and two hand-edited headers
  (AttestationData, BeaconBlockHeader) name another subdirectory. Nine headers have a hand-added line that names an
  earlier subdirectory. A change of these headers changes tracked Lean files. `checks/regenerate_and_compare.py` finds a
  `Desc` file by its base name.
- `kindcheck.py` does not bind the code constant of a theorem to the `.S` file of the header. It does not check the `.S` label against the IR type.
