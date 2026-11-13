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
- A generator does not write to the shared libraries (`lean/Spec`, `lean/Machine`, `lean/Runtime`, `lean/Codec`), `link/` or `gen/frozen/`.
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
| `checks/link_set.py`, `checks/*_link.py` | The Prysm ELF, its disassembly and symbol listing | The link set `prysm/go1.26.10/link-set`: the filtered disassembly and the data files. The `*link.py` scripts hold the item tables |
| `checks/callgraph.py` and the `callgraph` mode of `checks/*_link.py` | A filtered disassembly | `callgraph*.json` files. The tree holds none of them. `checks/checkpoint_and_epoch_link.py` imports the function list of `checks/callgraph.py` |
| `checks/*_differential.py` | Nothing, or a Go output file | Go differential cases, and their comparison with the Go output |
| `frozen/build_lists.py` | The inventory and the generated Go | `frozen/THEOREMS.json`, `frozen/ASSUMPTIONS.json` |
| `kraken-parser/summ.py` | A log of `kraken-parser/KParse.lean` | `prysm/go1.26.10/kparse.json`: which functions the Kraken parser reads |
| `prysm-gen.sh`, `prysm-elf.sh` | A Prysm tree and the generator binary | Generated Go, the IR and the Prysm ELF (needs Go) |

The tools for the 24 other flat types are in `prysm/go1.26.10/evidence/flat-types/tools/` and `prysm/go1.26.10/evidence/flat-types/runs/run_generators.sh`.
The encoder specification and witness emitter of the flat types is `prysm/go1.26.10/evidence/generator-cases/encode-spec/encode_spec_emitter.py`.

`generator/generator.py` has three modes. `uint64`: the accept path of a uint64 primitive decoder. `decoder`: a container
decoder. Without an option it writes the 32-byte field segments. `--field-segments` adds byte vectors of 32, 48 and
96 bytes and inline uint64 fields, `--call-segments` also the fields that a callee decodes, `--steps` the step chain
over windows (a padding `nop` anywhere), and `--whole-accept` the step chain with the whole accept and size-reject
theorems. `encoder --fast-path`: the encoder fast path theorem. `generator/option-names.tsv` gives the earlier names of
the modes and options and of the labels in the generated headers (run records and old headers use them).
`prysm/go1.26.10/evidence/flat-types/runs/record-names.tsv` maps the earlier run record names of `run_generators.sh`.

## 3. Check that a generated file is the generator output

Use `regen_check.sh` of the project skill. It runs the generator two times into scratch files and compares them with the tracked file.
Exit 0 means the same bytes. Run it from `fv/kraken`:

```sh
sh ../../.claude/skills/maintaining-methodical-fv/scripts/regen_check.sh lean/Prysm/CommitteeIndex/GeneratedDecodeAccept.lean -- sh -c 'python3 -I gen/generator/generator.py uint64 --S prysm/go1.26.10/link-set/norm/github.com_OffchainLabs_prysm_v7_consensus_types_primitives.CommitteeIndex.UnmarshalSSZ.S --const unmarshalSSZ --name Decode.generated_accept --same-as Prysm.CommitteeIndex.Decode.accept --imports Codec.Uint64Decoder,Prysm.Slot.DecodeAccept --open Prysm.CommitteeIndex.Code > "$REGEN_OUT"'
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
python3 -I -B fv/kraken/gen/generator/kindcheck.py fv/kraken/lean/Prysm/CommitteeIndex/GeneratedDecodeAccept.lean
python3 -I -B fv/kraken/gen/generator/kindcheck.py --partial fv/kraken/lean/Prysm/BeaconBlockHeader/GeneratedDecodeFieldSegmentsPartial.lean
```

Run Lean and `kindcheck.py` together on every generated file. Each one alone lets a defect through.
`kindcheck.py` does not check the kind parameters. Only the proof checks them, through its code facts.
A partial file gives exit 3, never 0. Exit 3 is not a full-coverage result.
A kind identity is not a witness. It does not show that the premises can hold.

## 5. The independent `Desc` checker

`desccheck/DescCheck.lean` is a Lean program that runs EthLib functions. It shares no code with `desc/producer.py`.
So a defect in the producer or in the IR does not also hide in the checker.
`desc/run_desccheck.sh` runs it (needs Lean). The result is `desc/results/main.result.json`.
That result and the review sources `desc/review/*` are records of earlier runs, and they keep the earlier names of the
`Spec` declarations (for example `Spec.scDesc`, `Fv1.luDesc`). `desc/spec-names-old-new.tsv` gives the present name of
each earlier name. A new checker run writes the present names.

- The set of expected types is closed. It is the table of hand cases in the checker plus the keys of `prysm/inventory.json`.
- Before it parses a file, the checker limits the file size and the nesting depth.
- For a hand case, the checker compares the `Desc` with the EthLib specification in `lean/Spec/`.
- For a Prysm type, the checker compares the `Desc` only with the inventory. This is a consistency check, not a specification check.

Thus the Prysm theorems use a hand `Desc` written from consensus-specs, and a theorem shows that it has the same codec as the checker `Desc`.

## 6. The axioms gate

`checks/axioms_gate.py` is the one axioms gate. It covers every declaration of every Lean library of the project.
`e2e/axioms_gate.py` only forwards to it: the CI workflow `.github/workflows/fv-lean.yaml` names that earlier path, and the workflow file
cannot be changed with the access of this session. When the workflow names `gen/checks/axioms_gate.py`, delete `gen/e2e/`.

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
- `checks/axioms.py` reads the output of `lake env lean <hand list>` for one hand list.

### Theorems with the same statement

`tools/duplicate_statements.py` reads the dump of the gate (`run` mode) and the tree. It finds each group of theorems
with the same statement hash and gives the group one class with a reason. The class rules are in its usage text.

```sh
python3 -I -B fv/kraken/gen/restructure/tools/regen.py <scratch>/regen-work > <scratch>/regen.txt
python3 -I -B fv/kraken/gen/tools/duplicate_statements.py <scratch>/dump.tsv --root fv/kraken \
  --regen <scratch>/regen.txt --out <scratch>/groups.tsv
python3 -I -B fv/kraken/gen/tools/duplicate_statements.py --selftest
```

- Give `regen.py` the `--files` options that its usage text names. The tool takes the generated files from its result.
- The table has one row per theorem of a group: group id, name, module, class, reason. The counts per class go to
  standard error.
- Exit 1 means a group in the class `delete-candidate` (a hand theorem that can be removed: its twin is visible at
  every use and no check names it) or `unclassified`. Remove the theorem, or record a new rule in the tool.
- The tool reads text. It does not see a name that a macro declares, or a use through a notation.

## 7. Python-only checks

These run without Lean, Go or the Prysm ELF:

- `generator/kindcheck.py`, and the `--selftest` mode of `checks/axioms_gate.py`.
- `tools/duplicate_statements.py`, on a dump of the axioms gate (the dump itself needs Lean).
- `python3 -B fv/kraken/link/data.py --check fv/kraken/link/out`.
- `regen_check.sh` with `generator/generator.py`, `checks/desc_to_lean.py`, `checks/list_desc_to_lean.py`, `checks/layout.py` and `checks/attestation_data_layout.py`.
- `type_inventory.py reduce` and `build`, `type_list_document.py`, `type_scope.py`, `keepalive.py`, `kraken-parser/summ.py`.
- `frozen/test_frozen.py <repo-root> <scratch>`, which runs `frozen/build_lists.py` and compares the two frozen lists.
- `desc/test_desc.py prepare` writes the `Desc` files. The checker run after it needs Lean.

These need more than Python:

- `checks/negative.py` and the `run` mode of the axioms gate need Lean.
- The link checks need the ELF and the LLVM tools.
- The differential checks need Go and a Prysm tree.
- `tools/proof_inventory.py methods` needs the symbol listing of the Prysm ELF. Its `run` mode needs Lean: the output of
  `tools/inventory_decls.lean` and the JSON of an axioms gate run on the built tree.

## 8. Known limits

These generated outputs do not reproduce from the tracked tree today:

- `frozen/ASSUMPTIONS.json`: the file has a hand edit. `frozen/test_frozen.py` exits 1.
- 11 of the 18 files that `checks/desc_to_lean.py` writes have hand-added or edited header lines.

Other limits:

- The specification and witness files of five flat types (HistoricalSummary, SyncAggregatorSelectionData, SigningData, ValidatorBalance, VoluntaryExit) have no tracked generator script.
- The commands of 12 generated files are not in `generator/gen.sh`. Their headers give the commands.
- `prysm/go1.26.10/evidence/flat-types/runs/run_generators.sh` calls a job wrapper that is not tracked. Run its `generator.py` commands directly.
- 15 of the 24 `*SpecChecker.lean` headers name a path where the `Desc` file is not. The file is in a subdirectory of
  `prysm/go1.26.10/evidence/` (`eth1-data/`, `flat-types/`, `five-flat-types/` and the hold-out directories). Nine of these headers have a hand-added line that
  gives the subdirectory; the other six do not (DepositRequest, HistoricalSummary, SigningData,
  SyncAggregatorSelectionData, ValidatorBalance, VoluntaryExit).
- `kindcheck.py` does not bind the code constant of a theorem to the `.S` file of the header. It does not check the `.S` label against the IR type.
