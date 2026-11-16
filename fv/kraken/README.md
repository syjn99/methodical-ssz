# kraken: proofs on the Kraken x86-64 model

This project proves that the x86-64 machine code of the SSZ methods that `sszgen` emits for Prysm types is correct.
The specification is the EthLib SSZ specification.
Prysm is an Ethereum consensus client.
Kraken is a Lean 4 model of x86-64 instructions.
The design principles are in `../README.md`.
The rules are in `../AGENTS.md`.

The per-method state of the proofs is the generated table `prysm/proof-inventory.md`.
Do not copy its numbers into other documents.
Run the inventory again instead (section 5).

## 1. Targets

The project has one target binary, the Prysm target.
A proof about one ELF does not transfer to another ELF.

- The source is a pinned Prysm commit, with the generated files of the pinned generator.
- The binary is a small Go `main` package.
  It keeps the SSZ methods of all inventory types in the ELF.
- The compiler is Go 1.26.10.
  It cross-compiles to `GOOS=linux GOARCH=amd64 GOAMD64=v1 CGO_ENABLED=0`, with `-tags purego -trimpath`.
- The ELF identity is its sha256.
  The file `prysm/go1.26.10/build-ids.txt` records it, with the Go build ID and the sha256 of the symbol listing and the disassembly.
- The ELF is about 23 MB.
  It is not in the repository.
  Section 3 tells how to build it again.
- The proofs read the code and the data of the ELF from the link set `prysm/go1.26.10/link-set`.

The small hand test types of `lean/Spec/Test*.lean` and `gen/desc/hand-types-ir.json` have no ELF.
The description checker tests use them (`gen/README.md` section 5).

## 2. Pinned versions

Read each pin from the file that holds it.
Do not copy the values into other files.

| Pin | File that holds it |
| --- | --- |
| Generator commit (`sszgen/`, `ssz/`) and Prysm source commit | This file: generator `698c2025a73a296b55b95744a8408f3b03b2546b`, Prysm `ab15ff70c72a568c870b2de662474685a95de294` |
| Go version, build flags, ELF sha256 of the Prysm target | `prysm/go1.26.10/build-ids.txt` |
| Kraken commit and EthLib commit | `lean/lakefile.toml` (`rev`) and `lean/lake-manifest.json` |
| Lean toolchain | `lean/lean-toolchain` |
| Sources of derived evidence files and their licenses | `THIRD-PARTY-NOTICES.md` |

## 3. Build the Prysm target again

You need Go 1.26.10 and a clean Prysm tree at the pinned commit.
You also need a generator binary built from the pinned generator commit.
Run heavy jobs one at a time, under a memory limit.

1. Apply `prysm/go1.26.10/prysm-go.mod.diff` to the Prysm `go.mod` with `git apply`.
   Do not change the diff.
   It sets the required version of the generator module to the pinned generator commit.
   It adds a `replace` line with the path `/workspace/methodical-ssz-generator`.
   The ELF records the version and the path.
   So the generator tree must be at this path when Go builds the ELF, for example as a Docker mount.
2. Generate the SSZ files and the generator IR with `sh fv/kraken/gen/prysm-gen.sh <prysm-tree> <generator-binary> <out>`.
3. Copy the generated files from `<out>/gen/` into the Prysm tree.
4. Write the `main` package with `python3 -I fv/kraken/gen/keepalive.py fv/kraken/prysm/inventory.json <prysm-tree>/fv/prysm-target/main.go`.
5. Build and dump the ELF with `sh fv/kraken/gen/prysm-elf.sh <prysm-tree> <elf-out> <empty-gocache-dir>`.
6. Compare the sha256 of the ELF with `prysm/go1.26.10/build-ids.txt`.
   If they differ, stop.
   The proofs do not apply.

`sh fv/kraken/gen/prysm-rebuild-and-check.sh <prysm-tree> <generator-tree> <scratch>` does steps 5 and 6 in Docker.
Then it runs the link check, the self-test of the link check and the Go differential check (section 5).
Its usage text gives the details.

The IR (intermediate representation) is the type description that the generator reads.
The generator binary is built from the pinned generator commit with Go 1.26.10, `-trimpath` and `-buildvcs=false`.
After step 2, these commands make the IR, the inventory, the function list, the parser result and the type lists:

```sh
python3 -I fv/kraken/gen/type_inventory.py reduce <out>/ir-mainnet.json fv/kraken/prysm/ir/ir-mainnet.json   # the same for minimal
python3 -I fv/kraken/gen/type_inventory.py build fv/kraken/prysm
python3 -I fv/kraken/gen/mnemonics.py <elf-out>/prysm-target-amd64.objdump fv/kraken/lean/.lake/packages/Kraken/Kraken/X64/Parser/Basic.lean fv/kraken/link/convert_objdump.py fv/kraken/prysm/inventory.json fv/kraken/prysm/go1.26.10/functions.json
mkdir -p <norm-out>
python3 -I fv/kraken/link/convert_objdump.py <elf-out>/prysm-target-amd64.objdump <elf-out>/prysm-target-amd64.nm <norm-out> --norm
ls <norm-out>/*.S | grep -v '/all\.S$' > <scratch>/parser-list.txt
cd fv/kraken/lean && PARSER_RUN_LIST=<scratch>/parser-list.txt lake env lean ../gen/kraken-parser/ParserRun.lean > <scratch>/parser-log.txt
python3 -I fv/kraken/gen/kraken-parser/summarize_parser_log.py <scratch>/parser-log.txt fv/kraken/prysm/go1.26.10/functions.json fv/kraken/prysm/go1.26.10/parser-result.json
python3 -I fv/kraken/gen/type_list_document.py fv/kraken/prysm
python3 -I fv/kraken/gen/type_scope.py fv/kraken
```

The converter does not make its output directory.
Make it first.
The `.S` list has one file for each function of `prysm/go1.26.10/functions.json`, without `all.S`.
The parser log is not tracked.
`kraken-parser/summarize_parser_log.py` makes `prysm/go1.26.10/parser-result.json` from it.

## 4. Directory layout

| Directory | Content |
| --- | --- |
| `link/` | The converter, the data extractor and the link check (see `link/README.md`) |
| `lean/` | The Lean project: specifications, contracts and proofs (see `lean/README.md`) |
| `gen/` | Generators and check tools (see `gen/README.md`) |
| `prysm/` | The Prysm target: inventory, IR, generated Go, link set and check records (see `prysm/README.md`) |

Section 7 tells who writes each kind of file, and what checks it.
`NEW-TYPE.md` gives the steps to prove a new type.
`FINDINGS.md` lists the limits that are open.
`THIRD-PARTY-NOTICES.md` names the sources of the files that come from other projects.

## 5. Build and check

Run the commands from the repository root, unless a command starts with `cd`.
Each item says what the command needs.

**Lean only.** Lake fetches Kraken and EthLib at the pinned commits on the first run.

```sh
cd fv/kraken/lean && lake build Machine Runtime Codec Spec Prysm
cd fv/kraken/lean && lake build Prysm.SyncAggregate.DecodeRejectSize    # one module
```

`lake build` without arguments builds only the default libraries `Spec`, `Machine` and `Runtime`.
After a build, `lake build --no-build <libraries>` must exit 0.
`lake env lean` does not check that the build is current.

**Lean and Python.** These scripts call Lean through Lake.

```sh
python3 -I -B fv/kraken/gen/checks/axioms_gate.py run <scratch>/gate.json <scratch>/dump.tsv
python3 -I -B fv/kraken/gen/checks/negative.py <cases.json> <work-dir> <scratch>/result.json <case-id>
python3 -I -B .claude/skills/maintaining-methodical-fv/scripts/decl_drift.py <base.tsv> <head.tsv>
```

- The axioms gate covers every library of `lean/lakefile.toml`.
  It reads the library names from the lakefile when it runs.
- The gate needs Lean and a built tree.
  First it runs `lake build --no-build` on all modules.
  If that fails, the gate stops with exit 2.
- The gate writes a declaration dump.
  It checks that every declaration uses only `propext`, `Classical.choice` and `Quot.sound`.
- The gate also checks that each name of the hand lists in `gen/axioms-lists/` is in the dump.
  Each `*.lean` file of that directory is a hand list.
- A new library or a new hand list needs no change to the gate.
- The gate overwrites its JSON argument.
  Give a scratch path.
- The negative test files are the `negative-cases-*.json` files in `gen/checks/negative-cases/`.
  A case id is the Go type, the theorem without its type namespace, and the kind (`control`, `statement` or `code`).
  For a mutant, the id ends with the changed words or operands, for example `epoch-decode-accept-code-cmp-0x8-to-0x9`.
  The usage text of `gen/checks/negative.py` gives the case fields.
  A case may name `mutant_imports`: `negative.py` imports these modules into the mutated copy only.
  So a mutant can use a declaration of another module.
  Run one case per job.
  A case file whose cases name `statement_module`, `inline` or `statement_def` runs with `gen/checks/list_negative.py`, with the same arguments.
- The negative run with Lean needs Linux, because `negative.py` and `gen/tools/memory_limit.py` read `/proc`.
  On macOS, run it in a Linux container that has the toolchain of `lean/lean-toolchain`.
- The drift check compares a dump with the dump of a reviewed tree.

The proof inventory `prysm/proof-inventory.md` needs a built tree and the JSON of an axioms gate run on it (cwd `fv/kraken`):

```sh
python3 -I -B gen/tools/proof_inventory.py names <scratch>/inventory-names.txt
cd lean && lake env lean --run ../gen/tools/inventory_decls.lean <scratch>/inventory-names.txt \
  $(cd .. && find lean/Prysm -name '*.lean' | sed 's|^lean/||;s|\.lean$||;s|/|.|g' | sort) > <scratch>/decls.tsv && cd ..
python3 -I -B gen/tools/proof_inventory.py run <scratch>/decls.tsv <scratch>/gate.json prysm/proof-inventory.md prysm/proof-inventory.json
```

**Python only.** These use only tracked files.

```sh
python3 -I -B fv/kraken/gen/generator/kindcheck.py --selftest
python3 -I -B fv/kraken/gen/generator/kindcheck.py fv/kraken/lean/Prysm/ValidatorIndex/GeneratedDecodeAccept.lean
python3 -I -B fv/kraken/gen/checks/axioms_gate.py --selftest
sh fv/kraken/gen/checks/python_checks.sh <scratch>/python-checks
```

`gen/README.md` tells how to regenerate a generated Lean file and compare it with the tracked file.

**The Prysm target ELF.** You must build it first (section 3).
Then these checks can run:

- The link check of the Prysm link set `prysm/go1.26.10/link-set`.
  `gen/checks/link_set.py` makes the set again from the ELF, its disassembly, its symbol listing and the item table `prysm/go1.26.10/link-set.tsv`.
  Then `link/check.py` runs on the set.
  `link/README.md` section 7 tells how to add a function or a data item.

```sh
python3 -I -B fv/kraken/gen/checks/link_set.py <scratch>/link-set <elf> <objdump> <nm>
python3 -B fv/kraken/link/check.py <scratch>/link-set
python3 -B fv/kraken/link/check.py --selftest <scratch>/link-set
```

- The link check needs `llvm-objdump` and `clang`.
  The self-test changes copies of the link set.
  Each changed copy must fail, and the unchanged copy must pass.

- The method list of the inventory: `python3 -I -B fv/kraken/gen/tools/proof_inventory.py methods <nm-listing> <scratch>/ssz-methods.json`.
  Compare the output with `prysm/go1.26.10/ssz-methods.json`.

**A Prysm tree and Go 1.26.10.** `gen/checks/differential.py` writes the Go differential cases, one file per Go type (`prysm/differential-cases/`).
The Go program `gen/checks/differential-main.go.txt` runs them as a package of a Prysm tree.
`differential.py check` compares the output.
These runs check Go semantics on the host.
They do not run the amd64 machine code.
`gen/prysm-rebuild-and-check.sh` runs all steps, with a negative control.

## 6. Known limits

`FINDINGS.md` lists every open limit with its effect and its place.
These are the main ones:

- No run on x86-64 hardware.
  No test compares Kraken with a real CPU.
- The runtime contracts are not proved on the compiled runtime.
  They are hypotheses.
- Some paths have no theorem.
  The premises exclude the stack growth path and the write barrier path.
  The hash tree root methods have no theorems.
- The growslice contract gives no lower bound on the remaining heap.
  One encoder state after a second growth is not proved.
- The accept kind does not constrain the frame size.
  Only `gen/generator/kindcheck.py` checks it.
- The negative suite with Lean runs only on Linux.
- The Prysm ELF and its symbol listing are not in the repository.
  The Prysm link checks need them (section 3).

## 7. Kinds of tracked files

This table has one row for each kind of tracked file under `fv/kraken/`.
It says who writes the file, the command that makes it again, and what checks it.
Paths and commands are relative to `fv/kraken/`.
`<T>` is a Go type name.
"Hand" means that a person writes the file. "None" means that no tool or check exists.
A tool-written file must equal a fresh run of its tool.
`gen/checks/regenerate_and_compare.py` compares all Python-written Lean files.
Do not edit a tool-written file by hand.
Change the tool and run it again.

### Lean modules of a type: `lean/Prysm/<T>/`

| Kind | Written by | Command that makes it again | What checks it |
| --- | --- | --- | --- |
| `Code.lean` | Hand | None | The build, the link check of its `.S` files, `gen/tools/proof_inventory.py` |
| `Layout.lean` | `gen/checks/layout.py` (Checkpoint), `gen/checks/attestation_data_layout.py` (AttestationData) | `python3 -I gen/checks/layout.py > lean/Prysm/Checkpoint/Layout.lean` | `regenerate_and_compare.py`, the build |
| `Spec.lean` | Hand. For the types of the table `T` of `gen/flat-types/flat_types_spec.py`: that tool | `python3 -I -B gen/flat-types/flat_types_spec.py lean` | The build, the axioms gate, `regenerate_and_compare.py` |
| `SpecDescription.lean`, `SpecDefinitions.lean` | Hand, from consensus-specs | None | The build, a review against consensus-specs |
| `SpecChecker.lean` | `gen/checks/desc_to_lean.py` or `gen/checks/list_desc_to_lean.py` (named in its header) | `python3 -I gen/checks/desc_to_lean.py prysm/go1.26.10/evidence/<package>.<T>.desc.json checkerDesc > lean/Prysm/<T>/SpecChecker.lean` | `regenerate_and_compare.py`, the build |
| `SpecEquivalence.lean` | Hand | None | The build, the axioms gate |
| `GeneratedDecodeAccept.lean` | `gen/generator/generator.py`: mode `uint64` for ValidatorIndex, `decoder --whole-accept` for the other types | `sh gen/generator/gen.sh` for its types. For the types of `gen/flat-types/run_generators.sh`: `sh gen/flat-types/run_generators.sh <out dir>`, then copy `<out dir>/<T>.whole-accept.lean` when `<T>.whole-accept.rc` is 0 | The build, `gen/generator/kindcheck.py`, `regenerate_and_compare.py`, the axioms gate, the negative cases |
| `GeneratedEncodeFastPath.lean` | `gen/generator/generator.py encoder --fast-path` | As for `GeneratedDecodeAccept.lean`, with `<T>.fast-path.lean` | The build, `kindcheck.py`, `gen/checks/fast_path_layout.py`, `regenerate_and_compare.py`, the negative cases |
| `DecodeSpec.lean` | Hand. For the types of the list `DEC` of `gen/flat-types/flat_types_decode_spec.py`: that tool | `python3 -I -B gen/flat-types/flat_types_decode_spec.py lean` | The build, the axioms gate, `regenerate_and_compare.py` |
| `WitnessGeneratedDecodeAccept.lean`, `WitnessGeneratedDecodeRejectSize.lean` | Hand. For the default type list of `gen/flat-types/flat_types_witness.py`: that tool | `python3 -I -B gen/flat-types/flat_types_witness.py .` | The build, the axioms gate, `regenerate_and_compare.py`, `proof_inventory.py` |
| `GeneratedEncodeFastPathSpec.lean`, `WitnessGeneratedEncodeFastPath.lean` | `gen/flat-types/flat_types_encode_spec.py`, for every type of its table `TYPES` | `python3 -I -B gen/flat-types/flat_types_encode_spec.py lean lean` | The build, the axioms gate, `regenerate_and_compare.py` |
| `EncodeLayout.lean` (BeaconBlockHeader, Eth1Data), `encodeLayout` in `Checkpoint/EncodeFastPathKindInstances.lean` | Hand. `gen/generator/gen.sh` gives it to the generator with `--hand-layout` | None | The build, `kindcheck.py` rule 13, `fast_path_layout.py` |
| `GeneratedEncodeFastPathSameAsHand.lean`, `Uint64DecoderKindSameAsHand.lean`, `EncodeFastPathStatements.lean` | Hand | None | The build (each identity is `rfl`) |
| Hand proof modules: `DecodeAccept.lean`, `DecodeReject*.lean`, `Encode*.lean`, `Statements*.lean`, the other `Witness*.lean` | Hand | None | The build, the axioms gate and its hand lists, the negative cases |
| `*.S` in a type directory | Hand: a runtime model for the witnesses of the type | None | The build: a theorem shows that the model satisfies its contract |

### Other Lean files

| Kind | Written by | Command that makes it again | What checks it |
| --- | --- | --- | --- |
| `lean/Spec/`, `lean/Machine/`, `lean/Runtime/`, `lean/Codec/` (except `Codec/Kind/`) | Hand | None | The build, the axioms gate |
| `lean/Codec/Kind/*.lean` | Hand | None | The build. `kindcheck.py` checks that a `_kind` line names one of these kinds |
| `lean/Prysm/ElfData/PrysmTarget.lean` | Hand: one `data_include <id>` line for each data file | None | The build (`data_include` reads each file), `gen/checks/deposit_data_include_check.py` |
| `lean/Prysm/RuntimeModel/*` | Hand | None | The build |
| `lean/lakefile.toml`, `lean/lean-toolchain` | Hand. A change needs user approval | None | The build |
| `lean/lake-manifest.json` | Lake | None | The build |

### Target files: `prysm/`

| Kind | Written by | Command that makes it again | What checks it |
| --- | --- | --- | --- |
| `prysm/go1.26.10/link-set.tsv` | Hand | None | `gen/checks/link_set.py` checks each data row against the converted code (needs the ELF) |
| `prysm/go1.26.10/link-set/**`: `target.objdump`, `norm/*.S`, `data/*.data` | `gen/checks/link_set.py` | `python3 -I -B gen/checks/link_set.py <scratch>/link-set <elf> <objdump> <nm>`, then copy into `prysm/go1.26.10/link-set` | `link/check.py`, `gen/prysm-rebuild-and-check.sh` |
| `prysm/go1.26.10/link-set/RESULT` | `link/check.py` | `python3 -B link/check.py <scratch>/link-set` | `gen/prysm-rebuild-and-check.sh` compares it. `proof_inventory.py` reads it |
| `prysm/go1.26.10/build-ids.txt` | `gen/prysm-elf.sh` (its `BUILD-INFO`). Do not change it | `sh gen/prysm-elf.sh <prysm-tree> <elf-out> <empty-gocache-dir>` | `gen/prysm-rebuild-and-check.sh` step 1 |
| `prysm/go1.26.10/functions.json` | `gen/mnemonics.py` | Section 3 | None |
| `prysm/go1.26.10/parser-result.json` | `gen/kraken-parser/summarize_parser_log.py` | Section 3 | None |
| `prysm/go1.26.10/ssz-methods.json` | `gen/tools/proof_inventory.py methods` | `python3 -I -B gen/tools/proof_inventory.py methods <nm> prysm/go1.26.10/ssz-methods.json` | The tool checks the sha256 of the symbol listing against `build-ids.txt` |
| `prysm/go1.26.10/prysm-target-main.go.txt` | `gen/keepalive.py` | `python3 -I gen/keepalive.py prysm/inventory.json prysm/go1.26.10/prysm-target-main.go.txt` | None |
| `prysm/go1.26.10/prysm-go.mod.diff` | Hand | None | The ELF sha256 of a rebuild (section 3) |
| `prysm/go1.26.10/evidence/<package>.<T>.desc.json` | `gen/desc/producer.py`: copies of `<work-dir>/orig/` of `gen/desc/test_desc.py prepare` | `python3 -I gen/desc/test_desc.py prepare <work-dir>`, with a relative `<work-dir>` | The sha256 in the header of `SpecChecker.lean` and in `gen/desc/results/main.result.json` |
| `prysm/ir/ir-mainnet.json`, `prysm/ir/ir-minimal.json` | `gen/type_inventory.py reduce` | Section 3 | The sha256 in the header of each generated module. `kindcheck.py` compares it |
| `prysm/inventory.json` | `gen/type_inventory.py build` | `python3 -I gen/type_inventory.py build prysm` | None |
| `prysm/TYPES.md` | `gen/type_list_document.py` | `python3 -I gen/type_list_document.py prysm` | None |
| `prysm/type-scope.json`, `prysm/type-scope.md` | `gen/type_scope.py` | `python3 -I gen/type_scope.py .` | None |
| `prysm/proof-inventory.md`, `prysm/proof-inventory.json` | `gen/tools/proof_inventory.py run` | Section 5 (needs Lean) | The tool fails when a mapped theorem is missing or has another axiom |
| `prysm/_generated/**` | `gen/prysm-gen.sh` (its `<out>/gen/`). No tool writes `SHA256SUMS` | `sh gen/prysm-gen.sh <prysm-tree> <generator-binary> <out> gen`, then copy | `cd prysm/_generated && sha256sum -c SHA256SUMS` |
| `prysm/diff/generated-go-diff.json` | `gen/generated_go_diff.py` | `python3 -I gen/generated_go_diff.py <prysm-tree> <out>/gen <out dir>` | None |
| `prysm/differential-cases/*.json` | `gen/checks/differential.py cases` | `python3 -I -B gen/checks/differential.py cases <dir>`, then compare with `diff -r` | `gen/prysm-rebuild-and-check.sh` step 4, and the Go program (section 5) |

### Check inputs: `gen/`

| Kind | Written by | Command that makes it again | What checks it |
| --- | --- | --- | --- |
| `gen/axioms-lists/*.lean` | Hand. `gen/flat-types/flat_types_hand_list.py` adds names of its types to `flat-fixed-size-types.lean` | `python3 -I gen/flat-types/flat_types_hand_list.py <dump.tsv> gen/axioms-lists/flat-fixed-size-types.lean <module list>` | `gen/checks/axioms_gate.py run`: each name is in the dump and has only the standard axioms |
| `gen/checks/negative-cases/*.json` | Hand. `gen/flat-types/flat_types_negative_cases.py` writes `negative-cases-flat-types.json` | `python3 -I -B gen/flat-types/flat_types_negative_cases.py lean gen/checks/negative-cases/negative-cases-flat-types.json` | `negative.py --check-cases` and `negative_case_ranges.py` (in `python_checks.sh`), `regenerate_and_compare.py`, the run of `negative.py` with Lean |
| `gen/desc/results/main.result.json` | `gen/desc/run_desc_checker.sh` (its `<work-dir>/main.result.json`) | `gen/desc/test_desc.py prepare`, then `run_desc_checker.sh` (needs Lean), then copy | `gen/desc/test_desc.py evaluate` on the work directory |
| `gen/desc/hand-types-ir.json`, `gen/desc/hand-types-references.json` | Hand | None | The `Desc` checker tests (`gen/README.md` section 5) |
