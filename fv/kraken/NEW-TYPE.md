# Prove a new type

This document gives the steps to prove the SSZ methods of a new Prysm type.
Do the steps in this order.
Each step says what you make, the command or the file, what checks it, and the result to expect.
Run the commands from the repository root, unless a command starts with `cd`.
Paths without `fv/kraken/` are relative to `fv/kraken/`.
`<T>` is the Go type name, for example `HistoricalSummary`.

Two finished types show the two paths:

- The generated path: `lean/Prysm/HistoricalSummary/`.
  A generator writes `GeneratedDecodeAccept.lean` and `GeneratedEncodeFastPath.lean`.
  `gen/flat-types/flat_types_encode_spec.py` writes `GeneratedEncodeFastPathSpec.lean` and `WitnessGeneratedEncodeFastPath.lean`.
  A person writes `Code.lean`, `SpecDescription.lean`, `Spec.lean`, `DecodeSpec.lean` and the two decoder witnesses.
  `gen/checks/desc_to_lean.py` writes `SpecChecker.lean`.
- The hand path: the decoder of `lean/Prysm/Checkpoint/`.
  A person writes `DecodeAccept.lean`, `DecodeRejectSize.lean`, `DecodeSpec.lean`, `WitnessDecodeAccept.lean` and `WitnessDecodeRejectSize.lean`.

`README.md` section 7 gives the writer and the check of each kind of file.
`lean/README.md` section 8 gives the module and theorem names.

## 1. The type is in the inventory, and its code is in the ELF

What you check: the full Go type name is in the list `sets.inventory_types` of `prysm/inventory.json`.
It is a key of `per_type` in `prysm/go1.26.10/functions.json`, with one entry for each method.
Each method has the status `OK` in `prysm/go1.26.10/parser-result.json`.

```sh
python3 -I -c "import json; print('github.com/OffchainLabs/prysm/v7/proto/prysm/v1alpha1.HistoricalSummary' in json.load(open('fv/kraken/prysm/inventory.json'))['sets']['inventory_types'])"
python3 -I -c "import json; print(sorted(json.load(open('fv/kraken/prysm/go1.26.10/functions.json'))['per_type']['github.com/OffchainLabs/prysm/v7/proto/prysm/v1alpha1.HistoricalSummary']))"
grep -n -A3 'v1alpha1.(\*HistoricalSummary).UnmarshalSSZ' fv/kraken/prysm/go1.26.10/parser-result.json
```

Expected: `True`, then the list `['MarshalSSZTo', 'SizeSSZ', 'UnmarshalSSZ']`, then a line `"status": "OK"`.
If the type is not in the inventory, its code is not in the pinned ELF.
A new ELF needs user approval.
If the status is not `OK`, the Kraken parser cannot read the function (`FINDINGS.md`, entry "Kraken cannot parse `bsr`").
`README.md` section 3 tells how these files are made again.

## 2. The link set holds the functions and the data items

What you make: rows in the item table `prysm/go1.26.10/link-set.tsv`.
Add one `function` row for each method that a proof reads.
HistoricalSummary has the rows of `UnmarshalSSZ` and `MarshalSSZTo`.
Add one `data` row for each data item that the code reads.
Examples are an error global and a format string.
`link/README.md` section 7 gives the procedure, and `gen/checks/link_set.py` gives the columns in its usage text.

The commands need the Prysm ELF, its disassembly and its symbol listing (`README.md` section 3):

```sh
python3 -I -B fv/kraken/gen/checks/link_set.py <scratch>/link-set <elf> <objdump> <nm>
python3 -B fv/kraken/link/check.py <scratch>/link-set
```

Expected: `check.py` exits 0, and the last check line of `RESULT` is `PASS all`.
Then copy the new set to `prysm/go1.26.10/link-set`.
For each data item that a proof reads, add a `data_include <id>` line to `lean/Prysm/ElfData/PrysmTarget.lean`.
A data file that no proof reads needs no line.

## 3. `Code.lean`

What you make: `lean/Prysm/<T>/Code.lean` by hand.
It has one `include_x64_code` constant for each method that a proof reads, for example `Code.unmarshalSSZ` and `Code.marshalSSZTo`.
Take `lean/Prysm/HistoricalSummary/Code.lean` as the model: `namespace Prysm.<T>` and `def Code.<method>`.
The path of each `.S` file is relative to `fv/kraken/lean`.

```sh
cd fv/kraken/lean && lake build Prysm.HistoricalSummary.Code
```

Expected: exit 0.
The Kraken parser reads the `.S` files when Lean elaborates the module.

## 4. The specification side

What you make, in this order:

1. The hand `Desc` in `lean/Prysm/<T>/SpecDescription.lean`, written by hand from consensus-specs.
   Write it before you read the checker `Desc`.
   Quote the consensus-specs container in the module text.
   Example: `lean/Prysm/HistoricalSummary/SpecDescription.lean`.
2. The checker `Desc`.
   `gen/desc/test_desc.py prepare` runs the producer `gen/desc/producer.py` on every inventory type.
   `gen/desc/run_desc_checker.sh` runs the checker (needs Lean).
   `gen/desc/test_desc.py evaluate` checks its result.
   The work directory is a relative path under `fv/kraken/lean`, for example `desc-work`.
   So the checker result holds no machine path.
   Delete the directory with `trash` after the copy below.

   ```sh
   cd fv/kraken/lean && python3 -I ../gen/desc/test_desc.py prepare desc-work
   cd fv/kraken/lean && sh ../gen/desc/run_desc_checker.sh desc-work .
   cd fv/kraken/lean && python3 -I ../gen/desc/test_desc.py evaluate desc-work desc-work/evaluate.json
   ```

   Expected: `run_desc_checker.sh` prints `main 0` and `batch 0`.
   `evaluate` exits 0.
   Copy `desc-work/orig/<package>.<T>.desc.json` to `prysm/go1.26.10/evidence/`.
   Copy `desc-work/main.result.json` to `gen/desc/results/main.result.json`.
   Then write `SpecChecker.lean` (from `fv/kraken`; use `list_desc_to_lean.py` for a type with vectors, lists or bit vectors):

   ```sh
   python3 -I gen/checks/desc_to_lean.py prysm/go1.26.10/evidence/prysm_v1alpha1.HistoricalSummary.desc.json checkerDesc > lean/Prysm/HistoricalSummary/SpecChecker.lean
   ```

3. `lean/Prysm/<T>/Spec.lean`: the structure `SszValue`, `SszValue.toValue`, `SszValue.encode` and the bridge lemmas.
   The tools of `gen/flat-types/` read `desc`, `SszValue.serialize_eq`, `SszValue.spec_rejects` and `SszValue.spec_accepts_iff`.
   It also holds the codec equality of `desc` and `checkerDesc`, for example `desc_serialize_checker`.
   Example: `lean/Prysm/HistoricalSummary/Spec.lean`.
   For a flat type of uint64 and byte vector fields, `gen/flat-types/flat_types_spec.py` can write it.
   Add the type to its table `SPEC_TYPES`, then run `python3 -I -B gen/flat-types/flat_types_spec.py lean` from `fv/kraken`.

What checks it: the build of these modules, and the axioms gate (step 7).
No tool checks the hand `Desc` against consensus-specs.
A reviewer reads it (`FINDINGS.md`).

## 5. The generator

What you make: one row for the type in one of two driver scripts.

- `gen/flat-types/run_generators.sh`: a row `<package> <T>` (`v1` or `v1alpha1`), for example `v1alpha1 ValidatorIdentity`.
  Choose it for a flat type when the tools of `gen/flat-types/` write its specification, decoder corollary and witnesses.
  The script writes into a scratch directory.
  Copy each output whose `.rc` file holds 0.
- `gen/generator/gen.sh`: the type name in the `decoder --whole-accept` loop and in the `encoder --fast-path` loop, for example `HistoricalSummary`.
  Choose it for a `v1alpha1` type when you write its specification, decoder corollary and decoder witnesses by hand.
  A row can give options: `--hand-layout` with `--hand-layout-src`, and `--same-as` with `--same-as-via`.
  The script writes into `lean/Prysm/<T>/` directly.

```sh
mkdir <scratch>/flat-out && sh fv/kraken/gen/flat-types/run_generators.sh <scratch>/flat-out
sh fv/kraken/gen/generator/gen.sh
```

Expected for a row of `run_generators.sh`: `ValidatorIdentity.whole-accept.rc` and `ValidatorIdentity.fast-path.rc` hold 0.
Expected for a row of `gen.sh`: `gen.sh` exits 0.
It writes `lean/Prysm/HistoricalSummary/GeneratedDecodeAccept.lean` and `lean/Prysm/HistoricalSummary/GeneratedEncodeFastPath.lean`.

Exit 2 is a refusal.
The generator writes nothing to standard output.
The last line of `<T>.whole-accept.stderr` or `<T>.fast-path.stderr` gives the reason, for example `byte vector of 20 bytes`.
`FINDINGS.md`, entry "The proof generator covers only some code forms", lists the covered forms.
Do not add a refused type to `gen.sh`: its output redirect writes an empty file, and the script stops.
A refused method needs hand proofs with the roles `DecodeAccept`, `DecodeRejectSize`, `EncodeFastPath` and their witnesses.
Put the statements first in a `Statements` module.
`lean/Prysm/SyncAggregate/` is the model of a hand decoder.
Its `Statements.lean` holds the statements.
`DecodeAccept.lean` and `DecodeRejectSize.lean` prove them from the `Codec` segment lemmas.
`Codec/FixedBytesDecode.lean` covers byte vectors of 32, 48 and 96 bytes.
For another size, prove the segment lemma in the type directory.
`lean/Prysm/SyncAggregate/DecodeFieldSegments.lean` does this for 64 bytes: `bytes_decode_segment_offset_zero_size64`.
It has the statement of `Codec.bytes_decode_segment_offset_zero` with `hn : n = 64`, and the proof method of `Codec/FixedBytesDecode.lean`.
A generator change needs user approval.

What checks it: `gen/generator/kindcheck.py` (step 7).
It recomputes the kind parameters from the `.S` file and the IR.

## 6. The proofs that the generator does not write

What you make:

- `lean/Prysm/<T>/DecodeSpec.lean`: `Decode.accept_spec`, `Decode.reject_size_spec` and `Decode.reject_complete`.
  They connect `Decode.generated_accept` and `Decode.generated_reject` to EthLib.
  Example: `lean/Prysm/HistoricalSummary/DecodeSpec.lean`.
- `WitnessGeneratedDecodeAccept.lean` and `WitnessGeneratedDecodeRejectSize.lean`: a concrete state for each main theorem.
  Examples: the two files of `lean/Prysm/HistoricalSummary/`.
  For a variable length, cover the empty value, one element and the maximum.
- `GeneratedEncodeFastPathSpec.lean` and `WitnessGeneratedEncodeFastPath.lean`: the encoder corollary and its witness.

A person writes the first two for the types of `gen.sh`.
Tools write them for a type of `run_generators.sh`.
Add a type of `run_generators.sh` to every table of this list.
A type whose decoder the generator refuses goes only into the tables of the encoder, as BuilderPreferences does.

| File | Table | What the table gives |
| --- | --- | --- |
| `gen/flat-types/run_generators.sh` | the rows after `<<'TYPES'` | The generator runs. `gen/checks/regenerate_and_compare.py` reads these rows |
| `gen/flat-types/flat_types_spec.py` | `SPEC_TYPES` | The Go type and the fields. The decoder and witness tools read this table too |
| `gen/flat-types/flat_types_decode_spec.py` | `DECODE_SPEC_TYPES` | The types that get `DecodeSpec.lean` |
| `gen/flat-types/flat_types_witness.py` | `WITNESS_TYPES` and `ASSEMBLY_NAMES` | The types that get the two decoder witnesses, and the name of the `.S` file |
| `gen/flat-types/flat_types_witness.py` | the frame forms in `__main__` | The accept witness form: frame `0x38`, frame `0x20`, or the frame with slices and callees |
| `gen/flat-types/flat_types_encode_spec.py` | `ENCODE_SPEC_TYPES` | Every type with a generated fast path, also the types of `gen.sh` |
| `gen/flat-types/flat_types_negative_cases.py` | `DECODER_CASE_TYPES` and `ENCODER_CASE_TYPES` | The negative cases of the decoder and of the encoder |
| `gen/flat-types/flat_types_hand_list.py` | `HAND_LIST_TYPES` | The names that go into `gen/axioms-lists/flat-fixed-size-types.lean` |

From `fv/kraken`:

```sh
python3 -I -B gen/flat-types/flat_types_spec.py lean
python3 -I -B gen/flat-types/flat_types_decode_spec.py lean
python3 -I -B gen/flat-types/flat_types_witness.py .
python3 -I -B gen/flat-types/flat_types_encode_spec.py lean lean
python3 -I -B gen/flat-types/flat_types_negative_cases.py lean gen/checks/negative-cases/negative-cases-flat-types.json
```

Expected: exit 0 for each tool.
`flat_types_hand_list.py` needs the declaration dump of the axioms gate (step 7).
What checks it: the build and the axioms gate (step 7), and `regenerate_and_compare.py` for the tool-written files.

## 7. The checks

Run all of them.
A check that did not run is "not run" in the pull request.

1. Build, then the freshness check:

   ```sh
   cd fv/kraken/lean && lake build Machine Runtime Codec Spec Prysm
   cd fv/kraken/lean && lake build --no-build Machine Runtime Codec Spec Prysm
   ```

   Expected: exit 0 for both.
2. The axioms gate, with a hand list entry.
   Add the imports and one `#print axioms <name>` line for each main theorem and witness to a file of `gen/axioms-lists/`.
   For a type of `HAND_LIST_TYPES`, `gen/flat-types/flat_types_hand_list.py` adds the lines to `flat-fixed-size-types.lean`:
   `python3 -I gen/flat-types/flat_types_hand_list.py <dump.tsv> gen/axioms-lists/flat-fixed-size-types.lean <module list>`.
   For any other new type, make a new file `gen/axioms-lists/<type>.lean`.
   `<type>` is the Go type name in lower case, with `-` between the words.
   An example is `gen/axioms-lists/historical-batch.lean`.
   The gate reads every `*.lean` file of the directory.

   ```sh
   python3 -I -B fv/kraken/gen/checks/axioms_gate.py run <scratch>/gate.json <scratch>/dump.tsv
   ```

   Expected: exit 0 and a line that starts with `PASS declarations`, with `missing []` and `nonstandard 0`.
3. The kind check of the generated files:

   ```sh
   python3 -I -B fv/kraken/gen/generator/kindcheck.py fv/kraken/lean/Prysm/HistoricalSummary/GeneratedDecodeAccept.lean fv/kraken/lean/Prysm/HistoricalSummary/GeneratedEncodeFastPath.lean
   ```

   Expected: exit 0 and one line `PASS <file> …` for each file.
4. The regeneration comparison.
   It covers the rows of `gen.sh`, `run_generators.sh` and the tools of `gen/flat-types/`:

   ```sh
   python3 -I -B fv/kraken/gen/checks/regenerate_and_compare.py <scratch>/regen-work > <scratch>/regen.txt
   ```

   Expected: every line starts with `EQ`.
5. The negative cases.
   Add one control and at least one mutant for each main theorem.
   For a type of `DECODER_CASE_TYPES` or `ENCODER_CASE_TYPES`, `flat_types_negative_cases.py` writes them into `negative-cases-flat-types.json`.
   For any other new type, make a new file `gen/checks/negative-cases/negative-cases-<type>.json`, with the type name as in step 2.
   An example is `negative-cases-historical-batch.json`.
   `python_checks.sh` reads every tracked file with `negative-cases` in its name.
   A control has `id`, `module`, `theorem` and `kind: "control"`.
   A statement mutant also has `old` and `new`: a text that occurs once in the statement, and its change.
   A code mutant has `code_definition`, `assembly`, `old` and `new` (`gen/checks/negative.py` usage text).
   `assembly` is the name of the `.S` file in `prysm/go1.26.10/link-set/norm`.
   The id is the Go type in lower case, the theorem without its type namespace, the kind and the change.
   An example is `historical-summary-decode-generated-accept-statement-hav-64-to-32`.
   The Python checks of the case files run in `python_checks.sh` (item 6).
   The run with Lean needs Linux (`FINDINGS.md`).
   Run one case per job:

   ```sh
   python3 -I -B fv/kraken/gen/checks/negative.py <cases.json> <work-dir> <scratch>/result.json <case-id>
   ```

   Expected: the class `control_pass` for a control and `inside` for a mutant.
6. The Python checks:

   ```sh
   sh fv/kraken/gen/checks/python_checks.sh <scratch>/python-checks
   ```

   Expected: every line of `<scratch>/python-checks/summary.txt` ends with `rc=0`.
7. The proof inventory: run the commands of `README.md` section 5 (needs a built tree and the gate JSON).
   `gen/tools/proof_inventory.py` derives the row of a type from its directory `lean/Prysm/<T>/` and the theorem names.
   The directory name must be a Go type of `prysm/go1.26.10/ssz-methods.json`, else the tool prints a `FAIL` line.
   The theorems must have the names of `lean/README.md` section 8, the candidates of `DEC_CANDIDATES`, `ENC_FORMS` and `SIZE_FORM`.
   An encoder theorem outside the fast path needs an entry in `ENC_EXTRA`.
   The entry gives a premise text for each theorem and a text of what is not proved.
   Without that entry, a theorem with a name of `ENC_UNCLASSIFIED` shows in the row as not classified.
   `GENERATOR_REFUSED` gives the reason why the generators refuse a flat type.
   Change the entry of the type when the generator result of the type changes.
   Do not add the type to `CORE_FLAT_TYPES`: it is a fixed list.
   Expected: `gen/tools/proof_inventory.py run` exits 0, and `prysm/proof-inventory.md` has a row for the type.
8. The link check of step 2, when the link set changed (needs the ELF).

## 8. The pull request

`fv/AGENTS.md` gives the rules.
In short:

- One issue on `syjn99/methodical-ssz` holds one type or one unit.
  The branch is `u/<issue number>-<type name>`, from `fv`.
- A unit changes only `lean/Prysm/<T>/`, the negative cases of that type and the generator rows of that type.
  It does not change `Machine`, `Runtime`, `Codec` or `Spec`.
  Keep a general lemma in the type directory and name it in the pull request.
- The title is `<type>(kraken): <summary>`.
  The body has the sections `Problem` and `Solution`, with three bullets at most each.
- Add a `Not run` line for each check that did not run.
  The last line of the body states the authoring model.
- Open the pull request against `fv` with `Closes #<issue number>`.
  The CI workflow `fv-lean.yaml` runs the build and the axioms gate.
- A session that did not write the change reviews it.
  It reads each new theorem statement against the EthLib definition.
- Each main theorem has a witness.
  Without a witness, the theorem is not complete.
