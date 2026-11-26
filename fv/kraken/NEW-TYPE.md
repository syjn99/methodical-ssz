# Prove a new type

This document gives the steps to prove the SSZ methods of a new Prysm type.
Do the steps in this order.
Each step says what you make, the command or the file, what checks it, and the result to expect.
Run the commands from the repository root, unless a command starts with `cd`.
Paths without `fv/kraken/` are relative to `fv/kraken/`.
`<T>` is the Go type name, for example `HistoricalSummary`.

Finished types show the paths:

- The generated path: `lean/Prysm/HistoricalSummary/`.
  A generator writes `GeneratedDecodeAccept.lean` and `GeneratedEncodeFastPath.lean`.
  `gen/flat-types/flat_types_encode_spec.py` writes `GeneratedEncodeFastPathSpec.lean` and `WitnessGeneratedEncodeFastPath.lean`.
  A person writes `Code.lean`, `SpecDescription.lean`, `Spec.lean` and `WitnessGeneratedDecodeAccept.lean`.
  `gen/flat-types/flat_types_decode_spec.py` writes `DecodeSpec.lean`, and `gen/flat-types/flat_types_witness.py` writes `WitnessGeneratedDecodeRejectSize.lean`.
  `gen/checks/desc_to_lean.py` writes `SpecChecker.lean`.
- The hand path of a decoder: `lean/Prysm/HistoricalBatch/`.
  A person writes `Statements.lean` (the statements), `DecodeAccept.lean`, `DecodeRejectSize.lean` and `DecodeSpec.lean`.
  `DecodeSpec.lean` holds `Decode.accept_spec`, `Decode.reject_size_spec` and `Decode.reject_complete`.
  `WitnessDecodeAccept.lean` and `WitnessDecodeRejectSize.lean` are the witnesses of the two main theorems.
- The hand path of an encoder fast path: `lean/Prysm/DataColumnsByRootIdentifier/`.
  A person writes `StatementsEncode.lean`, `EncodeFastPath.lean` (`Encode.fast_path`), `EncodeSpec.lean` (`Encode.fast_path_spec`) and `WitnessEncodeFastPath.lean`.

`README.md` section 7 gives the writer and the check of each kind of file.
`lean/README.md` section 8 gives the module and theorem names.

## 1. The code of the type is in the ELF

What you check: the list `functions` of `prysm/go1.26.10/functions.json` has one entry for each method of the type.
This list holds every function of the ELF that has a `.S` text.
Each method has the status `OK` in `prysm/go1.26.10/parser-result.json`.
The third command tells if the type is in the type inventory.

```sh
python3 -I -c "import json, sys; print(sorted((f['package'].rsplit('/', 1)[1], f['method'], f['kind']) for f in json.load(open('fv/kraken/prysm/go1.26.10/functions.json'))['functions'] if f['type'] == sys.argv[1]))" HistoricalSummary
grep -n -A3 'v1alpha1.(\*HistoricalSummary).UnmarshalSSZ' fv/kraken/prysm/go1.26.10/parser-result.json
python3 -I -c "import json, sys; print([t for t in json.load(open('fv/kraken/prysm/inventory.json'))['sets']['inventory_types'] if t.endswith('.' + sys.argv[1])])" HistoricalSummary
```

Expected for HistoricalSummary: the list `[('v1alpha1', 'MarshalSSZTo', 'generated'), ('v1alpha1', 'SizeSSZ', 'generated'), ('v1alpha1', 'UnmarshalSSZ', 'generated')]`.
Then the lines `"group": "inventory"` and `"status": "OK"`, and the full Go type name in a list.
If the first list is empty, the code of the type is not in the pinned ELF.
A new ELF needs user approval.
If the status is not `OK`, the Kraken parser cannot read the function (`FINDINGS.md`, entry "Kraken cannot parse `bsr`").
`README.md` section 3 tells how these files are made again.

The type inventory is the list `sets.inventory_types` of `prysm/inventory.json`.
It holds the generated types in the field closure of the fork configuration types.
The ELF also holds the code of types outside the inventory.
The `group` of `parser-result.json` tells the kind of a function: `inventory`, `generated (not inventory)` or `hand-written`.
For ValidatorIdentity, the first command gives the same three methods, the group is `generated (not inventory)`, and the last list is empty.
For Slot, the first command gives four methods of the kind `hand-written`, from `consensus-types/primitives`.

A type outside the inventory has its code in the ELF, but it lacks these items:

- It has no key in `per_type` of `prysm/go1.26.10/functions.json`, and no record in the list `types` of `prysm/inventory.json`.
- `gen/desc/test_desc.py prepare` writes no `Desc` file for it, and the `Desc` checker has no record of it.
  So step 4.2 does not exist for it.
  The type has no `SpecChecker.lean` and no codec equality with a checker `Desc`, as `lean/Prysm/ValidatorIdentity/` shows.
- A hand-written type of `consensus-types/primitives` (Epoch, Slot, CommitteeIndex, ValidatorIndex) also has no entry in the IR.
  So the generator modes that read the IR do not apply to it (step 5).
  The `Desc` producer reads only the IR, so the type has no checker `Desc`.
  Thus the proof inventory does not ask for a codec equality for its decoder (step 7).

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
   The module holds only `desc` and the definitions that only the description needs.
   It imports `EthLib.Serialization.Ssz`, and the `SpecDescription` module of each nested type.
   If you write it from the Prysm proto definition, say so in the module text, as `lean/Prysm/ValidatorBalance/SpecDescription.lean` does.
   Such a `Desc` has the same source as the `Desc` producer, so it is not an independent specification (`FINDINGS.md`).
2. The checker `Desc`, for an inventory type only (step 1).
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
   Then write `SpecChecker.lean` (from `fv/kraken`):

   ```sh
   python3 -I gen/checks/desc_to_lean.py prysm/go1.26.10/evidence/prysm_v1alpha1.HistoricalSummary.desc.json checkerDesc > lean/Prysm/HistoricalSummary/SpecChecker.lean
   ```

3. `lean/Prysm/<T>/Spec.lean`: the structure `SszValue`, `SszValue.toValue`, `SszValue.encode` and the bridge lemmas.
   Its statements import this module for these definitions.
   Import the modules whose names the module uses, for example `Spec.TestScalars` and `Spec.DeserializeOfSerialize`.
   The tools of `gen/flat-types/` read `desc`, `SszValue.serialize_eq`, `SszValue.spec_rejects` and `SszValue.spec_accepts_iff`.
   For a type with a checker `Desc`, it also holds the codec equality of `desc` and `checkerDesc`, for example `desc_serialize_checker`.
   Example: `lean/Prysm/HistoricalSummary/Spec.lean`.
   For a flat type of uint64 and byte vector fields, with at least one uint64 field, `gen/flat-types/flat_types_spec.py` can write it.
   Give the companion `spec` in a row of the type in `gen/generator/types.tsv` (step 5).
   Add the fields to the tables `SPEC_TYPES` and `descnames` of the tool.
   Add the type to `DESC_FROM_CONSENSUS_SPECS` when its `SpecDescription.lean` is written from consensus-specs.
   Add it to `DESC_FROM_PRYSM_PROTO` when it is written from the Prysm proto definition.
   The tool stops with a message for a type in neither set.
   Then run `python3 -I -B gen/flat-types/flat_types_spec.py lean` from `fv/kraken`.

What checks it: the build of these modules, and the axioms gate (step 7).
No tool checks the hand `Desc` against consensus-specs.
A reviewer reads it (`FINDINGS.md`).

## 5. The generator

What you make: one row in `gen/generator/types.tsv` for each method of the type that the generator runs on.
`gen/generator/gen.sh` runs every row of the table.
The header comment of the table gives the columns, separated by one tab:

- `package`: `v1alpha1`, `v1` or `primitives`.
- `type`: the Go type name, for example `HistoricalSummary`.
- `mode`: `decoder --whole-accept` for `UnmarshalSSZ`, `encoder --fast-path` for `MarshalSSZTo`.
  The mode `uint64` is for a uint64 primitive decoder (below).
- `options`: more generator options, or `-`.
  A row can give `--hand-layout` with `--hand-layout-src`, and `--same-as` with `--same-as-via`.
  Give the module of the hand layout with `--imports=`.
- `expect`: `accept` or `refuse`.
- `companions`: the files that the tools of `gen/flat-types/` write for the type (step 6), or `-`.

First run the script with a scratch directory.
Nothing goes into the tree:

```sh
sh fv/kraken/gen/generator/gen.sh <scratch>/gen-out
```

`<scratch>/gen-out/HistoricalSummary.whole-accept.rc` and `HistoricalSummary.fast-path.rc` hold the exit codes of the generator.
Then give `accept` or `refuse` to each row, and run the script without a directory:

```sh
sh fv/kraken/gen/generator/gen.sh
```

Expected: exit 0.
It writes `lean/Prysm/HistoricalSummary/GeneratedDecodeAccept.lean` and `lean/Prysm/HistoricalSummary/GeneratedEncodeFastPath.lean`.
For a row with another result than its `expect` value, a message names the row and the script exits 1.

Exit 2 is a refusal.
The generator writes nothing to standard output.
The last line of `<T>.whole-accept.stderr` or `<T>.fast-path.stderr` gives the reason, for example `byte vector of 1 bytes`.
`FINDINGS.md`, entry "The proof generator covers only some code forms", lists the covered forms.
Keep the row of a refused method with `refuse`: then `gen.sh` checks that the generator still refuses it.
A refused method needs hand proofs with the roles `DecodeAccept`, `DecodeRejectSize`, `EncodeFastPath` and their witnesses.
Put the statements first in a `Statements` module.
The models are the hand paths of the header of this document.
The proofs use the `Codec` segment lemmas.
`Codec/FixedBytesDecode.lean` covers byte vectors of 32, 48 and 96 bytes.
For another size, prove the segment lemma in the type directory.
`lean/Prysm/SyncAggregate/DecodeFieldSegments.lean` does this for 64 bytes: `bytes_decode_segment_offset_zero_size64`.
It has the statement of `Codec.bytes_decode_segment_offset_zero` with `hn : n = 64`, and the proof method of `Codec/FixedBytesDecode.lean`.
A generator change needs user approval.

A hand decoder that calls a callee decoder uses the function specification of the callee.
`Codec/CalleeDecode.lean` gives the call block lemma `Codec.call_decode_segment`.
Its premise `Uint64CalleeAccept fn` is the form of `Decode.accept_function_spec` of the callee type, for example `Prysm.Epoch.Decode.accept_function_spec`.
The proof gives it with `Decode.accept_function_spec_holds` of the callee type.
`lean/Prysm/PendingPartialWithdrawal/DecodeAccept.lean` does this for the callees ValidatorIndex and Epoch.

A uint64 primitive decoder uses the mode `uint64` and the package `primitives`.
The `uint64` rows of `gen/generator/types.tsv` name ValidatorIndex, Epoch, Slot and CommitteeIndex.
The files of ValidatorIndex are the model:

- `Code.lean`, and `GeneratedDecodeAccept.lean` with `Decode.generated_accept` (the `uint64` mode writes it);
- `DecodeAcceptFunctionSpec.lean`: the hand function specification `Decode.accept_function_spec` and its proof `Decode.accept_function_spec_holds`;
- `DecodeRejectSize.lean`, `WitnessGeneratedDecodeAccept.lean` and `WitnessDecodeRejectSize.lean`;
- `SpecDescription.lean` with `desc := .uint 8`, and `DecodeSpec.lean` with `Decode.accept_spec`, `Decode.reject_size_spec` and `Decode.reject_complete`.
  The lemmas about `.uint 8` are in `Prysm/Epoch/Spec.lean`.

The CommitteeIndex decoder has another format string: the Prysm source spells it "receiced".
Its reject theorems use the data item `formatBufferLengthReceiced`.

What checks it: `gen/generator/kindcheck.py` (step 7).
For a `decoder --whole-accept` or `encoder --fast-path` file, it recomputes the kind parameters from the `.S` file and the IR.
For a `uint64` file, it does not recompute parameters.
The kind `Codec.uint64DecodeAcceptKind` has only the code constant as parameter.
`kindcheck.py` checks that `Decode.generated_accept_kind` names this kind, the code constant of the theorem and the fixed proof line.
The proof checks the code itself, through its code facts (`gen/README.md` section 4).

## 6. The proofs that the generator does not write

What you make:

- `lean/Prysm/<T>/DecodeSpec.lean`: `Decode.accept_spec`, `Decode.reject_size_spec` and `Decode.reject_complete`.
  They connect `Decode.generated_accept` and `Decode.generated_reject` to EthLib.
  Example: `lean/Prysm/HistoricalSummary/DecodeSpec.lean`.
- `WitnessGeneratedDecodeAccept.lean` and `WitnessGeneratedDecodeRejectSize.lean`: a concrete state for each main theorem.
  Examples: the two files of `lean/Prysm/HistoricalSummary/`.
  For a variable length, cover the empty value, one element and the maximum.
- `GeneratedEncodeFastPathSpec.lean` and `WitnessGeneratedEncodeFastPath.lean`: the encoder corollary and its witness.

A tool writes a file of this list for a type when a row of the type names the companion of the file.
A person writes the file for a type without the companion.
`FINDINGS.md`, entry "Some companion files of generated types are written by a person", gives these types and the reasons.
`flat_types_encode_spec.py` writes the encoder files of every row with `encode-spec`, also for the types with hand decoder files.
To use a tool, add the companion to the `companions` column of the row, and add the data of the type to the tool.
A tool stops with a message that names the type when the type has no entry in its data.

| Companion | Tool | Row | The data of the type in the tool |
| --- | --- | --- | --- |
| `spec` | `gen/flat-types/flat_types_spec.py` (`Spec.lean`, step 4) | One row of the type | `SPEC_TYPES` and `descnames`: the fields and their `Desc` names. `DESC_FROM_CONSENSUS_SPECS` and `DESC_FROM_PRYSM_PROTO`: the source of the `Desc`. The decoder and witness tools read `SPEC_TYPES` too |
| `decode-spec` | `gen/flat-types/flat_types_decode_spec.py` | The `decoder --whole-accept` row | None |
| `reject-witness` | `gen/flat-types/flat_types_witness.py` (`WitnessGeneratedDecodeRejectSize.lean`) | The `decoder --whole-accept` row | None |
| `accept-witness` | `gen/flat-types/flat_types_witness.py` (`WitnessGeneratedDecodeAccept.lean`) | The `decoder --whole-accept` row | `FRAME_FORM`, and the tables `gsize`, `callees`, `Fr` and `lsave` of `accbytes` for its forms |
| `encode-spec` | `gen/flat-types/flat_types_encode_spec.py` | The `encoder --fast-path` row | `ENCODE_SPEC_TYPES`: the names of the specification and the field accessors |
| `negative-cases` | `gen/flat-types/flat_types_negative_cases.py` | The decoder row for the decoder cases, the encoder row for the encoder cases | None |
| `hand-list` | `gen/flat-types/flat_types_hand_list.py` | One row of the type | None |

A type whose decoder the generator refuses gives `spec` and `hand-list` in its encoder row, as BuilderPreferences does.

From `fv/kraken`:

```sh
python3 -I -B gen/flat-types/flat_types_spec.py lean
python3 -I -B gen/flat-types/flat_types_decode_spec.py lean
python3 -I -B gen/flat-types/flat_types_witness.py .
python3 -I -B gen/flat-types/flat_types_encode_spec.py lean lean
python3 -I -B gen/flat-types/flat_types_negative_cases.py lean gen/checks/negative-cases
```

Expected: exit 0 for each tool.
`flat_types_hand_list.py` needs the declaration dump of the axioms gate (step 7).

`flat_types_witness.py` chooses the accept witness form by the type name, in its table `FRAME_FORM`.
The decoder code of the type decides the form: its frame size (`sub $…,%rsp` of the `.S` file) and its callees.

- Frame `0x38` (`accept_witness_frame_0x38`): one Slot callee and then inline uint64 fields, no byte field.
  BeaconBlocksByRangeRequest has this form.
- Frame `0x20` (`accbytes`, form `no_callee_frame_0x20`): byte fields and uint64 fields, no callee.
  DepositRequest has this form.
- The frame with slices and callees (`accbytes`, form `slices_and_callees`): byte fields and callees.
  The table `Fr` gives the frame size.
  ValidatorIdentity has this form.

Read the `.S` file of the new type and choose the form.
Add the type to `FRAME_FORM` and to the tables of the form.
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
   Each type has one hand list `gen/axioms-lists/<type>.lean`.
   `<type>` is the Go type name in lower case, with `-` between the words.
   An example is `gen/axioms-lists/historical-batch.lean`.
   A shared library has one hand list with its name, for example `gen/axioms-lists/codec.lean`.
   Put into the list of the type one `#print axioms <name>` line for each main theorem and witness.
   Also put the import of each module that declares one of these names.
   For a type with the companion `hand-list`, `gen/flat-types/flat_types_hand_list.py` adds the lines to the list of the type:
   `python3 -I gen/flat-types/flat_types_hand_list.py <dump.tsv> gen/axioms-lists <module list>`.
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
   It covers every accept row of `gen/generator/types.tsv` and the tools of `gen/flat-types/`:

   ```sh
   python3 -I -B fv/kraken/gen/checks/regenerate_and_compare.py <scratch>/regen-work > <scratch>/regen.txt
   ```

   Expected: every line starts with `EQ`.
5. The negative cases.
   Add one control and at least one mutant for each main theorem.
   Each case file of `gen/checks/negative-cases/` holds the cases of one type, or of one shared library.
   The hand cases of a type go into `negative-cases-<type>.json`, with the type name as in item 2.
   An example is `negative-cases-historical-batch.json`.
   For a type with the companion `negative-cases`, `flat_types_negative_cases.py` writes `negative-cases-<type>-generated.json`.
   An example is `negative-cases-validator-identity-generated.json`.
   Do not put a hand case into a file that ends with `-generated.json`.
   A type can have both files, for example `negative-cases-deposit-request.json` and `negative-cases-deposit-request-generated.json`.
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
   The theorems must have the names of `lean/README.md` section 8, the candidates of `DEC_CANDIDATES`, `ENC_FORMS`, `SIZE_FORM` and `MARSHAL_FORM`.
   An encoder theorem outside the fast path needs an entry in `ENC_EXTRA`.
   The entry gives a premise text for each theorem and a text of what is not proved.
   Without that entry, a theorem with a name of `ENC_UNCLASSIFIED` shows in the row as not classified.
   `GENERATOR_REFUSED` is a hand table of the reason why the generators refuse a flat type.
   Each reason is a short form of the last line of `<T>.whole-accept.stderr` or `<T>.fast-path.stderr` of step 5.
   The `run` mode checks that the keys of the table are the refuse rows of `gen/generator/types.tsv` outside `CORE_FLAT_TYPES` and `NESTED`.
   No program compares the text of a reason with a generator run.
   Change the entry of the type when the generator result of the type changes.
   `CORE_FLAT_TYPES` is the set of types of the accept rows of `gen/generator/types.tsv` in the modes `decoder --whole-accept` and `encoder --fast-path`.
   It does not hold a type with the companion `hand-list`.
   The tool reads it from the table.
   Expected: `gen/tools/proof_inventory.py run` exits 0, and its output `<scratch>/proof-inventory.md` has a row for the type.
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
