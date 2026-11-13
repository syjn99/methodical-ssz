# rename.py in reference mode: usage notes and pitfalls

These notes add to `README.md` section 3 (reference mode).
They give the commands, the map files, the warnings and the pitfalls that earlier steps found.
Use `rename.py` unchanged.
Run `python3 -I -B fv/kraken/gen/restructure/rename.py --selftest` after any change to the tool.

## 1. Commands

Run these commands from the repository root.

```sh
# Trial on a copy first. The tool writes applied-lines.tsv into the map directory that it gets.
sh fv/kraken/gen/restructure/tools/trial.sh fv/kraken/gen/restructure/maps/<step> <scratch dir>
# The real run on the working tree.
python3 -I -B fv/kraken/gen/restructure/rename.py forward fv/kraken/gen/restructure/maps/<step>
# The inverse mode on a copy. On a copy of the new tree, it must give the old tree.
python3 -I -B fv/kraken/gen/restructure/rename.py inverse fv/kraken/gen/restructure/maps/<step> --root <copy>
```

Hand-edited files stop the inverse mode, because their recorded lines changed.
For that reason, `tools/inverse_check.sh` runs the inverse on a copy of a fresh tool run.
It also shows that the working tree differs from that copy only in the hand-edited files.

The tool runs in about 15 s.
It prints `forward: N files moved, N files rewritten, N line records, N warnings`.
Read every `warning:` line (stderr).
A map with at least one `type` row runs in reference mode (below).
The shared-layer map has no `type` row and keeps the old behaviour.

Maps compose in order: `shared-layer`, `checkpoint-and-epoch`, `attestation-data`, `sync-and-indexed-attestation`,
`historical-batch-and-deposit`, `data-columns-by-root-identifier`,
`flat-types`, `clean-up`, `shared-names`, `link-set`, `review-names`, `data-names`, then the next step.
To undo, run the inverse of the last map first.
The forward run of a step needs nothing from the earlier maps.
The inverse of the map of a step alone must give the tree from which the step started.

Do the hand edits after the forward run, as a separate script.
Examples of hand edits: the lakefile, generator emit strings, runner logic, README text.
Reason: the forward check stops if a new name already occurs in the old text.
A hand edit before the run puts new names into the old text.
Let each hand edit assert that its old text occurs exactly once.
Then a changed base stops the script.

## 2. Map directory

The files are `files.tsv`, `names.tsv`, `protect.txt`, and optional `manual-edits.tsv` and `declared.txt`.
Copy `protect.txt` from `maps/checkpoint-and-epoch/`.
Columns are separated by tabs.
Every `names.tsv` row has 5 columns (`-` for an unused column).

### files.tsv

The columns are `old path<TAB>new path<TAB>meaning`, relative to the repository root.
Give one row for each moved file, also for the `.S` files of a library directory.
A `.lean` row under `fv/kraken/lean/` is also the module rename.

### names.tsv rows

| kind | column 2 | column 3 | column 4 | column 5 |
| --- | --- | --- | --- | --- |
| `type` | type namespace, for example `Prysm.AttestationData` | `-` | `-` | `-` |
| `namespace` | old namespace | new namespace | scope (see below) | `whole` or `part` |
| `open` | old namespace | new namespace | type namespace of the file, `-` (file outside every type) or `*` (every file) | `-` |
| `declaration` | old full name | new full name | library (`Prysm`) | NEW module of the declaration |

- `type`: give one row for each type that the map moves.
  Outside the namespace of its type, the tool writes a reference with the full name.
  The tool never opens the namespace of another type.
- `namespace` scope: a NEW module prefix (`Prysm.Slot`, `Prysm.Checkpoint`, or one exact module).
  Or `MODULE#N`: only the N-th top-level `namespace` block of that new module (N counts from 1).
  The most specific row wins: a `#N` row, then the longest module prefix, then the longest old namespace.
  Example for one module with a Slot block and a CommitteeIndex block (both `namespace E2eAd` in the old file):
  ```
  namespace	E2eAd	Prysm.Slot	Prysm.Slot.DecodeAccept#1	part
  namespace	E2eAd	Prysm.CommitteeIndex	Prysm.Slot.DecodeAccept#2	part
  ```
  The tool maps nested namespace lines too (the full old namespace is the stack of blocks).
  `whole` also makes the row a prefix rule for qualified names in non-Lean text.
  Use `part` when the old namespace splits, or when two rows have the same old namespace.
- `open`: an `open <old>` line in a file of that scope becomes `open <new>`.
  Without a matching row, the tool drops the item.
  Exception: the item stays when the imports of the file still declare the old namespace.
  An example is a split namespace such as `E2e`.
  The tool deletes a line whose items are all dropped.
- `declaration`: list EVERY declaration of the moved modules, also the generated ones (`.eq_1`, `.mk`, fields, `match_1`).
  Take them from a Lean declaration dump of the old tree (`tools/dump_all.sh`).
  A name that is not listed does not count as declared.
  A missing field of a `structure` or a missing generated lemma breaks the resolution.
  Internal names (`_private...`, `_aux_...`) are not necessary, unless text uses them.
  The fifth column (new module) selects the row when two modules declare the same old full name.
  An example is two libraries that are never imported together.
  The tool takes the row whose module is in the import closure of the referencing file.
  A new name can be outside the new namespace block of its declaring line.
  Then the tool writes the declaring line root-qualified (`def _root_.Prysm.Epoch.Code.unmarshalSSZ ...` inside `namespace Prysm.Checkpoint.Code`).
  No extra row is necessary: give the true new full name.

### declared.txt (recommended)

Write one name per line.
List the declarations and namespaces of the old tree that the map does not move.
List only names whose last component is a component of a moved old or new name.
The tool resolves short names against them.
Then a short reference to a name of another library is not taken for a moved name.
Also, a new short form is not captured.
`tools/build_maps_example.py` writes this file from a dump `module<TAB>name<TAB>kind<TAB>internal` of all constants.
The dump program is `tools/dump_all.lean`.
Run it through `tools/dump_all.sh`.

### manual-edits.tsv

The columns are `new path<TAB>line<TAB>text after the tool<TAB>final text`.
Use it only for what no rule can see.
Examples:

- A path built from components in Python: `L / "E2e" / "Include.lean"`.
- A string literal in a Lean file, for example the path of `include_x64_rt "E2eAd/BumpNew72.S"`.
- A JSON field that holds a short name that another library also declares.
- A comment that names a deleted file or a name of an earlier map.

Find these lines with a trial run without manual edits (`tools/trial.sh --no-manual`).
Then write the rows from the trial tree, and run the trial again with the rows.

## 3. What the tool does in reference mode

- Lean files: the tool tracks the scope of each line.
  It reads namespace blocks, `open`, `open ... in` for the next command, `open X hiding a`, and the namespace that a dotted declaration name opens.
  It resolves each identifier as Lean does (the innermost namespace first, then the root and the opens).
  It rewrites comments too.
  It does not rewrite string literals.
- A reference to a moved declaration becomes the full new name in two cases.
  The first case: the old text was fully qualified.
  The second case: the line is outside the declaring type.
  Else it becomes the shortest form that resolves to exactly that declaration.
  That form can drop a prefix of the current namespace or an opened namespace.
  It never drops the namespace of a dotted declaration name.
  Exception: a file outside every type can get an `open` from an `open` row with scope `-` (or `*`).
  A reference in that file can be shortened through that `open` too.
  Reason: `generator.py` needs a bare `--const` name and refuses a qualified one (`Prysm.Checkpoint.Code.marshalSSZTo`).
  So the generated files keep `open Prysm.<GoTypeName>.Code` and the bare `unmarshalSSZ`.
- Comments: the tool does not rewrite a short token whose last name component does not change.
  Such a token is often an English word: `word`, `block`, `host`.
  A comment above the `open` lines is resolved in the scope of the first namespace block.
- A declaring line gets the new name relative to the new namespace block (`theorem Decode.accept`).
- Non-Lean text: the tool rewrites paths first.
  Then full old names (declarations, modules, `whole` namespaces) become full new names.
  An old last name component becomes the full new name if it meets three conditions.
  It is unique among the moved declarations, it changes, and it is not the last component of a `declared.txt` name.
- JSON case files are a list, or `{"cases": [...]}`, of objects with `module` and `theorem`.
  The tool rewrites their fields in the scope of that theorem in that module.
  `theorem` becomes the FULL new name, `code_def` the form that the module writes, and `code_ns` the new namespace (open rows).
  The fields `old`, `new` and `diff` are rewritten like Lean text.
- Inverse: the tool records in `applied-lines.tsv` every line that the rule-based inverse does not restore.
  The rule-based inverse covers full names, modules and paths.
  The forward mode runs the inverse in memory, and stops if it does not give the old text.

## 4. Warnings

- `unchanged token X now resolves to [...] (capture?)`: the tool did not rewrite a token, and it resolves to a new name now.
  Usually it is a local variable.
  That is harmless, because locals shadow globals.
  A real capture is a general lemma name in the body of a dotted declaration.
  Example: `SszValue.accepted_is_enc` had a proof that calls the general `accepted_is_enc`, and the new name captured it.
  Fix: choose another new name.
- `X resolves to [...]; left unchanged`: the reference is ambiguous in the old scope.
  Check it by hand.
- `X needs _root_`: no short or full form resolves uniquely.
  Check it by hand.
- Check every warning by hand, and give its reason in the commit message.
  Example: the Checkpoint and Epoch step had 18 capture warnings.
  All of them were local variables (`t30`, `scr`) in `DecodeThenEncode.lean` and `DecodeThenEncodeReceiver.lean`.
  The AttestationData step and the SyncAggregate, SyncCommittee and IndexedAttestation step had 0 warnings.

## 5. Pitfalls

- Name order in `simp`.
  `simp` with commutativity lemmas (`Std.ExtHashMap.sep_comm`, `sep_comm_l`) orders the fragments of a separating conjunction.
  The order comes from the names of the constants in them (Lean `Name.cmp`, root component first).
  A rename that moves a constant to a root that sorts differently can make such a proof fail.
  Example: `E2e.Data.e2eErrBytesLength_addr` to `Prysm.ElfData...` broke `Encode.reject_length_grow_first_site`.
  The root "Prysm" sorts after HAdd, HSub, Host, Int, List and Eq.
  The root "E2e" sorts before them.
  For that reason the data namespace is `ElfData.<PlainSetName>` (the root `ElfData` sorts like `E2e` against those names).
  The module path is `Prysm/ElfData/<PlainSetName>.lean`.
  Keep witness names and code names in the namespace of the type.
  Only a build shows such a failure.
  It is not a name error.
- `witness_split` (`Machine/WitnessHost.lean`) refers to the identifier `block` of the current namespace.
  A witness file that uses the host of another witness file must stay in the namespace of that file.
  Example: `Prysm/Checkpoint/WitnessDecodeAcceptSpec.lean` stays in `Prysm.Checkpoint.Witness.DecodeAccept` (theorem `runs_spec`).
- A generator template can write `open ... E2e ...` for all types.
  After a move, the namespace `E2e` can be gone from the imports of one generated file.
  The tool removes it from that file, and then the generator does not reproduce that file.
  `whole_accept.py` (`G5_OPENS`) and `flat_types_witness.py` were changed, because every output lost `E2e`.
  `encode_spec_emitter.py` was changed in the flat-types step.
- A generator writes its `--prefix` into a comment (the `FAST-PATH-JSON` line), and an evidence tool writes old names into
  comments. The tool does not rewrite such text: give `manual-edits.tsv` rows, made by rule from a trial tree.
- The tool rewrites a declaring line only in a moved module. A map that renames a declaration of a module that
  does not move gives `manual-edits.tsv` rows for its declaring lines (the clean-up map does so).
- List generated names (`.mk`, fields, `.eq_1`) as declaration rows.
  Else a body inside `theorem SszValue.x` sees `SszValue.g` as declared for every local `g`.
- Do not make declaration rows from a regular-expression list of the source files.
  Lean derives names that such a list does not see (`.eq_1`, `match_1`, names that a macro or an `elab` makes).
  Take the rows from a declaration dump of the base tree.
- A new short name can be equal to a general lemma name that the bodies of its own namespace use.
  Examples: `serialize`, `encode`, `accepted_is_enc` from `Spec` or EthLib.
  Then the new name captures them.
  The lines `open Spec hiding encode` in some files show such names.
- A new name can be equal to a local variable name or a tactic name, for example `p0` or `split`.
  Then the tool prints capture warnings, and the proof can change meaning.
  Choose a plain word: `input_pointer_mask` for `p0`, `bytes_split` for `split`.
- An `open` row with scope `*` applies to every file.
  If two `Code` namespaces would be opened in one file, `Code.unmarshalSSZ` becomes ambiguous.
  Give `open` rows of a `Code` namespace one scope per type (the type namespace, or `-`), not `*`.
- An `open` line comes before the `namespace` line.
  The tool takes the type of a file from its new module path (`Prysm/<Type>/...`).
  So name the modules under the type directory.
- Generators: the tool rewrites their strings like any text.
  Check each generated file with a fresh generator run (`tools/regen.py`).
  The tool does not see a template such as `f"def {abbr}GoFields"`.
  It makes a literal such as `cpGoFields` a FULL name, which is wrong inside a namespace block.
  Fix such a line by hand after the run.
- String literals: the tool does not rewrite them.
  The `.S` paths of `include_x64_rt "..."` need `manual-edits.tsv` rows.
  Path components in Python (`L / "E2eList" / "Include.lean"` in the `check_include` scripts) also need rows.
- JSON case fields `old` and `new` are rewritten like Lean text.
  The result can be a name form that differs from the text of the moved Lean file.
  Example: `accept_function_spec Heap S` in a case, but `Decode.accept_function_spec Heap S` in the module.
  Run `negative.py --check-cases` (cwd `fv/kraken`) after the run, and fix the cases with `manual-edits.tsv` rows.
- Old abbreviations can be equal across libraries.
  Example: the old library E2eScal (SyncAggregatorSelectionData) declared `PSa`, `psaEnc`, `prysmSaDesc` and `sa_*` lemmas.
  These are also old names of SyncAggregate.
  The tool leaves such short names in JSON fields unchanged.
  Count such names before and after the run in the files of the other library.
  The counts must be equal.
- `negative.py` and `list_negative.py` find a theorem by its full name, or by the written name if it is unique.
  `negative.py --check-cases <files>` checks every case without Lean.
  Run it before and after (cwd `fv/kraken`).
  Without `code_ns`, a case in a module under `Prysm/<Type>/` uses `Prysm.<Type>.Code` (`negative.code_ns_of`).
  A full name in `code_def` uses `_root_`.
- Modules that use the Lean module system (`module`, `public import`) keep it after a move.
- `fv/kraken/lean/Prysm/SyncCommitteeMessage/DecodeAcceptDependencyCheck.lean` walks the project namespaces
  `Prysm`, `Codec`, `ElfData`, `Machine` and `Runtime`. A step that adds a root namespace adds it there.
- `desc_to_lean.py` emits the namespace from the Go type name as written.
  For the Go type `Deposit_Data` the namespace is `Prysm.Deposit_Data`.
- The lakefile: a moved `.S` file of a library directory needs a new `input_dir` for its new directory (filter `.S`).
  Put that `input_dir` into the `needs` of `Prysm`.
  Remove the old `input_dir` from every `needs` list.
- The tactic `bhaddr` and the command `#g4_dep_check` of `maps/flat-types` are now `beacon_block_header_addr` and
  `#check_window_step_dependencies`, so an inverse run of that map needs these two names put back first.
- The tactics `eaddr`, `adaddr`, `e1addr`, `daddr`, `dcaddr`, `saddr`, `g4_regclose`, `bytesdec_g4c`, `bytesdec_g4z`,
  `bytesdec_g4c20`, `bytesdec_g4z20`, `smarg_close` and `u64rr_case` that the maps name are now `checkpoint_addr`,
  `attestation_data_addr`, `eth1_data_addr`, `data_columns_by_root_identifier_encode_addr`,
  `data_columns_by_root_identifier_decode_addr`, `segment_addr`, `register_equation_close`, `bytes_decode_window_case`,
  `bytes_decode_window_offset_zero_case`, `bytes_decode_window20_case`, `bytes_decode_window20_offset_zero_case`,
  `setup_argument_close` and `uint64_register_case`. The four `bytesdec_g4*` tactics had an intermediate name
  `bytesdec_window*_case`; the step of `maps/plain-lean-names/` renamed every `bytesdec_*` tactic to `bytes_decode_*`.
  An inverse run of an earlier map needs the old names put back first.
- The link-set step renamed the tactics `iaaddr`, `laddr` and `lvbytesdec_z` to `indexed_attestation_addr`,
  `address_with_products` and `bytes_decode_zero`. The data reader commands `e2e_data_include`, `ad_data_include`,
  `lv_data_include`, `lvt3_data_include` and `dcd_data_include` became the one command `prysm_data_include`.
  An inverse run of an earlier map needs the old names put back first.
- The records of `maps/flat-types/` and `maps/shared-names/` name `callDecSegKindG4_of`, `callDecSegKind_eq_G4`,
  `EncodeFastPathExamples`, `DecodeAcceptExamples` and `Uint64DecoderKindAnchors`, which `maps/review-names/` renamed.
  An inverse run of those maps needs `maps/review-names/` undone first.
  The tactic `bytesdec_z` became `bytesdec_offset_zero_case` and is now `bytes_decode_offset_zero_case`.

## 6. Self-test

`python3 -I -B fv/kraken/gen/restructure/rename.py --selftest` uses no Lean and a temporary tree.
It covers two modules with the same old full name, and two namespace blocks of two types in one module.
It also covers a `_root_` declaring line, a deleted `open`, and an exact inverse.
Run it after any change to the tool.
