# Type move: naming rules and decisions

This file gives the rules for each step that moves an old library to `fv/kraken/lean/Prysm/<GoTypeName>/`.
The rules are binding for every step.
If a case does not fit a rule, do not guess.
Choose the most literal option, and record the case in the commit message of the step.

## 1. Goal

The Lean tree moves from libraries named after old experiments to one directory per Prysm type:

    fv/kraken/lean/Prysm/<GoTypeName>/<Role>.lean        Lake library `Prysm`, namespace `Prysm.<GoTypeName>`

`<GoTypeName>` is the Go type name as the Go source writes it.
Examples: Checkpoint, Epoch, AttestationData, Slot, CommitteeIndex, SyncAggregate, SyncCommittee, IndexedAttestation.
More examples: HistoricalBatch, Deposit, DataColumnsByRootIdentifier, BeaconBlockHeader.
Never use an abbreviation.

The fully qualified Lean name of a main theorem is the name of the work unit.
Its form is `Prysm.<GoTypeName>.<Function>.<obligation>`, for example `Prysm.Checkpoint.Decode.reject_size`.

## 2. A step moves and renames only

- One old module becomes exactly one new module.
- Do not merge, split or delete modules, also not duplicates.
  The last step merges files and removes duplicate proofs.
- Do not change a statement, a definition body or a proof.
  The exceptions are identifiers, and the `import`, `namespace`, `end` and `open` lines.
- Every change comes from the maps and from `rename.py`.
  Then the inverse mode of the tool gives the old tree back.
- Read `README.md` and `TOOL-NOTES.md` in this directory before you make a map.
  The map `maps/attestation-data/` and `tools/build_maps_example.py` are a worked example.

## 3. Module names (the `<Role>` part)

Read the header and the main declarations of each module.
Then name the module by what it holds.
Use these words:

| Content of the module | Role name |
| --- | --- |
| Program constants read from the converted `.S` files | `Code` |
| Go struct layout (offsets, sizes) | `Layout` |
| Validity of the Go value of the receiver | `GoValue` (and `GoValueWitness` for its witness) |
| The EthLib description of the type and the bridge lemmas | `Spec` |
| The description generated for the description checker | `SpecChecker` |
| Equality of the hand description and the checker description | `SpecEquivalence` |
| Decoder, accept path | `DecodeAccept` |
| Decoder, one reject path | `DecodeRejectSize`, `DecodeRejectOffset`, `DecodeRejectAlignment`, `DecodeRejectOverflow`, `DecodeRejectDelegate` |
| Decoder, a loop or a call that the accept path uses | `DecodeLoop`, `DecodeCall`, with a plain qualifier when there are several |
| Decoder, connection to EthLib | `DecodeSpec` |
| Encoder, path with no slice growth | `EncodeFastPath` |
| Encoder, growth at the first append site only | `EncodeGrowFirstSite` |
| Encoder, growth at any one site / at any site | `EncodeGrowOneSite` / `EncodeGrowAnySite` |
| Encoder, a reject | `EncodeRejectLength`, `EncodeRejectTooBig`, and so on (name the cause) |
| Encoder, connection to EthLib | `EncodeSpec` |
| Encoder, a part of a long proof (head, tail, cover, a field) | `Encode` + plain word for the part (`EncodeHead`, `EncodeTail`, `EncodeCover`) |
| `SizeSSZ` | `Size` |
| Decode then encode, round trip, composition | `DecodeThenEncode` |
| A witness of theorem X (a concrete state that satisfies the premises) | `Witness` + the role of X (`WitnessDecodeAccept`, `WitnessEncodeFastPath`) |
| Statements only (definitions `..._stmt : Prop`) | `Statements`, or `Statements` + plain qualifier |
| ELF data definitions of a link set, and the command that reads them | under `Prysm/ElfData/`: `<PlainSetName>` and `<PlainSetName>Reader` |

If no role of the table fits, use plain words that say what the module holds.
Examples from earlier steps: `DecodeFieldSegments`, `DecodeLoopLemmas`, `SpecDefinitions`, `SpecDescription`, `AddressTactic`.
Say so in the meaning column of `files.tsv`.

A module that mixes several roles gets the name of its main role.
Say so in the meaning column of `files.tsv`.
Example: a module with a size reject and an offset reject is `DecodeRejectSize`.

Several types can share a module that is not about one type, for example a lemma file.
Such a module goes to the type that owns most of it.
Mark it "shared, needs a split" in the meaning column of `files.tsv`.

## 4. Namespace and declaration names

All declarations of the modules of one type go to the namespace `Prysm.<GoTypeName>`.
Use dotted declaration names for the function part.
For example, inside `namespace Prysm.Checkpoint`, write `theorem Decode.reject_size ...`.

Main theorems and their statements map to exactly these forms:

| Old pattern (`<t>` = old type abbreviation) | New name inside `Prysm.<GoTypeName>` |
| --- | --- |
| `<t>_e2e_accept_main` | `Decode.accept` |
| `<t>_e2e_reject_size_main` | `Decode.reject_size` |
| `<t>_e2e_reject_offset_main` | `Decode.reject_offset` |
| `<t>_e2e_reject_misaligned...` | `Decode.reject_alignment` (keep a suffix that states an added premise, in words: `_error_word_nonzero`) |
| `<t>_e2e_reject_toobig...` (decoder) | `Decode.reject_overflow` (same rule for an added premise) |
| `<t>_e2e_accept_spec_k`, `<t>_e2e_accept_spec` | `Decode.accept_spec` |
| `<t>_e2e_reject_<cause>_spec` | `Decode.reject_<cause>_spec` |
| `<t>_e2e_reject_complete` | `Decode.reject_complete` |
| `<t>_e2e_marshal_main`, `..._marshal_fast_main` | `Encode.fast_path` |
| `<t>_e2e_marshal_grow_main` | `Encode.grow_first_site` |
| `<t>_e2e_marshal_once_main` | `Encode.grow_one_site` |
| `<t>_e2e_marshal_grow_any_main`, `..._marshal_any_...` | `Encode.grow_any_site` |
| `<t>_e2e_marshal_reject_main`, `..._reject_bytes_main` | `Encode.reject_length` |
| `<t>_e2e_reject_toobig_main` (encoder) | `Encode.reject_too_big` |
| `<t>_e2e_marshal_spec_k`, `..._marshal_spec` | `Encode.fast_path_spec` (and `Encode.<path>_spec` for the others) |
| `<t>_e2e_size_main`, `<t>_e2e_size_spec` | `Size.result`, `Size.result_spec` |
| `<t>_e2e_unmarshal_then_marshal...`, `..._spec_roundtrip` | `DecodeThenEncode.round_trip` (keep a suffix that states an added premise in words) |
| `<name>_stmt` (a `def ... : Prop`) | the name of its theorem + `_statement` |
| Program constants `<T>Unmarshal`, `<T>Marshal`, `<T>Size`, `<T>MarshalSSZ` | `Code.unmarshalSSZ`, `Code.marshalSSZTo`, `Code.sizeSSZ`, `Code.marshalSSZ` |
| `prysm<T>Desc` | `desc` |
| `<t>CheckerDesc` | `checkerDesc` |
| `<t>GoFields`, `<t>GoSize` | `goFields`, `goSize` |

All other declarations:

- Remove the type abbreviation (prefix `<t>_`, infix `<T>`) and the marker `e2e`.
- Keep the remaining words.
- If the rest alone is unclear, put the function word first (`cp_marshal_head_step` becomes `Encode.head_step`).
- Two declarations of one type must not get the same name.
  Add the plain word that separates them.
- Do not rename a declaration whose name a macro or a command derives from a file name.
  An example is the data definitions that a data-include command makes from `.data` file ids.
  Change only their namespace.
- Do not rename `.S` files or `.data` files.
- A type step does not move link directories.
  The link-set step after the type steps merged them into `prysm/go1.26.10/link-set`.

References: a renamed declaration has a short name that other types also use (`Decode.accept`).
The tool must leave no ambiguous reference.
Outside the namespace of the declaring type, the tool writes the full name `Prysm.<GoTypeName>.<...>`.
The tool does not add an `open Prysm.<GoTypeName>` line to files of other types.

## 5. Decisions

These decisions are binding for every step.

1. The structure of the abstract value of a type (old `P<T>`, for example `PCp`, `PAd`) is `SszValue`.
   Its encoder function (old `p<t>Enc`) is `SszValue.encode`.
   Full name: `Prysm.Checkpoint.SszValue`.
   Lemma names derived from the encoder use the word `encode` (`SszValue.encode_size`,
   `Prysm.DataColumnsByRootIdentifier.encode_roundtrip`).
2. A callee-style function specification of a method (old names such as `EpUAccC`) is
   `Decode.accept_function_spec` or `Encode.fast_path_function_spec`.
   The lemma that it holds gets the suffix `_holds`.
3. Witness modules keep one namespace per file.
   The namespace is `Prysm.<GoTypeName>.Witness.<Role>`.
   `<Role>` is in CamelCase: the role of the theorem that the witness satisfies, for example `Witness.DecodeAccept`.
   The main witness theorem is `runs`, with a plain qualifier for the case (`runs_empty`, `runs_one_element`, `runs_maximum`).
   Full name: `Prysm.Checkpoint.Witness.DecodeAccept.runs`.
   Helper declarations of a witness file have plain names in that namespace (`program`, `host`, `zeros`, `word_bytes`,
   `label_err_size`; the placement facts `placed_at_<n>`, `labels_fresh_at_<n>`, `no_label_before_<n>`).
4. The link sets of the Prysm ELF are merged into one link set, `prysm/go1.26.10/link-set`, with one data reader.
   The data module is `Prysm/ElfData/PrysmTarget.lean` (namespace `ElfData.PrysmTarget`).
   The reader is `Prysm/ElfData/PrysmTargetReader.lean` with the command `prysm_data_include`.
   The data names are the ids of the `.data` files. The step data-names gave each ELF item a plain id, for example
   `sszErrSize_addr` (`link/data.py` `item_id`); `prysm/go1.26.10/link-set/data-ids-old-new.tsv` gives the earlier ids.
5. A module that holds two types stays one module (for example the Slot and CommitteeIndex decoders in one file).
   Each namespace block of that module goes to the namespace of its own type.
   The module goes under the type of the first block.
   Mark it "shared, needs a split".
6. The description term generators `fv/kraken/gen/checks/desc_to_lean.py` and `list_desc_to_lean.py` emit `namespace Prysm.<GoTypeName>`.
   The name comes from the Go type name.
   Do not edit the generators in a type step.
   Put the generated files of your types in the map.
   After the tool run, a fresh generator run must equal the moved file.
7. One namespace block can hold declarations of two types.
   Each declaration still gets the name of its own type.
   The tool writes the declaring occurrence with a root-qualified name.
   Example: `def _root_.Prysm.SyncCommittee.Code.unmarshalSSZ ...` inside a block of another type.
   The tool writes every reference with the full name.
   Do not invent a prefixed name in the namespace of the wrong type.
8. Some runtime models read ELF data of a link set or name one Prysm type.
   An example is a bump allocator model that dispatches on type descriptors.
   Such a model does not go to the `Runtime` library, because `Runtime` must not import `Prysm`.
   Put it under `Prysm/RuntimeModel/` (namespace `Prysm.RuntimeModel`) with a plain name.
   Put its `.S` model files next to it.
9. The removal or change of the `lean_lib` and `input_dir` entries of the moved libraries is part of the approved restructuring.
   It needs no further approval.
   Other lakefile changes need approval.
10. The ELF data namespace has the root `ElfData`, not `Prysm`: `ElfData.<PlainSetName>`.
    The module path is `Prysm/ElfData/<PlainSetName>.lean`.
    The reason is the `simp` order pitfall in `TOOL-NOTES.md` section 5.
11. The proofs of a namespace can use a bare name for another declaration.
    A new short name in that namespace must not be equal to such a name.
    Examples: the EthLib name `serialize`, the general lemma `accepted_input_is_encoding` (earlier `accepted_is_enc`),
    the named argument `enc`.
    Also avoid a local variable name or a tactic name.
    Examples: `p0` became `input_pointer_mask`, and `split` became `bytes_split`.

## 6. Everything that stores the names follows

These follow through the tool, or through the generator when a generator writes the file:

- Imports and references in every Lean file, also outside `fv/kraken/lean`.
  This includes the description checker and the hand lists in `fv/kraken/gen/axioms-lists/`.
- Negative-case files (`module`, `theorem`, `code_def`, `code_ns`, paths, `old` / `new` text pairs).
- Scripts that name the moved modules, namespaces or paths.
  Examples: link scripts, `check_include` scripts, generators and their emitted strings.
  A regenerated output must equal the moved file.
- `fv/kraken/lean/lakefile.toml`: the library `Prysm` (`globs = ["Prysm.+"]`).
  Its `needs` must name every `input_dir` that the moved modules read.
  Remove an old library when it has no module left.
- README files and `fv/kraken/FINDINGS.md`.

The axioms gate `fv/kraken/gen/checks/axioms_gate.py` reads the library list from `lakefile.toml`.
It needs no edit.

Do not rewrite these files:

- Link `RESULT` files and `build-ids.txt`.
- `fv/kraken/gen/frozen/*.json`, `fv/kraken/prysm/inventory.json` and `fv/kraken/prysm/proof-inventory.*`.
- The contents of `.S` and `.data` files.

List the stale names that they keep in the commit message.
`protect.txt` of each map names these files, so the tool does not change them.

## 7. Checks

`README.md` in this directory gives the checks before each commit.
In short:

- `lake build` of every library, exit 0.
  No `sorry`, `admit`, new `axiom`, `native_decide` or `bv_decide`.
  No raised `maxHeartbeats` or `maxRecDepth`.
- The inverse check.
  The inverse mode of the tool on a copy of the new tree gives the old tree.
  The only exceptions are files that the step changes for a stated reason.
  Examples: lakefile, generator emit strings, README text, the tool and the maps.
  No file under `fv/kraken/lean` may differ.
- Python checks before and after, with equal results.
- The axioms gate over all libraries, if the full build passed.

## 8. Rules

- Write text in English, in ASD-STE100 style.
- No code names in any new name: no abbreviations of types, steps, phases, experiments or reviews.
  A reader with no history must understand each name.
- Do not use `git add -A`.
  Stage the changed paths by name or by directory.
- Run only one `lake` job at a time.
  Check with `pgrep -lx lake` and `pgrep -lx lean`.
  Never use `pgrep -fl`.
- Do not change Kraken, EthLib, `ssz/`, `sszgen/`, the generator logic, or any theorem statement.
