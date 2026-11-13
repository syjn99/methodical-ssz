# restructure: rename maps and the rename tool

This directory holds the tool, the maps and the helper scripts that move Lean modules under `fv/`.
They also rename namespaces and declarations.
Each step that renames with `rename.py` has one map directory under `maps/`.
Some steps were applied by scripts only (section 4).
The directory is temporary.
Delete it (with `trash`) when the restructuring is done.

Read these files first:

- `SPEC.md`: the naming rules and the decisions, binding for every step.
- `TOOL-NOTES.md`: the use of `rename.py` in reference mode, the map files, the warnings and the pitfalls.
- This file: the tool, the applied maps, the procedure of one step and the checks before each commit.

## 1. The tool

`rename.py` applies one map directory to the tree, or undoes it.
It uses only the Python 3 standard library.

```sh
python3 -I -B fv/kraken/gen/restructure/rename.py forward fv/kraken/gen/restructure/maps/<step>
python3 -I -B fv/kraken/gen/restructure/rename.py inverse fv/kraken/gen/restructure/maps/<step> [--root <copy>]
python3 -I -B fv/kraken/gen/restructure/rename.py --selftest
```

The forward mode does these steps:

1. It checks that no new name or new path of the maps occurs in the old text.
   Else the inverse would not be exact, and the tool stops.
2. It moves the files of `files.tsv`.
3. It rewrites the text files under `fv/`.
   It rewrites `import` lines, qualified names, module names, renamed short names, and the paths of moved files.
4. In Lean files it also rewrites the `namespace`, `end` and `open` lines.
   An `open` of a split namespace becomes an `open` of the new namespaces that the imports of the file declare.
   A file in a split namespace gets an inserted `open` line before its first `namespace` line.
   An `open` can get a `hiding` clause for a name that the file uses.
   That name was not visible through the old `open`.
5. It applies `manual-edits.tsv`.
6. It writes `applied-lines.tsv`: every `namespace`, `end` and `open` line that it changed, inserted or deleted.

A map with at least one `type` row runs in reference mode (section 3).
A map without one keeps the steps above.

The inverse mode reads `applied-lines.tsv` and `manual-edits.tsv` and does the steps in the reverse order.
The tool does not change this directory or the files that `protect.txt` names.
It moves files with a plain rename.
It does not stage the moves in git.

## 2. A map directory

| File | Content |
| --- | --- |
| `files.tsv` | Old path, new path and the meaning of the file. A `.lean` file under `fv/kraken/lean/` also gives the module rename |
| `names.tsv` | Namespace rows (old namespace, new namespace, library of the module) and declaration rows (old name, new name, library, new module) |
| `manual-edits.tsv` | New path, line, the text after the automatic rewrite, the final text. Only for a change that the rules cannot make |
| `protect.txt` | Glob patterns of files whose text the tool does not change (records of runs, pinned files, the Lake configuration) |
| `applied-lines.tsv` | Written by the forward mode. The inverse mode needs it |
| `removed/` | Files that the step removes. They stay here so that the inverse mode can restore them |

A namespace row applies to the modules of its library.
The longest old prefix wins.
A declaration row comes from a Lean declaration dump of the old tree.

A reference-mode map adds the files and rows of the next table.
Every `names.tsv` row has five columns.
A `-` marks an unused column.

| Row or file | Columns or content |
| --- | --- |
| `type` row | The namespace of one type, for example `Prysm.Checkpoint` |
| `namespace` row | Old namespace, new namespace, scope, `whole` or `part`. The scope is a prefix of the new module name, or `MODULE#N`: only the N-th top-level `namespace` block of that new module |
| `open` row | Old namespace, new namespace, type namespace of the file (`-` for a file outside every type, `*` for every file) |
| `declaration` row | Old full name, new full name, library, new module. List every declaration of the moved modules, the generated ones included (`.eq_1`, `.mk`, fields) |
| `declared.txt` | Optional. Old-tree names that the step does not move and whose last component is a component of a moved name |

The most specific namespace row wins: a `MODULE#N` row, then the longest module prefix, then the longest old namespace.
Two declaration rows can have the same old name if their new modules differ.
A reference takes the row whose module is in the import closure of the file.

## 3. Reference mode

The renames are keyed on the full old name and the declaring module, never on the last name component alone.

1. The forward mode checks that no new full name, new module name or new path occurs in the old text.
2. In a Lean file it tracks the scope of each line.
   It reads the namespace blocks and the `open` lines (also `open ... in` and `hiding`).
   It also reads the namespace that a dotted declaration name opens.
   It resolves each identifier as Lean does: the innermost namespace first, then the root name and the opened namespaces.
3. The reference rule.
   A reference to a moved declaration gets the full new name in two cases.
   The first case: the old text had the full old name.
   The second case: the line is outside the namespace of the declaring type.
   Else the reference gets the shortest form that resolves to exactly that declaration in the new scope.
   The tool can drop a prefix of the current namespace or an opened namespace.
   It does not drop the namespace of a dotted declaration name.
4. A declaring line gets the new name relative to its new namespace block.
   If the new name is not inside that block, the line gets the root-qualified name (`def _root_.Prysm.Epoch.Code.unmarshalSSZ`).
5. An `open` of an old namespace becomes the `open` rows that match the type of the file.
   The type of a file comes from its namespace or from its new module path.
   The tool never opens the namespace of another type.
   The tool removes an item without a row, except an old namespace that the imports of the file still declare.
   The tool deletes a line without items.
6. In other text files the tool rewrites paths first.
   Then it rewrites full old names (declarations, modules, `whole` namespaces).
   An old last name component becomes the full new name if it meets three conditions.
   It is unique among the moved declarations, it changes, and no name of `declared.txt` has it as last component.
7. A JSON file of negative cases holds objects with `module` and `theorem`.
   The tool rewrites their fields in the scope of that theorem.
   `theorem` becomes the full new name, `code_def` the form that the module writes, and `code_ns` the new namespace.
   The fields `old`, `new` and `diff` are rewritten like Lean text.
8. Every line that the rule-based inverse (full names, modules, paths) does not restore goes to `applied-lines.tsv`.
   The forward mode runs the inverse in memory and stops if it does not give the old text.
9. It prints a warning for a token that it did not change and that now resolves to a new name.
   Such a token is a capture or a local variable.
   It also prints a warning for an ambiguous old reference, and for a name that needs `_root_`.

Limits:

- The scope tracker reads lines, not Lean syntax.
- It knows only the names of the maps and of `declared.txt`.
- It does not know local variables.
- A rename can break a proof that depends on the order of names.
  An example is `simp` with commutativity lemmas, which orders terms by constant names.
  Only a build shows it.

Several maps apply one after another on the same tree, in the order of section 4.
Each forward run reads only its own map.
To undo them, run the inverse of the last map first.
The inverse of one map alone gives the tree from which its forward run started.
Do hand edits (the Lake configuration, generator strings, runner logic) after the forward run.
A hand edit before the run puts new names into the old text, and the forward check then stops.

## 4. Applied maps

The maps apply in this order:

- `maps/shared-layer/`: the shared libraries `Machine`, `Runtime`, `Spec` and `Codec`, and the library of the Go 1.26.3
  test target (deleted after the clean-up step).
  They come from `Fk`, `Fv`, `Fv1`, `E2eSeg`, `E2e/WitSplit.lean` and the type-independent modules of `E2eScal`.
- `maps/checkpoint-and-epoch/`: the library `E2e` becomes `Prysm/Checkpoint/`, `Prysm/Epoch/` and `Prysm/ElfData/` (library `Prysm`).
  It is the first map in reference mode.
- `maps/attestation-data/`: the library `E2eAd` becomes `Prysm/AttestationData/`, `Prysm/Slot/` and `Prysm/CommitteeIndex/`.
  Some of its modules go to `Prysm/Checkpoint/` and `Prysm/ElfData/`.
- `maps/sync-and-indexed-attestation/`: the library `E2eList` becomes `Prysm/SyncAggregate/`, `Prysm/SyncCommittee/` and `Prysm/IndexedAttestation/`.
  Some of its modules go to `Prysm/RuntimeModel/` and `Prysm/ElfData/`.
- `maps/historical-batch-and-deposit/`: the libraries `E2eHb`, `E2eDep` and `E2eDepW` become `Prysm/HistoricalBatch/` and `Prysm/Deposit/`.
- `maps/data-columns-by-root-identifier/`: the libraries `E2eEnc` and `E2eDec` become `Prysm/DataColumnsByRootIdentifier/`.
  Some of their modules go to `Prysm/RuntimeModel/` and `Prysm/ElfData/`.

- `maps/flat-types/`: the library `E2eScal` becomes `Prysm/<GoTypeName>/` for 24 flat types; some modules go to the
  directories of earlier types, and the type-independent modules go to `Codec/` and `Codec/Kind/`.
  The step changed the emit strings of the generators and the evidence tools, `kindcheck.py`, `regen.py` and `python_checks.sh`.
- `maps/clean-up/`: renames of the clean-up step. The declarations of the test-target library that other libraries used get the names of
  `Runtime`, `Machine` and `Codec`, and a hand edit moves their text into new modules of those libraries.
- `maps/shared-names/`: names of declarations that other types use. The Slot and CommitteeIndex programs of the
  AttestationData link set get the names of their types, and type-independent lemmas get `Codec` names.
  A cut script then moves their text into the modules of their new names.
- `maps/link-set/`: the data namespaces become `ElfData.PrysmTarget`, and eight address lemmas get names there.
  A hand-edit script merges the 16 link sets of the Prysm ELF into `prysm/go1.26.10/link-set` and the five data readers into one.
- `maps/review-names/`: plain names from the independent review.
  The callee window segment kind `Codec.callDecSegKindG4` (and `_of`, `_eq_G4`) becomes `Codec.callDecSegKindWindow` (`_of`, `_eq_window`).
  The frame `Machine.luFrame` (`_sep`, `_slices`) becomes `Machine.stackFrame144`.
  The modules `EncodeFastPathExamples` and `DecodeAcceptExamples` become `EncodeFastPathExampleIndex` and `DecodeAcceptExampleIndex`.
  The module `Uint64DecoderKindAnchors` becomes `Uint64DecoderKindSameAsHand`.
  A script renames the tactic `bytesdec_z` to `bytesdec_offset_zero_case`, and the kind name in `kindcheck.py` and `generator.py`.
- `maps/data-names/`: plain ids for the ELF data of the Prysm link set.
  The data names `ElfData.PrysmTarget.<id>`, `<id>_addr` and `<id>_addr_eq` take the new ids, and
  `Prysm.Deposit.Code.depDataType_addr` becomes the data include `ElfData.PrysmTarget.typeDeposit_Data_addr`.
  A script renames the data files (`prysm/go1.26.10/link-set/data-ids-old-new.tsv`) and the item tables of the link scripts.
- `maps/plain-lean-names/`: plain names inside the Lean libraries (kind structures and their constructors and fields,
  directive builders, step lemmas, tactics, runtime contracts and models, witness helpers, opaque lemma names).
  This step was applied by a script; the map directory holds only the name table (`names.tsv`) and the moved
  runtime model files (`files.tsv`).

Some steps were applied by scripts, not by maps. The inverse mode of `rename.py` does not undo them.
The commit message of each such step lists its edits:

- the clean-up step after `maps/clean-up/`: a script split the modules that held declarations of two types (each
  declaration kept its full name and its text), and a script deleted the duplicate theorems whose statements were identical
  to kept theorems;
- the retirement of the library of the Go 1.26.3 test target: a script deleted that library with its proofs;
- the cut after `maps/shared-names/`: a script moved declaration texts into the modules of their new names;
- the template names step: a script renamed the tactic `bhaddr`, the command `#g4_dep_check` and the comments that
  generator templates write;
- the step of the short tactic names: a script renamed the tactics listed in `TOOL-NOTES.md` section 5;
- the link-set step after `maps/link-set/`: a script merged the 16 link sets into `prysm/go1.26.10/link-set`, merged the
  five data modules and readers into `Prysm/ElfData/PrysmTarget.lean` and `PrysmTargetReader.lean`, moved the eight
  address lemmas there, and renamed the tactics `iaaddr`, `laddr` and `lvbytesdec_z`.

Issue 10 of `syjn99/methodical-ssz` holds the list of the steps that remain.

## 5. Helper scripts in `tools/`

All scripts take repository-relative arguments and run from the repository root.
Scratch output goes to a directory that you give as an argument.
That directory must not exist.
Delete scratch directories with `trash`.
The scripts need Python 3 (3.9 or later), git, POSIX `sh`, `tar` and `diff`.
On Linux, the `trash` command comes from the package `trash-cli`.

| Script | Purpose | Lean |
| --- | --- | --- |
| `dump_all.lean`, `dump_all.sh` | Declaration dump of every module of every library: `module`, `name`, `kind`, `internal`. Input of a map builder | yes |
| `build_maps_example.py` | Map builder of the step `attestation-data`. An example to copy for a new step | no |
| `trial.sh` | Forward run of a map on a fresh copy of a commit. `--no-manual` leaves out `manual-edits.tsv` | no |
| `inverse_check.sh` | Inverse check of a step: fresh forward run on the base, compare, inverse, compare | no |
| `python_checks.sh` | Python-only checks. Run it before and after a step and compare the two out dirs with `diff -r` | no |
| `negative_case_ranges.py` | Theorem line range of every negative case. `python_checks.sh` runs it | no |
| `regen.py` | Regeneration comparison of the Python generators of Lean files | no |
| `gate_dump_compare.py` | Comparison of two axioms gate dumps across the maps of a step | no |
| `constant_uses.lean` | Use count of the constants of some modules in other modules. For the splits and the detach of the test-target library | yes |

The repository does not keep a declaration dump of the tree.
Write a new one at the start of each step (section 6, item 3).

## 6. Procedure of one step and checks before each commit

Run lake jobs one at a time, under the heavy-job gate of the machine.
Check that no job runs with `pgrep -lx lake` and `pgrep -lx lean`.
Never use `pgrep -fl`.
A timeout or an out-of-memory kill is a result to report, not a pass.

Before the forward run:

1. Start from a clean working tree.
   Write down the base commit (`git rev-parse HEAD`).
2. Build every library of `lakefile.toml` (from `fv/kraken/lean`):
   ```sh
   lake build $(awk '/^\[\[lean_lib\]\]/ { getline; if (sub(/^name = "/, "")) { sub(/"$/, ""); print } }' lakefile.toml)
   ```
3. Write the declaration dump of the base:
   `sh fv/kraken/gen/restructure/tools/dump_all.sh <scratch>/dump-base.tsv`.
4. Run the axioms gate on the base, and keep its dump:
   `python3 -B fv/kraken/gen/checks/axioms_gate.py run <scratch>/gate-base.json <scratch>/gate-base.tsv`.
5. Run the Python checks on the base:
   `sh fv/kraken/gen/restructure/tools/python_checks.sh <scratch>/python-before`.
6. Run the regeneration comparison on the base:
   ```sh
   python3 -I -B fv/kraken/gen/restructure/tools/regen.py <scratch>/regen-before-work \
     --files fv/kraken/gen/restructure/maps/shared-layer/files.tsv \
     --files fv/kraken/gen/restructure/maps/flat-types/files.tsv > <scratch>/regen-before.txt
   ```

Make the map:

7. Copy `tools/build_maps_example.py` to a scratch directory, and change its tables for the step.
   Write `files.tsv`, `names.tsv`, `declared.txt` and `protect.txt` into `fv/kraken/gen/restructure/maps/<step>/`.
8. Run a trial without manual edits:
   `sh fv/kraken/gen/restructure/tools/trial.sh --no-manual fv/kraken/gen/restructure/maps/<step> <scratch>/trial`.
   Read every warning.
   Change the map until each warning left has a reason.
9. In the trial tree, find the lines that no rule can see.
   Write `manual-edits.tsv` for them (`TOOL-NOTES.md` section 2).
   Run the trial again with the manual edits.

Apply the step:

10. Run the forward mode on the working tree.
11. Do the hand edits with a script that asserts each old text once (lakefile, generator strings, README text).

Checks before the commit:

12. Inverse check against the base:
    ```sh
    sh fv/kraken/gen/restructure/tools/inverse_check.sh fv/kraken/gen/restructure/maps/<step> <base commit> WORKTREE <scratch>/inverse
    ```
    Expected: `PASS`.
    The new tree differs from the fresh forward run only in the hand-edited files.
    No file under `fv/kraken/lean` may differ.
13. Run `lake build` of every library of `lakefile.toml` (the command of item 2).
    Expected: exit 0.
14. Run the axioms gate:
    `python3 -B fv/kraken/gen/checks/axioms_gate.py run <scratch>/gate.json <scratch>/gate.tsv`.
    Expected: PASS. The count `declarations` of `<scratch>/gate.json` equals that of `<scratch>/gate-base.json`
    (item 4), or the difference is the declarations that the step adds or deletes, listed in the commit message.
    Then compare the two gate dumps across the map:
    ```sh
    python3 -I -B fv/kraken/gen/restructure/tools/gate_dump_compare.py <scratch>/gate-base.tsv <scratch>/gate.tsv fv/kraken/gen/restructure/maps/<step>
    ```
    Expected: exit 0 (no missing name, no extra name, no changed kind or axiom set).
15. Check the negative cases (cwd `fv/kraken`):
    `python3 -I -B gen/checks/negative.py --check-cases <every negcases*.json file>`.
    Expected: 0 failures.
    `python_checks.sh` runs this check with every tracked case file.
16. Run the Python checks after the step:
    `sh fv/kraken/gen/restructure/tools/python_checks.sh <scratch>/python-after`.
    Then run `diff -r <scratch>/python-before <scratch>/python-after`.
    Expected: the same rc for every check, and equal theorem line ranges of the negative cases.
    The text of the axioms gate self-test changes with the number of libraries.
17. Run the regeneration comparison after the step (the command of item 6, with new scratch names).
    Then `diff` the two results.
    Expected: the same lines, except generator outputs of the moved types that change from DIF to EQ.
18. Make one commit for the step.
    Follow `fv/AGENTS.md` for the title and the body.
    Record the base commit, the results of items 12 to 17, the warnings and their reasons, and the kept names.
    Record a reason for each difference from the expected results.
    Do not use `git add -A`, amend, rebase or force push.
