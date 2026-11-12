# restructure: rename maps and the rename tool

This directory holds the tool and the maps that move Lean modules and rename namespaces and declarations under `fv/`.
Each step of the restructuring has one map directory under `maps/`.
Remove this directory when the restructuring ends.

## 1. The tool

`rename.py` applies one map directory to the tree, or undoes it. It uses only the Python 3 standard library.

```sh
python3 -I -B fv/kraken/gen/restructure/rename.py forward fv/kraken/gen/restructure/maps/<step>
python3 -I -B fv/kraken/gen/restructure/rename.py inverse fv/kraken/gen/restructure/maps/<step> [--root <copy>]
```

The forward mode does these steps:

1. It checks that no new name or new path of the maps occurs in the old text. Else the inverse would not be exact, and the tool stops.
2. It moves the files of `files.tsv`.
3. It rewrites the text files under `fv/`: `import` lines, qualified names and module names, renamed short names, and the paths of moved files.
4. In Lean files it also rewrites the `namespace`, `end` and `open` lines.
   An `open` of a namespace that the step splits becomes an `open` of the new namespaces that the imports of the file declare.
   A file in a split namespace gets an inserted `open` line before its first `namespace` line.
   An `open` gets a `hiding` clause for a name that the old `open` did not make visible and that the file uses.
5. It applies `manual-edits.tsv`.
6. It writes `applied-lines.tsv`: every `namespace`, `end` and `open` line that it changed, inserted or deleted.

A map with at least one `type` row runs in reference mode (section 3). A map without one keeps the steps above.

The inverse mode reads `applied-lines.tsv` and `manual-edits.tsv` and does the steps in the reverse order.
The tool does not change this directory or the files that `protect.txt` names.
It moves files with a plain rename. It does not stage the moves in git.

## 2. A map directory

| File | Content |
| --- | --- |
| `files.tsv` | Old path, new path and the meaning of the file. A `.lean` file under `fv/kraken/lean/` also gives the module rename |
| `names.tsv` | Namespace rows (old namespace, new namespace, library of the module) and declaration rows (old name, new name, library, new module) |
| `manual-edits.tsv` | New path, line, the text after the automatic rewrite, the final text. Only for a change that the rules cannot make |
| `protect.txt` | Glob patterns of files whose text the tool does not change (records of runs, pinned files, the Lake configuration) |
| `applied-lines.tsv` | Written by the forward mode. The inverse mode needs it |
| `removed/` | Files that the step removes. They stay here so that the inverse mode can restore them |

A namespace row applies to the modules of its library. The longest old prefix wins.
A declaration row comes from a Lean declaration dump of the old tree.

A reference-mode map adds these files and rows (every `names.tsv` row has five columns; `-` marks an unused column):

| Row or file | Columns or content |
| --- | --- |
| `type` row | The namespace of one type, for example `Prysm.Checkpoint` |
| `namespace` row | Old namespace, new namespace, scope, `whole` or `part`. The scope is a prefix of the new module name, or `MODULE#N`: only the N-th top-level `namespace` block of that new module |
| `open` row | Old namespace, new namespace, type namespace of the file (`-` for a file outside every type, `*` for every file) |
| `declaration` row | Old full name, new full name, library, new module. List every declaration of the moved modules, the generated ones included (`.eq_1`, `.mk`, fields) |
| `declared.txt` | Optional. Old-tree names that the step does not move and whose last component is a component of a moved name |

The most specific namespace row wins: a `MODULE#N` row, then the longest module prefix, then the longest old namespace.
Two declaration rows can have the same old name if their new modules differ. A reference takes the row whose
module is in the import closure of the file.

## 3. Reference mode

The renames are keyed on the full old name and the declaring module, never on the last name component alone.

1. The forward mode checks that no new full name, new module name or new path occurs in the old text.
2. In a Lean file it tracks the scope of each line: the namespace blocks, the `open` lines (also `open ... in`
   and `hiding`), and the namespace that a dotted declaration name opens. It resolves each identifier as Lean does:
   the innermost namespace first, then the root name and the opened namespaces.
3. The reference rule. A reference to a moved declaration gets the full new name if the old text had the full old
   name, or if the line is outside the namespace of the declaring type. Else it gets the shortest form that
   resolves to exactly that declaration in the new scope. The tool can drop a prefix of the current namespace or an
   opened namespace, but not the namespace of a dotted declaration name.
4. A declaring line gets the new name relative to its new namespace block. If the new name is not inside that
   block, the line gets the root-qualified name (`def _root_.Prysm.Epoch.Code.unmarshalSSZ`).
5. An `open` of an old namespace becomes the `open` rows that match the type of the file. The type of a file comes
   from its namespace or from its new module path. The tool never opens the namespace of another type.
   An item without a row is removed, except an old namespace that the imports of the file still declare.
   A line without items is deleted.
6. In other text files the tool rewrites paths first, then full old names (declarations, modules, `whole`
   namespaces). An old last name component that is unique among the moved declarations, that changes, and that no
   name of `declared.txt` has as last component becomes the full new name.
7. In a JSON file of negative cases (objects with `module` and `theorem`), the fields are rewritten in the scope of
   that theorem: `theorem` becomes the full new name, `code_def` the form that the module writes, `code_ns` the new
   namespace, and `old`, `new`, `diff` like Lean text.
8. Every line that the rule-based inverse (full names, modules, paths) does not restore goes to `applied-lines.tsv`.
   The forward mode runs the inverse in memory and stops if it does not give the old text.
9. It prints a warning for a token that it did not change and that now resolves to a new name (a capture, or a
   local variable), for an ambiguous old reference, and for a name that needs `_root_`.

Limits: the scope tracker reads lines, not Lean syntax. It knows only the names of the maps and of `declared.txt`.
It does not know local variables. A proof that depends on the order of names (for example `simp` with
commutativity lemmas, which orders terms by constant names) can break after a rename. Only a build shows it.

Several maps apply one after another on the same tree: shared-layer, then checkpoint-and-epoch, then the next one.
Each forward run reads only its own map. To undo them, run the inverse of the last map first. The inverse of one
map alone gives the tree from which its forward run started.
Do hand edits (the Lake configuration, generator strings, runner logic) after the forward run. A hand edit before
the run puts new names into the old text, and the forward check then stops.

## 4. Steps

- `maps/shared-layer/`: the shared libraries `Machine`, `Runtime`, `TestTarget`, `Spec` and `Codec` (from `Fk`, `Fv`, `Fv1`, `E2eSeg`, `E2e/WitSplit.lean` and the type-independent modules of `E2eScal`).
- `maps/checkpoint-and-epoch/`: the first type step: the library `E2e` becomes `Prysm/Checkpoint/`, `Prysm/Epoch/` and `Prysm/ElfData/` (library `Prysm`). The first map in reference mode.
