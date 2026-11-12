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

## 3. Steps

- `maps/shared-layer/`: the shared libraries `Machine`, `Runtime`, `TestTarget`, `Spec` and `Codec` (from `Fk`, `Fv`, `Fv1`, `E2eSeg`, `E2e/WitSplit.lean` and the type-independent modules of `E2eScal`).
