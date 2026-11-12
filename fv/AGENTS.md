# AGENTS.md

These rules apply to all agents and persons that change files under `fv/`.
The design principles are in `fv/README.md`. Each project has its own `fv/<project>/README.md`.
Git history and pull requests hold the history. The tree holds no reports, review records or session logs.

## Base rules

This file adopts [the AGENTS.md of EthLib](https://github.com/ethereum/EthLib/blob/8621856/AGENTS.md) as the base rules.
This file records only the differences and the additions. If the two documents conflict, this file has priority.

## Three sources

One theorem has three sources. If one source changes, check the theorem again.

| Source | What to record | Where |
| --- | --- | --- |
| Specification | EthLib commit, module, definition name | Theorem file header and `lean/README.md` |
| Target | Go source path, generator commit, Go version, build flags, ELF sha256 | The `build-ids.txt` files and the project `README.md` |
| Semantics | Kraken commit. For a PR branch, the PR number and "not in main" | `lake-manifest.json` and the project `README.md` |

The behavior of other clients and the output of the Go compiler are not evidence.

## Layout

Put `target/` (target Go), `link/` (build, conversion, link check), `lean/` (theorems) and `gen/` (generators and checkers) in `fv/<project>/`.
The documents are `README.md` in the project directory, a `README.md` in each directory that needs its own principles, and one `FINDINGS.md`.
A commit of one project does not touch files outside that directory.
Put external clones (`upstream/`, `vcgen-src/`) and generated files in `.gitignore`.

## Proofs

- Do not use `sorry`, `admit`, a new `axiom`, `native_decide` or `bv_decide`. The only axioms are `propext`, `Classical.choice` and `Quot.sound`.
- A contract hypothesis states the size range, the runtime-owned memory, the frame and the stack window. Do not quantify over "all sizes, all frames".
- For each main theorem, supply a witness: a concrete state that satisfies all premises. For variable length, use the empty value, 1 element and the maximum. Without a witness, the theorem is not complete.
- A postcondition keeps the input, the prefix, the frame, rsp after return and the preserved registers. Do not end it with `⋆ True`.
- Label freshness and global addresses are premises of the theorem. The `link/` check confirms that they hold in the real ELF.

## Checks

Before a PR, run the check commands of the project `README.md` and record the results in the PR body.
For a check that did not run, record that it did not run.

## Known answers

Take expected values from consensus-specs test vectors or from EthLib. Do not make expected values with the code under check.
One ELF hash binds the conversion result, `Code.lean`, the data files and the link check result. Print the hash after the last PASS line.

## Tool boundaries

- Do not change Kraken, gohashtree, `sszgen/`, `ssz/` or `fv/<project>/upstream/`.
- Record a missing instruction and a generator bug in the project `FINDINGS.md`.
- The user makes upstream PRs. Use an open PR branch only for tests, and record its source.
- A hash function is a contract until the `gohashtree` project proves it.

## Documents

- Documents are in English, in ASD-STE100 style. One sentence has 20 words at most, one sentence per line. Do not write a guess as a fact.
- A `README.md` gives design principles and commands that work. It does not record who did what, or when.
- Do not add reports, review records, attempt logs or result dumps to the tree. Put them in the PR.
- A status is a result that a check computes. Do not write a status by hand.
- Do not invent code names. A code name is a short letter or number label for a work unit, a step, a program path, a type, a review or a finding.
  This rule applies to file names, directory names, module names, declaration names, options, JSON keys, comments and documents.
  Use the full type name and plain words. A reader with no history must understand the name.
- A comment gives its reason in words. It does not point to a record outside the tree.
- The reviewer of a change checks its new names and comments against this rule.
- Git history keeps deleted content. Do not keep a file for the reason "historical material".

## Commits and PRs

- The title is an English Conventional Commits title `<type>(<scope>): <summary>`. The type is from the EthLib list + `proof`. The scope is `kraken`, `gohashtree`, `link`, `spec`, `contracts` or `negative`.
- At the end of the body, state the authoring model: `Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>`.
- PR body: the problem, the idea, one example, and what the reviewer must know. If the author is an AI agent, state it.

## Session operation

- Run only one heavy Lean build at a time. Check with `pgrep -fl "lean|lake"` and wait.
- Do not use absolute home directory paths in commands. Use `~` or `$HOME`.
- Delete directories with `trash`, not `rm`.
- Make a commit for each work unit. Update the progress with `orca worktree set --worktree active --comment "..."`.
- When the work is complete, run `orca worktree set --worktree active --workspace-status in-review --unread`.
- If an item is blocked, mark it as not run and go to the next item. Stop only when all of the work is blocked.
