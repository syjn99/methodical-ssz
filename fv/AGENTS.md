# AGENTS.md

These rules apply to all agents and persons that change files under `fv/`.
Direction and trust base decisions are in `fv/<project>/DIRECTION.md`, the current status is in `REPORT.md`, and the history is in `HISTORY.md`.

## Base rules

This file adopts [the AGENTS.md of EthLib](https://github.com/ethereum/EthLib/blob/8621856/AGENTS.md) as the base rules.
This file records only the differences and the additions. If the two documents conflict, this file has priority.

## Three sources

One theorem has three sources. If one source changes, check the theorem again.

| Source | What to record | Where |
| --- | --- | --- |
| Specification | EthLib commit, module, definition name | Theorem file header and `SPEC.md` |
| Target | Go source path, generator commit, Go version, build flags, ELF sha256 | `link/out/build-ids.txt` and `TOOLS.md` |
| Semantics | Kraken commit. For a PR branch, the PR number and "not in main" | `lake-manifest.json` and `TOOLS.md` |

The behavior of other clients and the output of the Go compiler are not evidence.

## Layout

Put `target/` (target Go), `link/` (build, conversion, link check), `lean/` (theorems), `negative/` (negative tests) and `review/` (review texts and Lean regression files) in `fv/<project>/`.
The documents are `DIRECTION.md`, `REPORT.md`, `HISTORY.md`, `CONTRACTS.md`, `SPEC.md` and `TOOLS.md`.
A commit of one project does not touch files outside that directory.
Put external clones (`upstream/`, `vcgen-src/`) and generated files in `.gitignore`.

## Proofs

- Do not use `sorry`, `admit`, a new `axiom`, `native_decide` or `bv_decide`. The only axioms are `propext`, `Classical.choice` and `Quot.sound`.
- A contract hypothesis states the size range, the runtime-owned memory, the frame and the stack window. Do not quantify over "all sizes, all frames".
- For each main theorem, supply a witness: a concrete state that satisfies all premises. For variable length, use the empty value, 1 element and the maximum. Without a witness, the theorem is not complete.
- A postcondition keeps the input, the prefix, the frame, rsp after return and the preserved registers. Do not end it with `⋆ True`.
- Label freshness and global addresses are premises of the theorem. The `link/` check confirms that they hold in the real ELF.

## Checks

Before a PR, run all commands in the Reproduction section of `REPORT.md` and record the results.
For a check that did not run, record that it did not run.
If the hardware comparison did not run, record this in the trust items of `REPORT.md`.

## Known answers

Take expected values from consensus-specs test vectors or from EthLib. Do not make expected values with the code under check.
One ELF hash binds the conversion result, `Code.lean`, `AXIOMS.txt` and the check logs. Print the hash after the last PASS line.

## Tool boundaries

- Do not change Kraken, gohashtree, `sszgen/`, `ssz/` or `fv/<project>/upstream/`.
- Record a missing instruction in `REPORT.md` "Kraken request list". Record a generator bug in the "Findings" section.
- The user makes upstream PRs. Use an open PR branch only for tests, and record its source.
- A hash function is a contract until the `gohashtree` project proves it.

## Documents

- Documents are in English, in ASD-STE100 style. One sentence has 20 words at most, one sentence per line. Do not write a guess as a fact.
- `REPORT.md` starts with the verdict (`possible`, `conditional`, `not possible`). If the verdict is conditional, the list of conditions follows immediately.
- `REPORT.md` records only the current status. Record session history and retractions in `HISTORY.md` as one paragraph.
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
