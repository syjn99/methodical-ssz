# AGENTS.md

These rules apply to all agents and persons that change files under `fv/`.
Read these documents before you start:

- `README.md`: what a proof says, the trust base, and when one function is done.
- `kraken/README.md`: the pins and the check commands.
- `kraken/NEW-TYPE.md`: the steps to prove a type.
- `kraken/FINDINGS.md`: the limits that are open.

Git history and pull requests hold the history.
The tree holds no reports, review records or session logs.

## Proofs

- Do not use `sorry`, `admit`, a new `axiom`, `native_decide` or `bv_decide`. The only axioms are `propext`, `Classical.choice` and `Quot.sound`.
- Do not weaken a statement to make a proof close. If a proof needs a weaker statement, stop and report.
- A contract hypothesis states the size range, the runtime-owned memory, the frame and the stack window. Do not quantify over "all sizes, all frames".
- A contract stays a hypothesis until a proof discharges it. Do not present it as proved.
- For each main theorem, supply a witness: a concrete state that satisfies all premises. For variable length, use the empty value, 1 element and the maximum.
- A postcondition keeps the input, the prefix, the frame, rsp after return and the preserved registers. Do not end it with `⋆ True`.
- Label freshness and global addresses are premises of the theorem. The link check confirms that they hold in the real ELF.
- Do not add or raise `maxHeartbeats` or `maxRecDepth` without a measured cause. Write the cause in a comment above the option.
- Do not change a generated file by hand. Change its row or its tool, and run the tool again.
- Take expected values from consensus-specs test vectors or from EthLib. Do not make expected values with the code under check.
- The behavior of other clients and the output of the Go compiler are not evidence.

## User approval

Get the approval of the user, each time, before one of these actions:

- A change to `sszgen/`, `ssz/`, Kraken, EthLib, the Lean toolchain, the Go version, the build flags or the target ELF.
- A new runtime contract form, a change to a contract hypothesis, or a new item of the trust base.
- A push to `fv` or `main`, a merge, a branch deletion, a release, or a write to another repository.

On `syjn99/methodical-ssz`, an agent may push `u/*` branches and may open, update and comment on issues and PRs.
Record a missing instruction or a generator bug in `kraken/FINDINGS.md`. The user makes upstream PRs.

## Checks

- Before a PR, run the check commands of `kraken/README.md` section 5.
- CI runs the build and the axioms gate. For a check that did not run, write "not run" in the PR body.
- A timeout or an out-of-memory kill is a result. It is not a pass.
- The author of a change does not review it.

## Documents and names

- Documents are in English, in ASD-STE100 style. One sentence has 20 words at most, one sentence per line. Do not write a guess as a fact.
- A document gives design principles and commands that work. It does not record who did what, or when.
- Do not add reports, review records, attempt logs or result dumps to the tree. Put them in the PR.
- A status is a result that a check computes. Do not write a status by hand.
- Do not invent code names. A code name is a short letter or number label for a work unit, a step, a program path, a type, a review or a finding.
  This rule applies to file names, directory names, module names, declaration names, options, JSON keys, comments and documents.
  Use the full type name and plain words. A reader with no history must understand the name.
- A label that a tool prints is not a code name if one document list defines each value.
  Examples are the check letters of `kraken/link/check.py` and the rule numbers of `kraken/gen/generator/kindcheck.py`.
- A comment gives its reason in words. It does not tell the history of the file.
- Git history keeps deleted content. Do not keep a file, an alias or an option for an earlier state of the tree.

## Commits and PRs

- The title is an English Conventional Commits title `<type>(<scope>): <summary>`.
  The type is `feat`, `fix`, `proof`, `refactor`, `docs`, `test`, `build`, `ci`, `style` or `chore`.
  The scope is `kraken`, `gohashtree`, `link`, `spec`, `contracts` or `negative`.
- If the author is an AI agent, the last line of the commit body is `Co-Authored-By: MODEL-NAME <E-MAIL-ADDRESS>` for that model.
- Do not amend, rebase, reset or force push. Add new commits.
- The PR body has two sections, `Problem` and `Solution`. Each section has three bullets at most. One bullet is one sentence.

## Work units

- One unit is one obligation of one function of one type. Its name is its Lean name, for example `Prysm.Checkpoint.Decode.reject_size`.
- One issue on `syjn99/methodical-ssz` holds one type, one unit or one group of types on one decode path. The issue title names it.
- If an issue names an earlier issue, wait until the PR of the earlier issue is merged.
- To take an issue, add the label `wip` and write a comment that gives your branch name.
  Do not take an issue that has this label, such a comment or an open PR.
- The branch name is `u/<issue number>-<type name>`. Start it from `fv`.
- Change only `kraken/lean/Prysm/<Type>/`, the negative cases of that type and the generator rows of that type.
- Do not change `Machine`, `Runtime`, `Codec` or `Spec` in a unit. If a general lemma is necessary, keep it in the type directory and name it in the PR.
- Open the PR against `fv` with `Closes #<issue number>`.
- A session that did not write the change reviews the PR. It reads each new theorem statement against the EthLib definition.
- If the unit is blocked, write the cause in the issue. Then remove the label `wip` and delete your branch-name comment.

## Session operation

- Do not wait for `lean --server` or `lake serve`: they are editor processes. To see builds, use `pgrep -lx lean` and `pgrep -lx lake`.
- Do not print the environment or the full command line of other processes. Do not use `pgrep -f` or `ps e`.
- Do not use absolute paths of one machine in commands or in tracked files. Use `~`, `$HOME` or a path relative to the repository.
- Do not start a long command and wait for a notification. Run it in the foreground, or read its log.
- Read the result line of a check, for example `Build completed successfully`. Do not trust the exit code of a pipe.
- If an item is blocked, mark it as not run and go to the next item. Stop only when all of the work is blocked.
