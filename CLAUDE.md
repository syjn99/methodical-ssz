# CLAUDE.md

Claude Code does not load `AGENTS.md` by itself. The imports below load the shared policy
only when the session starts in the repository root. Start FV sessions there.

@AGENTS.md
@fv/AGENTS.md

If the rules of `AGENTS.md` and `fv/AGENTS.md` are not in your context
(for example, the session started in a subdirectory), read both files from the repository root before FV work.

Before FV work (proofs, generator output, Lean builds, drift or review reports, findings),
read the project skill `maintaining-methodical-fv`.
If the Skill tool is not available, read the file directly:
`.claude/skills/maintaining-methodical-fv/SKILL.md` (from the repository root), then the `references/` file it names for the task.
