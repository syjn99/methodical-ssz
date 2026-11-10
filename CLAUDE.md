# CLAUDE.md

Claude Code does not load `AGENTS.md` by itself. These imports load the shared policy:

@AGENTS.md
@fv/AGENTS.md

Before FV work (proofs, generator output, Lean builds, drift or review reports, findings),
read the project skill `maintaining-methodical-fv`.
If the Skill tool is not available, read the file directly:
`.claude/skills/maintaining-methodical-fv/SKILL.md`, then the `references/` file it names for the task.
