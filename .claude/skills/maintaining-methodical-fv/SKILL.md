---
name: maintaining-methodical-fv
description: >-
  Procedures for formal-verification work under fv/ in methodical-ssz (Lean/Kraken proofs about
  generated Go SSZ code). Use before you change or review a proof, a theorem statement, a contract,
  a witness, generator output or a target binary; before you raise maxHeartbeats/maxRecDepth; after a
  capped, killed or failed Lean build; when you compare a branch with a reviewed baseline (statement or
  axiom drift); when you classify a run (pass, expected fail, timeout, wrong target); and when you write
  a report, a findings ledger or a bug-fix loop. Includes tested scripts: decl_dump.lean + decl_drift.py,
  stale_olean.py, regen_check.sh.
---

# Maintaining methodical-ssz FV

Policy first: root `AGENTS.md` (roles, prohibitions, approvals) and `fv/AGENTS.md` (invariants; wins on conflict).
This skill says *how*. It never relaxes a rule in those files.

## Gate status

IMPLEMENTED AND TESTED (scripts in `scripts/`, controls in `scripts/selftest.sh`):

| Script | Checks | Exit codes |
| --- | --- | --- |
| `decl_dump.lean` + `decl_drift.py` | per-declaration kind, type hash, def value hash, axiom set; base vs head, both directions, name allowlist with reasons | 0 clean, 1 drift, 2 usage |
| `stale_olean.py` | `.olean`/`.ilean` older than source, orphaned, or written after a failed-job marker | 0, 1 flagged, 2 usage |
| `regen_check.sh` | generator rerun twice into scratch, compared with committed output | 0 same, 1 differ, 3 generator failed, 4 no output, 5 nondeterministic, 2 usage |

Tested means: all 34 selftest controls passed on core-Lean fixtures and temp trees, with the toolchain in
`fv/kraken/lean/lean-toolchain`. Deliberately broken copies of the scripts made the selftest fail;
a behaviour with no control is not tested. The selftest needs GNU `date -d` and `touch -d`.
`decl_dump.lean` has NOT yet been run on the Kraken tree (`fv/kraken/lean`). Its first run there is a separate, gated unit.

PROPOSED (not implemented; never cite as a gate that ran):
profiler automation and per-module cause breakdown; generator rerun as a step of the proof gate;
mechanical retargeting tables (instruction index / pc maps) for a changed binary;
Lake trace-hash staleness check; measurement A/B with an untouched control module.

Run the selftest after any change to `scripts/`, under the heavy-job gate (it runs `lean`):

```sh
LEAN_TOOLCHAIN=$(cat fv/kraken/lean/lean-toolchain) sh .claude/skills/maintaining-methodical-fv/scripts/selftest.sh
```

Exit 0 = every control ran and passed; 1 = a control failed; 3 = controls skipped (`--no-lean`), which is not a pass.

## Procedures

Each procedure has limits. State them in the report.

1. **Pins** (`references/pins-and-drift.md`).
   Record the reviewed base SHA, target ELF sha256, generator commit, Go version and flags, Kraken commit, Lean toolchain.
   Read them from the files named in `fv/kraken/TOOLS.md`, not from memory. A claim is tied to these pins only.
2. **Preserved statements and drift** (`references/pins-and-drift.md`).
   Theorem statements, every definition they reference, and the meaning of each witness stay as reviewed.
   Run `decl_drift.py` base vs head; every drift is either fixed or allowlisted by name with a reason.
   The allowlist passes any change to a listed name: the reviewer reads every ALLOWED line.
   "Same allowed axiom policy" is not "no drift". Equal hashes or equal printed text do not prove definitional equivalence.
   Prove the check can fail: run at least one negative control (a planted change) on the same setup.
3. **Profile before raising a limit** (`references/builds.md`).
   Before any `maxHeartbeats` or `maxRecDepth` increase, profile the one declaration and record the named cause.
4. **Deterministic regeneration** (`references/builds.md`).
   Rerun the generator into scratch with `regen_check.sh` and compare with the committed output.
5. **Stale artifacts** (`references/builds.md`).
   After a capped, killed or failed build, run `stale_olean.py` with the job start as marker, or rebuild clean.
   Do not trust a pass that follows a killed build until one of the two is done.
6. **Run classification** (`references/evidence.md`).
   Every run is one of: pass, expected-fail-inside-target, timeout, wrong-target.
   A timeout or a wrong-target failure is never a passed negative test.
7. **Three evidence kinds** (`references/evidence.md`).
   Executable evidence, kernel-checked proofs and reviewed claims stay separate in every report. Never upgrade one into another.
8. **Findings ledger** (`references/evidence.md`).
   Stable historic IDs, never renamed or reused. Each checkpoint reports the delta.
9. **Bug loop** (`references/evidence.md`).
   Reproduce, get an approved fix, regenerate, recompile, re-prove, benchmark.
   A proof about the old binary does not transfer to a changed binary.
10. **Hard rules** (root `AGENTS.md`, `fv/AGENTS.md`).
    No `sorry`/`admit`/new `axiom`/`native_decide`/`bv_decide`; no weakened statement; no unproved callee contract;
    no new runtime-contract form without explicit user approval; heavy jobs serialized under the gate with a memory cap;
    stop when the unit's attempt limit is used up.

## Reporting a gate result

Quote the command, the exit code and the output file path. Name the base and head SHAs.
If a gate did not run, write "not run" and why. A PROPOSED gate is never reported as run.

## References

- `references/pins-and-drift.md`: procedures 1-2, `decl_dump`/`decl_drift` usage and limits.
- `references/builds.md`: procedures 3-5, `regen_check.sh` and `stale_olean.py` usage and limits.
- `references/evidence.md`: procedures 6-9.
- `references/ATTRIBUTION.md`: adapted ideas, source pins, license, what was not adopted.
