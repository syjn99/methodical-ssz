# Builds: profiling, regeneration, stale artifacts (procedures 3-5)

All commands here that run `lake`, `lean`, `go` or the generator are heavy. Run them under the heavy-job gate, one at a time,
with a memory cap and a timeout.

## 3. Profile before raising a tactic limit

Status: procedure only. Profiler automation is PROPOSED.

1. Isolate the slow declaration. Build only its module.
2. Profile that declaration, for example with `set_option trace.profiler true` and `set_option profiler true`
   in a scratch copy of the file, under the gate. Do not commit the options.
3. Name the cause in the report: which tactic, which `isDefEq`, which `simp` set, which instance search, what share of time.
4. Prefer a fix in the shared lemma or tactic layer over a local limit increase. Keep the statement unchanged.
5. Raise `maxHeartbeats` or `maxRecDepth` only with the recorded cause and the measured value. Record the old and new limit.

Limits: one profile is one measurement. Compare against an untouched control module when you claim a speed-up.
Wall time on a shared machine varies; report the conditions.

## 4. Deterministic regeneration

Status: IMPLEMENTED AND TESTED as `scripts/regen_check.sh` (toy generators only). Running it as a step of the proof gate is PROPOSED.

```sh
sh .claude/skills/maintaining-methodical-fv/scripts/regen_check.sh <committed path> -- <generator argv...>
```

The generator gets `REGEN_OUT` (a fresh scratch path) and must write there what it writes to the committed path.
It runs twice. Exit 0 same; 1 differs from committed; 3 generator failed; 4 no output; 5 two runs differ; 2 usage.
Exit 3, 4 or 5 is never a pass.
Most generators take an output flag; wrap them in `sh -c '... --output="$REGEN_OUT"'`.

Limits: byte equality only. It does not show the output is correct. A generator that copies the committed file passes trivially;
check that the generator reads the real sources. Changing the generator itself needs user approval (root `AGENTS.md`).

## 5. Stale artifacts after a capped or killed build

Status: IMPLEMENTED AND TESTED as `scripts/stale_olean.py` (temp trees with crafted mtimes only).

A memory cap or a timeout can kill a build after some `.olean` files were written. A later "pass" can then use them.

```sh
python3 -I .claude/skills/maintaining-methodical-fv/scripts/stale_olean.py \
  --src fv/kraken/lean --build fv/kraken/lean/.lake/build/lib/lean --marker <file touched at job start>
```

Flags: STALE (older than its source), ORPHAN (source missing), AFTER (written at or after the marker or `--since` epoch).
Exit 0 nothing flagged, 1 flagged, 2 usage (including no artifacts found).

Before you trust a pass after a killed build, do one of:
- run `stale_olean.py` with the killed job's start time and rebuild every flagged module; or
- rebuild clean in a fresh copy (`git archive` into scratch). The independent reviewer does this anyway.

Limits: mtimes only. It does not read Lake trace hashes and does not follow imports.
A module whose dependency changed but whose own source did not is not flagged. Clean output is not proof of a sound build.
