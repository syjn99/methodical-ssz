# Evidence, findings and the bug loop (procedures 6-9)

## 6. Classify every run

| Class | Meaning | Counts as |
| --- | --- | --- |
| pass | ran to completion, exit 0, all expected lines present | pass |
| expected-fail-inside-target | a negative test failed at the planted defect, with the expected error at the expected place | negative test passed |
| timeout | killed by a timeout or memory cap | nothing; report and rerun or investigate |
| wrong-target | failed for another reason: syntax error, missing import, wrong file, unrelated error | nothing; the test is broken |

Rules:
- A negative test passes only if it fails *inside the target*. Check the error text and position, not only the exit code.
- A timeout or a wrong-target failure is never a passed negative test.
- A run that did not happen is "not run", never "pass".

## 7. Three kinds of evidence

Keep them in separate sections of every report. Never present one as another.

| Kind | Examples | What it shows |
| --- | --- | --- |
| Executable evidence | Go tests, differential tests, witness evaluation, link checks, hardware comparison | behaviour on the inputs that ran |
| Kernel-checked proof | a theorem that compiles with the allowed axioms, its axiom set listed | the statement, under its hypotheses and pins |
| Reviewed claim | text a reviewer read: contracts, witness meaning, "this statement means X" | a person or model's judgement |

- A passing test is not a proof. A proof under a contract hypothesis does not prove the contract.
- A reviewer's agreement is a reviewed claim, not a kernel check.
- Contract hypotheses stay listed as hypotheses until a proof discharges them.

## 8. Findings ledger

- Each finding gets an ID once (for example `F1`, `F2`). Never rename or reuse an ID, also after it is closed or withdrawn.
- Each entry: ID, first seen (commit), state (open, fixed, withdrawn, accepted), evidence kind, short text.
- Each checkpoint report lists the delta: new IDs, state changes, and IDs whose evidence changed.
- A withdrawn finding stays in the ledger with the reason. The history goes to `HISTORY.md`, per `fv/AGENTS.md`.

## 9. Bug loop

1. Reproduce: a minimal input and an executable failure (or a proof that cannot close for a stated reason).
2. Record the finding with a new ID.
3. Get approval for the fix. Agents do not modify `sszgen/` or `ssz/` (`fv/AGENTS.md`).
   For a generator bug the agent reports the finding; the user makes or approves the generator change.
   A change to the target binary also needs explicit user approval.
4. Regenerate the target with `regen_check.sh`-style determinism, rebuild, and record the new pins (new ELF sha256).
5. Recompile and re-prove. A proof about the old binary does not transfer to the changed binary automatically.
   Retargeting tables are PROPOSED, not available.
6. Rerun the drift check against the reviewed base; allowlist only reviewed, intended changes.
7. Benchmark under the same conditions as the baseline, with a control module.
8. Fresh independent review before any claim.
