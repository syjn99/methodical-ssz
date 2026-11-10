# Pins and drift (procedures 1-2)

## 1. Pins

A claim is about one exact set of inputs. Record all of them before work starts and again in the report.

| Pin | Where it is read |
| --- | --- |
| Reviewed base commit (full SHA) | the review that accepted it; `git rev-parse <sha>^{commit}` |
| Target ELF sha256 | `link/out/build-ids.txt` or the project's `build-ids.txt` |
| Generator commit (`sszgen/`, `ssz/`) | the commit recorded in `fv/kraken/TOOLS.md` and `build-ids.txt`. `git rev-parse HEAD:ssz` gives a tree id, not a commit; record it only as "`ssz/` tree id" |
| Go version and build flags | `build-ids.txt`, `TOOLS.md` |
| Kraken commit | `lean/lake-manifest.json` |
| Lean toolchain | `lean/lean-toolchain` |

Rules:
- Copy values from those files. Do not type them from memory.
- If a pin changes, every claim that depends on it is open again. See `evidence.md` (bug loop).
- Limit: pins identify inputs. They do not show that the inputs are correct.

## 2. Preserved statements, definitions and witnesses

What must stay as reviewed:
- the statement of every reviewed theorem;
- every definition the statement mentions, directly or through other definitions (also private and auxiliary ones);
- the meaning of every witness: a concrete state that satisfies all hypotheses of the main theorem.
  A witness that still compiles but now satisfies weaker hypotheses has changed meaning. A reviewer reads it.

### Per-declaration drift check

`scripts/decl_dump.lean` prints one line per declaration of the chosen module roots:
name, kind, type hash, value hash (only `def` and `opaque`), sorted axiom set from `Lean.collectAxioms`.
`scripts/decl_drift.py BASE.tsv HEAD.tsv [--allow FILE]` compares two dumps in both directions:
REMOVED, ADDED, CHANGED (kind, type, value, axioms).

Steps:
1. Build the reviewed base in a separate checkout (for example `git worktree add` or `git archive` into scratch). Build the head.
2. In each tree, under the gate, dump the same modules with the same toolchain, for example from `fv/kraken/lean`:
   `lake env lean --run <repo>/.claude/skills/maintaining-methodical-fv/scripts/decl_dump.lean Fk Fv.Spec Fv1.SpecScalars ... > dump.tsv`
   (use the import list of `lean/tools/AxiomsAll.lean`). This has NOT yet been run on the Kraken tree.
3. Run `decl_drift.py base.tsv head.tsv --allow allow.txt`.
4. Every line is fixed or allowlisted. Allowlist format: `<full declaration name> <reason>`, one per line.
   An allowlist entry that matches no drift fails the check, so the list stays the exact set of intended changes.
   The allowlist is by name only: an allowlisted name passes any change to it (kind, type, value, axioms, REMOVED).
   The reviewer must read every ALLOWED line and check that the change is the one the reason describes.
5. Give the reviewer the drift output, the allowlist and both SHAs.

An axiom-set change is drift even when every axiom is on the allowed policy list (`propext`, `Classical.choice`, `Quot.sound`).
`lean/tools/axioms.sh` checks the policy. It does not detect a theorem that now uses `Classical.choice` and did not before.

### Negative controls

A check that never fails proves nothing. For each new setup (new toolchain, new module list), plant at least one change
in a scratch copy and show that the check reports it: a changed private definition, a changed statement, or a proof that
now uses `Classical.em`. `scripts/selftest.sh` does this on fixtures; repeat it on the real tree before the first real use.

### Limits (state them in the report)

- `Expr.hash` is a structural hash; on the tested toolchain it has only 32 bits. A collision can hide a change. It ignores binder names
  and binder kind (explicit, implicit, instance-implicit): `(n : Nat)` changed to `{n : Nat}` is not drift.
- Equal hashes or equal printed Lean text are not a proof of definitional equivalence. A different hash does not say what changed.
- Hashes are comparable only between dumps from the same Lean build. `decl_drift.py` refuses different `lean=`/`githash=` headers.
- Theorem proofs are not hashed. A changed proof is visible only if its axiom set changes. That is intended: the statement is the claim.
- Private names contain the module name. Auto-generated names (`match_1`, `proof_1`, `_eq_1`, instance names) can shift
  when an unrelated declaration changes. Such lines are drift until a reviewer reads them and allowlists them with a reason.
  Auxiliary proofs also drift when a definition they unfold changes: in the fixture, changing a private
  definition also changed the type of `Fix.pub_pos._proof_1_1`.
- Not covered: attributes (`simp`, `reducible`, `irreducible`, instance priority), notation and macros, `set_option`,
  `implemented_by`/`extern`, docstrings, and anything outside the dumped roots.
