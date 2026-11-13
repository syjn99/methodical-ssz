import Machine.WitnessHost

/-!
# `witness_split_n`: variant for the Prysm witnesses of `Machine.Witness.witness_split`

Same macro as `Machine.Witness.witness_split` (`Machine/WitnessHost.lean`, unchanged). The only change: the simp set of the
side goal of `Mem.At_append_sep` (`l1`) also has `← Nat.add_assoc` and `Nat.reduceAdd`. Then the
chunk-length sum is normalised to `K + n` before `omega`. Without them, `omega` spends most of the
build time of the cover witnesses on a failing definitional check of the unnormalised sum (audit
profile: 92–94 % of the `Prysm/Checkpoint/WitnessEncodeCover.lean` / `Prysm/Checkpoint/WitnessEncodeRejectLengthCover.lean` build time is this one side goal).

Only proof scripts change. Statements, definitions and witness states stay the same.
Used by `Prysm.Checkpoint.WitnessEncodeCover`, `Prysm.Checkpoint.WitnessEncodeCoverFramed`, `Prysm.Checkpoint.WitnessEncodeRejectLengthCover`, `Prysm.Checkpoint.WitnessEncodeRejectLengthCoverFramed`.
-/

open Machine

namespace Machine.Witness.Normalized

/-- Split `H : Eq ((block ..).At a) m` into one `Eq (chunk.At addr)` per chunk and normalize the
addresses (as `Machine.Witness.witness_split`); the side goal also normalises `a + (b + c)` sums of literals. -/
syntax "witness_split_n" (" [" term,* "]")? : tactic
set_option hygiene false in
macro_rules
  | `(tactic| witness_split_n $[[$hs,*]]?) => do
    let hs := (hs.map (·.getElems)).getD #[]
    let ls ← hs.mapM fun h => `(Lean.Parser.Tactic.simpLemma| $h:term)
    let l1 := #[← `(Lean.Parser.Tactic.simpLemma| List.length_append), ← `(Lean.Parser.Tactic.simpLemma| List.length_replicate),
      ← `(Lean.Parser.Tactic.simpLemma| Int.toBytes_length), ← `(Lean.Parser.Tactic.simpLemma| List.length_cons),
      ← `(Lean.Parser.Tactic.simpLemma| List.length_nil), ← `(Lean.Parser.Tactic.simpLemma| ← Nat.add_assoc),
      ← `(Lean.Parser.Tactic.simpLemma| Nat.reduceAdd)] ++ ls
    let l2 := #[← `(Lean.Parser.Tactic.simpLemma| List.length_replicate), ← `(Lean.Parser.Tactic.simpLemma| Int.toBytes_length),
      ← `(Lean.Parser.Tactic.simpLemma| List.length_cons), ← `(Lean.Parser.Tactic.simpLemma| List.length_nil),
      ← `(Lean.Parser.Tactic.simpLemma| Nat.reduceAdd)] ++ ls ++
      #[← `(Lean.Parser.Tactic.simpLemma| BitVec.ofNat_eq_ofNat), ← `(Lean.Parser.Tactic.simpLemma| BitVec.reduceAdd)]
    `(tactic| (
      conv at H => lhs; unfold block
      repeat rw [Mem.At_append_sep _ _ _ (by simp only [$l1,*]; omega)] at H
      simp only [$l2,*] at H))

end Machine.Witness.Normalized
