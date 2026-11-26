module
public import Kraken.Separation
public meta import Lean

/-!
`sep_perm h` closes a goal `Q m'` from `h : P m`.
`P` and `Q` have the same conjuncts in a different order or grouping.
`m'` and `m` are definitionally equal.

The tactic uses `ac_rfl`, because a `simp` sort with `sep_comm` is very slow on long conjunctions.
`ac_rfl` compares conjuncts by syntax.
Thus the tactic first replaces each conjunct of `Q` by the definitionally equal conjunct of `P`.
-/

open Lean Elab Tactic Meta

namespace Machine.SepPerm

/-- The conjuncts of a separating conjunction `p ⋆ q`, or of `(p ⋆ q) m`. -/
meta partial def conjuncts (e : Expr) : Array Expr :=
  if e.isAppOf ``Std.ExtHashMap.sep && e.getAppNumArgs ≥ 8 then
    conjuncts (e.getArg! 6) ++ conjuncts (e.getArg! 7)
  else #[e]

end Machine.SepPerm

/-- Close `Q m'` from `h : P m`. See the module documentation. -/
elab "sep_perm " h:term : tactic => withMainContext do
  let hType ← whnfR (← instantiateMVars (← inferType (← elabTerm h none)))
  let goal ← whnfR (← instantiateMVars (← getMainTarget))
  let hParts := Machine.SepPerm.conjuncts hType
  let qParts := Machine.SepPerm.conjuncts goal
  -- First compare at reducible transparency. Then compare only the remaining conjuncts at default transparency.
  let mut same : Std.HashMap Expr Expr := {}
  let mut free := hParts.filter (!qParts.contains ·)
  for useDefault in [false, true] do
    for q in qParts do
      unless hParts.contains q || same.contains q do
        for i in [:free.size] do
          let p := free[i]!
          if ← (if useDefault then isDefEq p q else withReducible (isDefEq p q)) then
            same := same.insert q p
            free := free.eraseIdx! i
            break
  let goal' := goal.replace fun e => same[e]?
  replaceMainGoal [← (← getMainGoal).replaceTargetDefEq goal']
  evalTactic (← `(tactic| exact Eq.mp (congrFun (by ac_rfl) _) $h))
