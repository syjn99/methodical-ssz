import Fk
import Fv.Spec
import Fv1.SpecScalars
import Fv1.SpecList
import Fv1.SpecFixedVec
import Fv1.SpecBitVec
import Fv1.SpecNested
import Fv1.SpecListC
import Fv1.SpecPrysm
import Fv1.SpecBitList
import Fv1.Transfer

/-!
Every declaration (theorem, definition, instance, internal auxiliary
declaration) of a module under `Fk`, `Fv1` or `Fv`, with the axioms it
depends on. The theorem scope (`tools/Axioms.lean`) lists non-internal
theorems only; this file is the all-declarations scope (re-proof R10, astra
1b-fix 7). It prints the declarations with a nonstandard axiom and the totals.
-/

open Lean Elab Command in
#eval show CommandElabM Unit from do
  let env ← getEnv
  let std : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut out : Array String := #[]
  let mut bad := 0
  for (n, ci) in env.constants.toList do
    let some idx := env.getModuleIdxFor? n | continue
    let mod := env.header.moduleNames[idx.toNat]!
    let top := mod.getRoot
    unless top == `Fk || top == `Fv1 || top == `Fv do continue
    let _ := ci
    let axs ← liftCoreM (Lean.collectAxioms n)
    if axs.any (fun a => !std.contains a) then
      bad := bad + 1
      IO.println s!"NONSTANDARD {mod}\t{n}\t{axs.toList}"
    out := out.push s!"{n}"
  IO.println s!"ALL-DECLARATIONS TOTAL {out.size} NONSTANDARD {bad}"
