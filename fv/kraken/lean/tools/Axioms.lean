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
Every theorem declared in a module under `Fk`, `Fv1` or `Fv`, with the axioms
it depends on (astra style: `#print axioms` for each). Run by
`tools/axioms.sh`, which writes `../AXIOMS.txt` and fails when a theorem uses
an axiom other than `propext`, `Classical.choice`, `Quot.sound`.
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
    unless ci matches .thmInfo _ do continue
    if n.isInternalDetail then continue
    let axs ← liftCoreM (Lean.collectAxioms n)
    let axs := axs.qsort (·.toString < ·.toString)
    if axs.any (fun a => !std.contains a) then bad := bad + 1
    out := out.push s!"{mod}\t{n}\t{axs.toList}"
  out := out.qsort (· < ·)
  for l in out do IO.println l
  IO.println s!"TOTAL {out.size} NONSTANDARD {bad}"
