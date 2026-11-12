import E2eScal.SmAcceptG4
import E2eScal.PcAcceptG4
import E2eScal.SmAccept

/-!
# Executed dependency check of the two re-derived accept theorems (SyncCommitteeMessage, PendingConsolidation)

A program (not a proof) walks the constants that the proof terms of `H5.sm_e2e_accept_g4` and
`H5.pc_e2e_accept_g4` reach inside the project namespaces (`E2eScal`, `E2e`, `E2eAd`, `Fk`) and fails the build
if one of the hold-out hand lemmas `bytes32dec_seg_rax`, `sm_vi_arg`, `calldec_nop_seg` is among them.
Controls: the same walk from the hold-out theorems `sm_e2e_accept_main` / `pc_e2e_accept_main` must reach them.
Executable evidence only.
-/

open Lean Elab Command

namespace E2eScal.G4DepCheck

/-- The project constants reached from `root` through types and values. -/
def reach (env : Environment) (root : Name) : Array Name := Id.run do
  let mut seen : Array Name := #[]
  let mut seenSet : NameSet := {}
  let mut todo : Array Name := #[root]
  let mut fuel := 2000000
  while todo.size > 0 && fuel > 0 do
    fuel := fuel - 1
    let n := todo[todo.size - 1]!
    todo := todo.pop
    if seenSet.contains n then continue
    seenSet := seenSet.insert n
    seen := seen.push n
    match env.find? n with
    | none => pure ()
    | some ci =>
      let val : Option Expr := match ci with
        | .thmInfo v => some v.value
        | .defnInfo v => some v.value
        | .opaqueInfo v => some v.value
        | _ => none
      let cs := ci.type.getUsedConstants ++ (match val with | some v => v.getUsedConstants | none => #[])
      for c in cs do
        if ((`E2eScal).isPrefixOf c || (`E2e).isPrefixOf c || (`E2eAd).isPrefixOf c || (`Fk).isPrefixOf c)
            && !seenSet.contains c then
          todo := todo.push c
  return seen

def banned : List Name :=
  [`E2eScal.H5.bytes32dec_seg_rax, `E2eScal.H5.sm_vi_arg, `E2eScal.H5.calldec_nop_seg]

elab "#g4_dep_check" : command => do
  let env ← getEnv
  for b in banned do
    unless env.contains b do throwError "g4 dependency check: {b} is not in the environment (wrong name)"
  for root in [`E2eScal.H5.sm_e2e_accept_g4, `E2eScal.H5.pc_e2e_accept_g4] do
    unless env.contains root do throwError "g4 dependency check: {root} is not in the environment"
    let r := reach env root
    for b in banned do
      if r.contains b then throwError "g4 dependency check FAILED: {root} reaches {b}"
    logInfo m!"g4 dependency check PASS: {root} reaches {r.size} project constants, none of {banned}"
  -- controls: the hold-out proofs must reach the hand lemmas (the walk can fail)
  let r1 := reach env `E2eScal.H5.sm_e2e_accept_main
  unless r1.contains `E2eScal.H5.bytes32dec_seg_rax && r1.contains `E2eScal.H5.sm_vi_arg do
    throwError "g4 dependency check: control failed (sm_e2e_accept_main does not reach the hand lemmas)"
  let r2 := reach env `E2eScal.H5.pc_e2e_accept_main
  unless r2.contains `E2eScal.H5.calldec_nop_seg do
    throwError "g4 dependency check: control failed (pc_e2e_accept_main does not reach calldec_nop_seg)"
  logInfo m!"g4 dependency check controls PASS: sm_e2e_accept_main reaches bytes32dec_seg_rax and sm_vi_arg ({r1.size} constants); pc_e2e_accept_main reaches calldec_nop_seg ({r2.size} constants)"

#g4_dep_check

end E2eScal.G4DepCheck
