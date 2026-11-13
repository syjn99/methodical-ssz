import Prysm.SyncCommitteeMessage.DecodeAcceptFromWindowSteps
import Prysm.PendingConsolidation.DecodeAcceptFromWindowSteps
import Prysm.SyncCommitteeMessage.DecodeAccept

/-!
# Executed dependency check of the two re-derived accept theorems (SyncCommitteeMessage, PendingConsolidation)

A program (not a proof) walks the constants that the proof terms of `Decode.accept_from_window_steps` and
`Prysm.PendingConsolidation.Decode.accept_from_window_steps` reach inside the project namespaces (`Prysm`, `Codec`, `ElfData`, `Machine`, `Runtime`) and fails the build
if one of the hold-out hand lemmas `Prysm.SyncCommitteeMessage.bytes32dec_seg_rax`,
`Prysm.SyncCommitteeMessage.Decode.validator_index_arg`, `Prysm.PendingConsolidation.calldec_nop_seg` is among them.
Controls: the same walk from the hold-out theorems `Prysm.SyncCommitteeMessage.Decode.accept` /
`Prysm.PendingConsolidation.Decode.accept` must reach them.
Executable evidence only.
-/

open Lean Elab Command

open Codec
namespace Prysm.SyncCommitteeMessage.DependencyCheck

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
        if ((`Prysm).isPrefixOf c || (`Codec).isPrefixOf c || (`ElfData).isPrefixOf c || (`Machine).isPrefixOf c || (`Runtime).isPrefixOf c)
            && !seenSet.contains c then
          todo := todo.push c
  return seen

def banned : List Name :=
  [`Prysm.SyncCommitteeMessage.bytes32dec_seg_rax, `Prysm.SyncCommitteeMessage.Decode.validator_index_arg, `Prysm.PendingConsolidation.calldec_nop_seg]

elab "#check_window_step_dependencies" : command => do
  let env ← getEnv
  for b in banned do
    unless env.contains b do throwError "window step dependency check: {b} is not in the environment (wrong name)"
  for root in [`Prysm.SyncCommitteeMessage.Decode.accept_from_window_steps, `Prysm.PendingConsolidation.Decode.accept_from_window_steps] do
    unless env.contains root do throwError "window step dependency check: {root} is not in the environment"
    let r := reach env root
    for b in banned do
      if r.contains b then throwError "window step dependency check FAILED: {root} reaches {b}"
    logInfo m!"window step dependency check PASS: {root} reaches {r.size} project constants, none of {banned}"
  -- controls: the hold-out proofs must reach the hand lemmas (the walk can fail)
  let r1 := reach env `Prysm.SyncCommitteeMessage.Decode.accept
  unless r1.contains `Prysm.SyncCommitteeMessage.bytes32dec_seg_rax && r1.contains `Prysm.SyncCommitteeMessage.Decode.validator_index_arg do
    throwError "window step dependency check: control failed (Prysm.SyncCommitteeMessage.Decode.accept does not reach the hand lemmas)"
  let r2 := reach env `Prysm.PendingConsolidation.Decode.accept
  unless r2.contains `Prysm.PendingConsolidation.calldec_nop_seg do
    throwError "window step dependency check: control failed (Prysm.PendingConsolidation.Decode.accept does not reach Prysm.PendingConsolidation.calldec_nop_seg)"
  logInfo m!"window step dependency check controls PASS: Prysm.SyncCommitteeMessage.Decode.accept reaches Prysm.SyncCommitteeMessage.bytes32dec_seg_rax and Prysm.SyncCommitteeMessage.Decode.validator_index_arg ({r1.size} constants); Prysm.PendingConsolidation.Decode.accept reaches Prysm.PendingConsolidation.calldec_nop_seg ({r2.size} constants)"

#check_window_step_dependencies

end Prysm.SyncCommitteeMessage.DependencyCheck
