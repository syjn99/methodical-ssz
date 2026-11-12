import E2eScal.CallDec

/-!
# `U64CalleeAcc` is the existing function-specification form

The four existing accept specifications of the `uint64`-overlay decoders are `U64CalleeAcc` at their label,
by `rfl` (the definitions unfold to the same text). So `calldec_seg` takes its callee hypothesis in the
existing form; the proved theorems `sl_uacc_holds`, `ci_uacc_holds`, `vi_uacc_holds`, `ep_uacc_holds` give it.
-/

open Machine Runtime TestTarget

open Codec
namespace E2eScal

theorem slUAccC_eq : ∀ (h : Host), @Prysm.Slot.Decode.accept_function_spec h = @U64CalleeAcc h Prysm.AttestationData.Code.slotUnmarshalLabel := by
  intro h; rfl

theorem ciUAccC_eq : ∀ (h : Host), @Prysm.CommitteeIndex.Decode.accept_function_spec h = @U64CalleeAcc h Prysm.AttestationData.Code.committeeIndexUnmarshalLabel := by
  intro h; rfl

theorem viUAccC_eq : ∀ (h : Host), @E2eScal.ViUAccC h = @U64CalleeAcc h E2eScal.BhCode.viLabel := by
  intro h; rfl

theorem epUAccC_eq : ∀ (h : Host), @Prysm.Epoch.Decode.accept_function_spec h = @U64CalleeAcc h Prysm.Epoch.Code.unmarshalSSZLabel := by
  intro h; rfl

end E2eScal
