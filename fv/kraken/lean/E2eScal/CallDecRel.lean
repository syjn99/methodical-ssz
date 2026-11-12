import E2eScal.CallDec

/-!
# `U64CalleeAcc` is the existing function-specification form

The four existing accept specifications of the `uint64`-overlay decoders are `U64CalleeAcc` at their label,
by `rfl` (the definitions unfold to the same text). So `calldec_seg` takes its callee hypothesis in the
existing form; the proved theorems `sl_uacc_holds`, `ci_uacc_holds`, `vi_uacc_holds`, `ep_uacc_holds` give it.
-/

open Fk

namespace E2eScal

theorem slUAccC_eq : ∀ (h : Host), @E2eAd.SlUAccC h = @U64CalleeAcc h E2eAd.Code.slLabel := by
  intro h; rfl

theorem ciUAccC_eq : ∀ (h : Host), @E2eAd.CiUAccC h = @U64CalleeAcc h E2eAd.Code.ciLabel := by
  intro h; rfl

theorem viUAccC_eq : ∀ (h : Host), @E2eScal.ViUAccC h = @U64CalleeAcc h E2eScal.BhCode.viLabel := by
  intro h; rfl

theorem epUAccC_eq : ∀ (h : Host), @E2e.EpUAccC h = @U64CalleeAcc h E2e.Code.epLabel := by
  intro h; rfl

end E2eScal
