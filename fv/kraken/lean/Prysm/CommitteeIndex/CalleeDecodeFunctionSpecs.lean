import Codec.CalleeDecode

/-!
# `U64CalleeAcc` is the existing function-specification form: the `CommitteeIndex` part

The declarations of the other types of this group are in `Prysm/Slot/CalleeDecodeFunctionSpecs.lean`.
-/

open Machine Runtime

open Codec
namespace Prysm.CommitteeIndex

theorem Decode.accept_function_spec_is_callee_accept : ∀ (h : Host), @Prysm.CommitteeIndex.Decode.accept_function_spec h = @U64CalleeAcc h Prysm.AttestationData.Code.committeeIndexUnmarshalLabel := by
  intro h; rfl

end Prysm.CommitteeIndex
