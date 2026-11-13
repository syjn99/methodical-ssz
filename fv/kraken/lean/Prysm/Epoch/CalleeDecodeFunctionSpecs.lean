import Codec.CalleeDecode

/-!
# `U64CalleeAcc` is the existing function-specification form: the `Epoch` part

The declarations of the other types of this group are in `Prysm/Slot/CalleeDecodeFunctionSpecs.lean`.
-/

open Machine Runtime

open Codec
namespace Prysm.Epoch

theorem Decode.accept_function_spec_is_callee_accept : ∀ (h : Host), @Prysm.Epoch.Decode.accept_function_spec h = @U64CalleeAcc h Prysm.Epoch.Code.unmarshalSSZLabel := by
  intro h; rfl

end Prysm.Epoch
