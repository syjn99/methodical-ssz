import Codec.CalleeDecode

/-!
# `Uint64CalleeAccept` is the existing function-specification form: the `ValidatorIndex` part

The declarations of the other types of this group are in `Prysm/Slot/CalleeDecodeFunctionSpecs.lean`.
-/

open Machine Runtime

open Codec
namespace Prysm.ValidatorIndex

theorem Decode.accept_function_spec_is_callee_accept : ∀ (h : Host), @Prysm.ValidatorIndex.Decode.accept_function_spec h = @Uint64CalleeAccept h Prysm.ValidatorIndex.Code.unmarshalLabel := by
  intro h; rfl

end Prysm.ValidatorIndex
