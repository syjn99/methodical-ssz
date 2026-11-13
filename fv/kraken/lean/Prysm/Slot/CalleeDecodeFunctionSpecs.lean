import Codec.CalleeDecode
import Prysm.CommitteeIndex.CalleeDecodeFunctionSpecs
import Prysm.Epoch.CalleeDecodeFunctionSpecs
import Prysm.ValidatorIndex.CalleeDecodeFunctionSpecs

/-!
# `U64CalleeAcc` is the existing function-specification form

The four existing accept specifications of the `uint64`-overlay decoders are `U64CalleeAcc` at their label,
by `rfl` (the definitions unfold to the same text). So `calldec_seg` takes its callee hypothesis in the
existing form; the proved theorems `sl_uacc_holds`, `ci_uacc_holds`, `Prysm.ValidatorIndex.Decode.accept_function_spec_holds`, `ep_uacc_holds` give it.
After the split of this module, the declarations of the other types are in `Prysm/CommitteeIndex/CalleeDecodeFunctionSpecs.lean`, `Prysm/Epoch/CalleeDecodeFunctionSpecs.lean`, `Prysm/ValidatorIndex/CalleeDecodeFunctionSpecs.lean`.
-/

open Machine Runtime

open Codec
namespace Prysm.Slot

theorem Decode.accept_function_spec_is_callee_accept : ∀ (h : Host), @Prysm.Slot.Decode.accept_function_spec h = @U64CalleeAcc h Prysm.AttestationData.Code.slotUnmarshalLabel := by
  intro h; rfl

end Prysm.Slot
