import Prysm.DepositRequest.Statements
import Prysm.DepositRequest.GeneratedDecodeAccept
import Prysm.BeaconBlocksByRangeRequest.GeneratedDecodeAccept
import Prysm.PartialDataColumnGroupID.GeneratedDecodeAccept
import Prysm.ValidatorIdentity.GeneratedDecodeAccept
import Prysm.BuilderPreferences.GeneratedEncodeFastPath
import Prysm.BeaconBlocksByRangeRequest.GeneratedEncodeFastPath
import Prysm.PartialDataColumnGroupID.GeneratedEncodeFastPath
import Prysm.ValidatorIdentity.GeneratedEncodeFastPath

/-!
# Identity of four generated decoder accept theorems and four generated encoder fast-path theorems: the `BeaconBlocksByRangeRequest` part

The declarations of the other types of this group are in `Prysm/DepositRequest/GeneratedSameAsHand.lean`.
-/

open Machine Runtime
variable [Host]

open Codec
namespace Prysm.BeaconBlocksByRangeRequest

set_option maxHeartbeats 4000000 in
theorem Decode.generated_accept_same_as_statement : ∀ (h : Host), type_of% (@Prysm.BeaconBlocksByRangeRequest.Decode.generated_accept h) = @Prysm.BeaconBlocksByRangeRequest.Decode.accept_statement h := by
  intro h; rfl

/-- The generated accept theorem proves the independent hand statement. -/
theorem Decode.generated_accept_satisfies_statement : Prysm.BeaconBlocksByRangeRequest.Decode.accept_statement := Prysm.BeaconBlocksByRangeRequest.Decode.generated_accept

set_option maxHeartbeats 4000000 in
theorem Encode.generated_fast_same_as_statement : ∀ (h : Host), type_of% (@Prysm.BeaconBlocksByRangeRequest.Encode.generated_fast h) = @Prysm.BeaconBlocksByRangeRequest.Encode.fast_path_statement h := by
  intro h; rfl

end Prysm.BeaconBlocksByRangeRequest
