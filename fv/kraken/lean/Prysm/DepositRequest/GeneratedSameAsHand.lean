import Prysm.DepositRequest.Statements
import Prysm.DepositRequest.GeneratedDecodeAccept
import Prysm.BeaconBlocksByRangeRequest.GeneratedDecodeAccept
import Prysm.PartialDataColumnGroupID.GeneratedDecodeAccept
import Prysm.ValidatorIdentity.GeneratedDecodeAccept
import Prysm.BuilderPreferences.GeneratedEncodeFastPath
import Prysm.BeaconBlocksByRangeRequest.GeneratedEncodeFastPath
import Prysm.PartialDataColumnGroupID.GeneratedEncodeFastPath
import Prysm.ValidatorIdentity.GeneratedEncodeFastPath
import Prysm.BeaconBlocksByRangeRequest.GeneratedSameAsHand
import Prysm.BuilderPreferences.GeneratedSameAsHand
import Prysm.PartialDataColumnGroupID.GeneratedSameAsHand
import Prysm.ValidatorIdentity.GeneratedSameAsHand

/-!
# Identity of four generated decoder accept theorems and four generated encoder fast-path theorems
with the independent hand statements of `Prysm/DepositRequest/Statements.lean`

`Prysm/DepositRequest/Statements.lean` was committed before its author opened the generated modules imported here. Each line type-checks
only if the type of the generated theorem (`decoder --whole-accept` / `encoder --fast-path`, raw output of the one-shot runs on the 24 flat types) is
definitionally the hand statement. Neither side is edited for this check. `maxHeartbeats 4000000` = the value of the
model identity files (`Prysm/PowBlock/GeneratedEncodeFastPathSameAsHand.lean`).
After the split of this module, the declarations of the other types are in `Prysm/BeaconBlocksByRangeRequest/GeneratedSameAsHand.lean`, `Prysm/BuilderPreferences/GeneratedSameAsHand.lean`, `Prysm/PartialDataColumnGroupID/GeneratedSameAsHand.lean`, `Prysm/ValidatorIdentity/GeneratedSameAsHand.lean`.
-/

open Machine Runtime
variable [Host]

open Codec
namespace Prysm.DepositRequest

set_option maxHeartbeats 4000000 in
theorem Decode.generated_accept_same_as_statement : ∀ (h : Host), type_of% (@Prysm.DepositRequest.Decode.generated_accept h) = @Decode.accept_statement h := by
  intro h; rfl

/-- The generated accept theorem proves the independent hand statement. -/
theorem Decode.generated_accept_satisfies_statement : Decode.accept_statement := Prysm.DepositRequest.Decode.generated_accept

end Prysm.DepositRequest
