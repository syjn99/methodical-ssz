import Prysm.SyncAggregatorSelectionData.Statements
import Prysm.SyncAggregatorSelectionData.GeneratedDecodeAccept
import Prysm.ValidatorBalance.GeneratedDecodeAccept
import Prysm.VoluntaryExit.GeneratedDecodeAccept

/-!
# Identity of three generated accept theorems with independent hand statements: the `ValidatorBalance` part

The declarations of the other types of this group are in `Prysm/SyncAggregatorSelectionData/GeneratedDecodeAcceptSameAsHand.lean`.
-/

open Machine Runtime
variable [Host]

open Codec
namespace Prysm.ValidatorBalance

/-- The generated accept theorem of ValidatorBalance proves the independent hand statement. -/
theorem Decode.generated_accept_satisfies_statement : Prysm.ValidatorBalance.Decode.accept_statement := Prysm.ValidatorBalance.Decode.generated_accept
/-- Type equality form (`rfl`). -/
theorem Decode.generated_accept_same_as_statement : ∀ (h : Host), type_of% (@Prysm.ValidatorBalance.Decode.generated_accept h) = @Prysm.ValidatorBalance.Decode.accept_statement h :=
  fun _ => rfl

end Prysm.ValidatorBalance
