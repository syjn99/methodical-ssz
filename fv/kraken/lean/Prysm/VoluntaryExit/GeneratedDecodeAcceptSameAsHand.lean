import Prysm.SyncAggregatorSelectionData.Statements
import Prysm.SyncAggregatorSelectionData.GeneratedDecodeAccept
import Prysm.ValidatorBalance.GeneratedDecodeAccept
import Prysm.VoluntaryExit.GeneratedDecodeAccept

/-!
# Identity of three generated accept theorems with independent hand statements: the `VoluntaryExit` part

The declarations of the other types of this group are in `Prysm/SyncAggregatorSelectionData/GeneratedDecodeAcceptSameAsHand.lean`.
-/

open Machine Runtime
variable [Host]

open Codec
namespace Prysm.VoluntaryExit

/-- The generated accept theorem of VoluntaryExit proves the independent hand statement. -/
theorem Decode.generated_accept_satisfies_statement : Prysm.VoluntaryExit.Decode.accept_statement := Prysm.VoluntaryExit.Decode.generated_accept
/-- Type equality form (`rfl`). -/
theorem Decode.generated_accept_same_as_statement : ∀ (h : Host), type_of% (@Prysm.VoluntaryExit.Decode.generated_accept h) = @Prysm.VoluntaryExit.Decode.accept_statement h :=
  fun _ => rfl

end Prysm.VoluntaryExit
