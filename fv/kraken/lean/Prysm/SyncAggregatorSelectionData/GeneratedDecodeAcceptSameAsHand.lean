import Prysm.SyncAggregatorSelectionData.Statements
import Prysm.SyncAggregatorSelectionData.GeneratedDecodeAccept
import Prysm.ValidatorBalance.GeneratedDecodeAccept
import Prysm.VoluntaryExit.GeneratedDecodeAccept
import Prysm.ValidatorBalance.GeneratedDecodeAcceptSameAsHand
import Prysm.VoluntaryExit.GeneratedDecodeAcceptSameAsHand

/-!
# Identity of three generated accept theorems with independent hand statements

The hand statements `Decode.accept_statement` of SyncAggregatorSelectionData, ValidatorBalance and VoluntaryExit (`Prysm/SyncAggregatorSelectionData/Statements.lean`) were committed before the
generated modules were written. Each line below type-checks only if the type of the generated accept theorem
(`decoder --whole-accept`; statement = kind instance `decodeAcceptKindAnyFrame`) is definitionally the hand statement.
Neither side is edited for this check.
After the split of this module, the declarations of the other types are in `Prysm/ValidatorBalance/GeneratedDecodeAcceptSameAsHand.lean`, `Prysm/VoluntaryExit/GeneratedDecodeAcceptSameAsHand.lean`.
-/

open Machine Runtime
variable [Host]

open Codec
namespace Prysm.SyncAggregatorSelectionData

/-- The generated accept theorem of SyncAggregatorSelectionData proves the independent hand statement. -/
theorem Decode.generated_accept_satisfies_statement : Decode.accept_statement := Prysm.SyncAggregatorSelectionData.Decode.generated_accept
/-- Type equality form (`rfl`). -/
theorem Decode.generated_accept_same_as_statement : ∀ (h : Host), type_of% (@Prysm.SyncAggregatorSelectionData.Decode.generated_accept h) = @Decode.accept_statement h :=
  fun _ => rfl

end Prysm.SyncAggregatorSelectionData
