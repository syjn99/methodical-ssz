import Prysm.SyncAggregatorSelectionData.Statements
import Prysm.SyncAggregatorSelectionData.GeneratedDecodeAccept
import Prysm.ValidatorBalance.GeneratedDecodeAccept
import Prysm.VoluntaryExit.GeneratedDecodeAccept

/-!
# Identity of three generated accept theorems with independent hand statements

The hand statements `E2eScal.G5C.{sa,vb,ve}_accept_stmt` (`G5CStmt.lean`) were committed before this session
opened the generated modules. Each line below type-checks only if the type of the generated accept theorem
(`p2dec --gen5`; statement = kind instance `decAcceptKindN`) is definitionally the hand statement.
Neither side is edited for this check.
-/

open Machine Runtime TestTarget
variable [Host]

open Codec
namespace Prysm.SyncAggregatorSelectionData

/-- The generated accept theorem of SyncAggregatorSelectionData proves the independent hand statement. -/
theorem Decode.generated_accept_satisfies_statement : Decode.accept_statement := Prysm.SyncAggregatorSelectionData.Decode.generated_accept
/-- Type equality form (`rfl`). -/
theorem Decode.generated_accept_same_as_statement : ∀ (h : Host), type_of% (@Prysm.SyncAggregatorSelectionData.Decode.generated_accept h) = @Decode.accept_statement h :=
  fun _ => rfl

/-- The generated accept theorem of ValidatorBalance proves the independent hand statement. -/
theorem _root_.Prysm.ValidatorBalance.Decode.generated_accept_satisfies_statement : Prysm.ValidatorBalance.Decode.accept_statement := Prysm.ValidatorBalance.Decode.generated_accept
/-- Type equality form (`rfl`). -/
theorem _root_.Prysm.ValidatorBalance.Decode.generated_accept_same_as_statement : ∀ (h : Host), type_of% (@Prysm.ValidatorBalance.Decode.generated_accept h) = @Prysm.ValidatorBalance.Decode.accept_statement h :=
  fun _ => rfl

/-- The generated accept theorem of VoluntaryExit proves the independent hand statement. -/
theorem _root_.Prysm.VoluntaryExit.Decode.generated_accept_satisfies_statement : Prysm.VoluntaryExit.Decode.accept_statement := Prysm.VoluntaryExit.Decode.generated_accept
/-- Type equality form (`rfl`). -/
theorem _root_.Prysm.VoluntaryExit.Decode.generated_accept_same_as_statement : ∀ (h : Host), type_of% (@Prysm.VoluntaryExit.Decode.generated_accept h) = @Prysm.VoluntaryExit.Decode.accept_statement h :=
  fun _ => rfl

end Prysm.SyncAggregatorSelectionData
