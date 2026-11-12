import E2eScal.G5CStmt
import E2eScal.Gen5SaDec
import E2eScal.Gen5VbDec
import E2eScal.Gen5VeDec

/-!
# Identity of three generated accept theorems with independent hand statements (unit G5-C)

The hand statements `E2eScal.G5C.{sa,vb,ve}_accept_stmt` (`G5CStmt.lean`) were committed before this session
opened the generated modules. Each line below type-checks only if the type of the generated accept theorem
(`p2dec --gen5`, unit G5-G; statement = kind instance `decAcceptKindN`) is definitionally the hand statement.
Neither side is edited for this check.
-/

open Fk
variable [Host]

namespace E2eScal.G5C

/-- The generated accept theorem of SyncAggregatorSelectionData proves the independent hand statement. -/
theorem sa_accept_hand : sa_accept_stmt := E2eScal.Gen.sa_g5dec_accept
/-- Type equality form (`rfl`). -/
theorem sa_accept_same : ∀ (h : Host), type_of% (@E2eScal.Gen.sa_g5dec_accept h) = @sa_accept_stmt h :=
  fun _ => rfl

/-- The generated accept theorem of ValidatorBalance proves the independent hand statement. -/
theorem vb_accept_hand : vb_accept_stmt := E2eScal.Gen.vb_g5dec_accept
/-- Type equality form (`rfl`). -/
theorem vb_accept_same : ∀ (h : Host), type_of% (@E2eScal.Gen.vb_g5dec_accept h) = @vb_accept_stmt h :=
  fun _ => rfl

/-- The generated accept theorem of VoluntaryExit proves the independent hand statement. -/
theorem ve_accept_hand : ve_accept_stmt := E2eScal.Gen.ve_g5dec_accept
/-- Type equality form (`rfl`). -/
theorem ve_accept_same : ∀ (h : Host), type_of% (@E2eScal.Gen.ve_g5dec_accept h) = @ve_accept_stmt h :=
  fun _ => rfl

end E2eScal.G5C
