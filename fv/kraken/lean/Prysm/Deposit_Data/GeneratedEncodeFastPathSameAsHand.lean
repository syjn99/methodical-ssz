import Prysm.PowBlock.EncodeFastPathStatements
import Prysm.PowBlock.GeneratedEncodeFastPath
import Prysm.SyncCommitteeMessage.GeneratedEncodeFastPath
import Prysm.PendingPartialWithdrawal.GeneratedEncodeFastPath
import Prysm.Deposit_Data.GeneratedEncodeFastPath

/-!
# Identity of the generated encoder fast-path theorem of `Deposit_Data` with the hand statement

This theorem shows that the generated theorem `Prysm.Deposit_Data.Encode.generated_fast` has the hand statement `Prysm.Deposit_Data.Encode.fast_path_statement`.
The hand statement of `Prysm/Deposit_Data/EncodeFastPathStatements.lean` does not refer to the generated theorem.
The identity is `rfl` at default transparency.
-/

open Machine Runtime Codec

namespace Prysm.Deposit_Data

set_option maxHeartbeats 4000000 in
theorem Encode.generated_fast_same_as_statement : ∀ (h : Host), type_of% (@Prysm.Deposit_Data.Encode.generated_fast h) = @Prysm.Deposit_Data.Encode.fast_path_statement h := by
  intro h; rfl

end Prysm.Deposit_Data
