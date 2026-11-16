import Prysm.PowBlock.EncodeFastPathStatements
import Prysm.PowBlock.GeneratedEncodeFastPath
import Prysm.SyncCommitteeMessage.GeneratedEncodeFastPath
import Prysm.PendingPartialWithdrawal.GeneratedEncodeFastPath
import Prysm.Deposit_Data.GeneratedEncodeFastPath
import Prysm.Deposit_Data.GeneratedEncodeFastPathSameAsHand
import Prysm.SyncCommitteeMessage.GeneratedEncodeFastPathSameAsHand

/-!
# Identity of the generated encoder fast-path theorem of `PowBlock` with the hand statement

This theorem shows that the generated theorem `Prysm.PowBlock.Encode.generated_fast` has the hand statement `Prysm.PowBlock.Encode.fast_path_statement`.
The hand statement of `Prysm/PowBlock/EncodeFastPathStatements.lean` does not refer to the generated theorem.
The identity is `rfl` at default transparency.
-/

open Machine Runtime Codec

namespace Prysm.PowBlock

set_option maxHeartbeats 4000000 in
theorem Encode.generated_fast_same_as_statement : ∀ (h : Host), type_of% (@Prysm.PowBlock.Encode.generated_fast h) = @Encode.fast_path_statement h := by
  intro h; rfl

end Prysm.PowBlock
