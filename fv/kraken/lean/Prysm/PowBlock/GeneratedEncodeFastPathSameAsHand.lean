import Prysm.PowBlock.EncodeFastPathStatements
import Prysm.PowBlock.GeneratedEncodeFastPath
import Prysm.SyncCommitteeMessage.GeneratedEncodeFastPath
import Prysm.PendingPartialWithdrawal.GeneratedEncodeFastPath
import Prysm.Deposit_Data.GeneratedEncodeFastPath
import Prysm.Deposit_Data.GeneratedEncodeFastPathSameAsHand
import Prysm.PendingPartialWithdrawal.GeneratedEncodeFastPathSameAsHand
import Prysm.SyncCommitteeMessage.GeneratedEncodeFastPathSameAsHand

/-!
# Identities of the generated encoder fast-path theorems with the independent hand statements

`Prysm/PowBlock/EncodeFastPathStatements.lean` was committed before the generated theorems were read. Each identity is `rfl` at default
transparency; a failed identity is recorded, not forced. Encoder fast path only.
After the split of this module, the declarations of the other types are in `Prysm/Deposit_Data/GeneratedEncodeFastPathSameAsHand.lean`, `Prysm/PendingPartialWithdrawal/GeneratedEncodeFastPathSameAsHand.lean`, `Prysm/SyncCommitteeMessage/GeneratedEncodeFastPathSameAsHand.lean`.
-/

open Machine Runtime Codec

namespace Prysm.PowBlock

set_option maxHeartbeats 4000000 in
theorem Encode.generated_fast_same_as_statement : ∀ (h : Host), type_of% (@Prysm.PowBlock.Encode.generated_fast h) = @Encode.fast_path_statement h := by
  intro h; rfl

end Prysm.PowBlock
