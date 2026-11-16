import Prysm.PowBlock.EncodeFastPathStatements
import Prysm.PowBlock.GeneratedEncodeFastPath
import Prysm.SyncCommitteeMessage.GeneratedEncodeFastPath
import Prysm.PendingPartialWithdrawal.GeneratedEncodeFastPath
import Prysm.Deposit_Data.GeneratedEncodeFastPath
import Prysm.Deposit_Data.GeneratedEncodeFastPathSameAsHand
import Prysm.SyncCommitteeMessage.GeneratedEncodeFastPathSameAsHand

/-!
# Identities of the generated encoder fast-path theorems with the independent hand statements

The hand statements of `Prysm/PowBlock/EncodeFastPathStatements.lean` do not refer to the generated theorems.
Each identity is `rfl` at default transparency. Encoder fast path only.
-/

open Machine Runtime Codec

namespace Prysm.PowBlock

set_option maxHeartbeats 4000000 in
theorem Encode.generated_fast_same_as_statement : ∀ (h : Host), type_of% (@Prysm.PowBlock.Encode.generated_fast h) = @Encode.fast_path_statement h := by
  intro h; rfl

end Prysm.PowBlock
