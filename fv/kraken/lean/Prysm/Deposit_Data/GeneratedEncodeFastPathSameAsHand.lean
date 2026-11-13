import Prysm.PowBlock.EncodeFastPathStatements
import Prysm.PowBlock.GeneratedEncodeFastPath
import Prysm.SyncCommitteeMessage.GeneratedEncodeFastPath
import Prysm.PendingPartialWithdrawal.GeneratedEncodeFastPath
import Prysm.Deposit_Data.GeneratedEncodeFastPath

/-!
# Identities of the generated encoder fast-path theorems with the independent hand statements: the `Deposit_Data` part

The declarations of the other types of this group are in `Prysm/PowBlock/GeneratedEncodeFastPathSameAsHand.lean`.
-/

open Machine Runtime Codec

namespace Prysm.Deposit_Data

set_option maxHeartbeats 4000000 in
theorem Encode.generated_fast_same_as_statement : ∀ (h : Host), type_of% (@Prysm.Deposit_Data.Encode.generated_fast h) = @Prysm.Deposit_Data.Encode.fast_path_statement h := by
  intro h; rfl

end Prysm.Deposit_Data
