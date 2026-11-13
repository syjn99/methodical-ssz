import Prysm.PowBlock.EncodeFastPathStatements
import Prysm.PowBlock.GeneratedEncodeFastPath
import Prysm.SyncCommitteeMessage.GeneratedEncodeFastPath
import Prysm.PendingPartialWithdrawal.GeneratedEncodeFastPath
import Prysm.Deposit_Data.GeneratedEncodeFastPath

/-!
# Identities of the generated encoder fast-path theorems with the independent hand statements

`E2cStmt.lean` was committed before the generated theorems were read. Each identity is `rfl` at default
transparency; a failed identity is recorded, not forced. Encoder fast path only.
-/

open Machine Runtime TestTarget Codec

namespace Prysm.PowBlock

set_option maxHeartbeats 4000000 in
theorem Encode.generated_fast_same_as_statement : ∀ (h : Host), type_of% (@Prysm.PowBlock.Encode.generated_fast h) = @Encode.fast_path_statement h := by
  intro h; rfl

set_option maxHeartbeats 4000000 in
theorem _root_.Prysm.SyncCommitteeMessage.Encode.generated_fast_same_as_statement : ∀ (h : Host), type_of% (@Prysm.SyncCommitteeMessage.Encode.generated_fast h) = @Prysm.SyncCommitteeMessage.Encode.fast_path_statement h := by
  intro h; rfl

set_option maxHeartbeats 4000000 in
theorem _root_.Prysm.PendingPartialWithdrawal.Encode.generated_fast_same_as_statement : ∀ (h : Host), type_of% (@Prysm.PendingPartialWithdrawal.Encode.generated_fast h) = @Prysm.PendingPartialWithdrawal.Encode.fast_path_statement h := by
  intro h; rfl

set_option maxHeartbeats 4000000 in
theorem _root_.Prysm.Deposit_Data.Encode.generated_fast_same_as_statement : ∀ (h : Host), type_of% (@Prysm.Deposit_Data.Encode.generated_fast h) = @Prysm.Deposit_Data.Encode.fast_path_statement h := by
  intro h; rfl

end Prysm.PowBlock
