import Prysm.SyncCommitteeMessage.EncodeFastPathStatements
import Prysm.SyncCommitteeMessage.GeneratedEncodeFastPath

/-!
# Tie of the generated encoder fast-path theorem of `SyncCommitteeMessage` to the hand statement

This theorem shows that the generated theorem `Prysm.SyncCommitteeMessage.Encode.generated_fast` has the hand statement `Prysm.SyncCommitteeMessage.Encode.fast_path_statement`.
The hand statement of `Prysm/SyncCommitteeMessage/EncodeFastPathStatements.lean` does not refer to the generated theorem.
The identity is `rfl` at default transparency.
-/

open Machine Runtime Codec

namespace Prysm.SyncCommitteeMessage

set_option maxHeartbeats 4000000 in
theorem Encode.fast_path_statement_tie : ∀ (h : Host), type_of% (@Prysm.SyncCommitteeMessage.Encode.generated_fast h) = @Prysm.SyncCommitteeMessage.Encode.fast_path_statement h := by
  intro h; rfl

end Prysm.SyncCommitteeMessage
