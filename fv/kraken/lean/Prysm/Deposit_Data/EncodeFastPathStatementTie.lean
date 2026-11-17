import Prysm.Deposit_Data.EncodeFastPathStatements
import Prysm.Deposit_Data.GeneratedEncodeFastPath

/-!
# Tie of the generated encoder fast-path theorem of `Deposit_Data` to the hand statement

This theorem shows that the generated theorem `Prysm.Deposit_Data.Encode.generated_fast` has the hand statement `Prysm.Deposit_Data.Encode.fast_path_statement`.
The hand statement of `Prysm/Deposit_Data/EncodeFastPathStatements.lean` does not refer to the generated theorem.
The identity is `rfl` at default transparency.
-/

open Machine Runtime Codec

namespace Prysm.Deposit_Data

set_option maxHeartbeats 4000000 in
theorem Encode.fast_path_statement_tie : ∀ (h : Host), type_of% (@Prysm.Deposit_Data.Encode.generated_fast h) = @Prysm.Deposit_Data.Encode.fast_path_statement h := by
  intro h; rfl

end Prysm.Deposit_Data
