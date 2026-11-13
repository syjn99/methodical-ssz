import Codec.Kind.DecodeAcceptComposition
import Prysm.BlobIdentifier.GeneratedDecodeAcceptComposition
import Prysm.DepositMessage.GeneratedDecodeAcceptComposition
import Prysm.Eth1Data.GeneratedDecodeAcceptComposition
import Prysm.DepositMessage.GeneratedDecodeAcceptCompositionKind
import Prysm.Eth1Data.GeneratedDecodeAcceptCompositionKind

/-!
# The three generated composed accept theorems have the kind `decAcceptKind`

The declared type of each in-sample generated composed theorem (`Prysm/BlobIdentifier/GeneratedDecodeAcceptComposition.lean`, `Prysm/DepositMessage/GeneratedDecodeAcceptComposition.lean`,
`Prysm/Eth1Data/GeneratedDecodeAcceptComposition.lean`; generator output, unchanged) is `decAcceptKind` at the parameters of its type, by `rfl`
at default transparency. This is the `_kind` line a generated composed theorem of this shape can carry
instead of the identity with a hand theorem.
After the split of this module, the declarations of the other types are in `Prysm/DepositMessage/GeneratedDecodeAcceptCompositionKind.lean`, `Prysm/Eth1Data/GeneratedDecodeAcceptCompositionKind.lean`.
-/

open Machine Runtime

open Codec
namespace Prysm.BlobIdentifier

theorem Decode.accept_generated_composition_is_kind : ∀ (h : Host), type_of% (@Prysm.BlobIdentifier.Decode.accept_generated_composition h)
    = @decAcceptKind h Prysm.BlobIdentifier.Code.unmarshalSSZ true [.bytes 32, .u64] 32 := by
  intro h; rfl

end Prysm.BlobIdentifier
