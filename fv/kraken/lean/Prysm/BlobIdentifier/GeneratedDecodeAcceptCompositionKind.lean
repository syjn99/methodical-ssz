import Codec.Kind.DecodeAcceptComposition
import Prysm.BlobIdentifier.GeneratedDecodeAcceptComposition
import Prysm.DepositMessage.GeneratedDecodeAcceptComposition
import Prysm.Eth1Data.GeneratedDecodeAcceptComposition

/-!
# The three generated composed accept theorems have the kind `decAcceptKind`

The declared type of each in-sample generated composed theorem (`Gen2BiAccept.lean`, `Gen2DmAccept.lean`,
`Gen2E1Accept.lean`; generator output, unchanged) is `decAcceptKind` at the parameters of its type, by `rfl`
at default transparency. This is the `_kind` line a generated composed theorem of this shape can carry
instead of the identity with a hand theorem.
-/

open Machine Runtime TestTarget

open Codec
namespace Prysm.BlobIdentifier

theorem Decode.accept_generated_composition_is_kind : ∀ (h : Host), type_of% (@Prysm.BlobIdentifier.Decode.accept_generated_composition h)
    = @decAcceptKind h Prysm.BlobIdentifier.Code.unmarshalSSZ true [.bytes 32, .u64] 32 := by
  intro h; rfl

theorem _root_.Prysm.DepositMessage.Decode.accept_generated_composition_is_kind : ∀ (h : Host), type_of% (@Prysm.DepositMessage.Decode.accept_generated_composition h)
    = @decAcceptKind h Prysm.DepositMessage.Code.unmarshalSSZ false [.bytes 48, .bytes 32, .u64] 68 := by
  intro h; rfl

theorem _root_.Prysm.Eth1Data.Decode.accept_generated_composition_is_kind : ∀ (h : Host), type_of% (@Prysm.Eth1Data.Decode.accept_generated_composition h)
    = @decAcceptKind h Prysm.Eth1Data.Code.unmarshalSSZ true [.bytes 32, .u64, .bytes 32] 70 := by
  intro h; rfl

end Prysm.BlobIdentifier
