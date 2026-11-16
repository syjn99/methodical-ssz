import Codec.Kind.DecodeAcceptComposition
import Prysm.BlobIdentifier.GeneratedDecodeAcceptComposition

/-!
# The generated composed accept theorem has the kind `decodeAcceptKind`

The declared type of the in-sample generated composed theorem (`Prysm/BlobIdentifier/GeneratedDecodeAcceptComposition.lean`;
generator output, unchanged) is `decodeAcceptKind` at the parameters of its type, by `rfl`
at default transparency. This is the `_kind` line a generated composed theorem of this shape can carry
instead of the identity with a hand theorem.
-/

open Machine Runtime

open Codec
namespace Prysm.BlobIdentifier

theorem Decode.accept_generated_composition_is_kind : ∀ (h : Host), type_of% (@Prysm.BlobIdentifier.Decode.accept_generated_composition h)
    = @decodeAcceptKind h Prysm.BlobIdentifier.Code.unmarshalSSZ true [.bytes 32, .uint64] 32 := by
  intro h; rfl

end Prysm.BlobIdentifier
