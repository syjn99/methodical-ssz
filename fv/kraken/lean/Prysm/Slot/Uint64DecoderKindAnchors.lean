import Codec.Kind.FieldPatterns
import Prysm.Slot.DecodeAccept
import Prysm.CommitteeIndex.Uint64DecoderKindAnchors

/-!
# Anchors of the uint64 decoder statement kind

The uint64 decoder kind `Codec.u64DecAcceptKind C` is, for `C = Code.unmarshalSSZ` and `C = Prysm.CommitteeIndex.Code.unmarshalSSZ`, the full declared
type of the reviewed hand theorem (binders before the colon included). So the frozen kind is the hand
statement kind, not new text. P2 decode has no hand theorem of the segment shape; its kind is tied to the
lemma by `Codec.rootDecSegKind_of` only.
After the split of this module, the declarations of the other types are in `Prysm/CommitteeIndex/Uint64DecoderKindAnchors.lean`.
-/

open Machine Runtime Prysm.AttestationData.Code

open Codec
namespace Prysm.Slot

theorem Decode.accept_kind_anchor : ∀ (h : Host), type_of% (@Prysm.Slot.Decode.accept h)
    = @u64DecAcceptKind h Code.unmarshalSSZ := by
  intro h; with_reducible rfl

end Prysm.Slot
