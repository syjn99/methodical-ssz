import Codec.Kind.FieldPatterns
import Prysm.Slot.DecodeAccept

/-!
# Anchors of the P1 statement kind (review fix-r1 S1)

The P1 kind `Codec.u64DecAcceptKind C` is, for `C = slotUnmarshalSSZ` and `C = committeeIndexUnmarshalSSZ`, the full declared
type of the reviewed hand theorem (binders before the colon included). So the frozen kind is the hand
statement kind, not new text. P2 decode has no hand theorem of the segment shape; its kind is tied to the
lemma by `Codec.rootDecSegKind_of` only.
-/

open Machine Runtime TestTarget Prysm.AttestationData.Code

open Codec
namespace Prysm.Slot

theorem Decode.accept_kind_anchor : ∀ (h : Host), type_of% (@Prysm.Slot.Decode.accept h)
    = @u64DecAcceptKind h slotUnmarshalSSZ := by
  intro h; with_reducible rfl

theorem _root_.Prysm.CommitteeIndex.Decode.accept_kind_anchor : ∀ (h : Host), type_of% (@Prysm.CommitteeIndex.Decode.accept h)
    = @u64DecAcceptKind h committeeIndexUnmarshalSSZ := by
  intro h; with_reducible rfl

end Prysm.Slot
