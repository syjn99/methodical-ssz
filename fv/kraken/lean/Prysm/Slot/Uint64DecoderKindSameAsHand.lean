import Codec.Kind.FieldPatterns
import Prysm.Slot.DecodeAccept
import Prysm.Slot.Code

/-!
# Anchors of the uint64 decoder statement kind

The uint64 decoder kind `Codec.uint64DecodeAcceptKind C` is, for `C = Code.unmarshalSSZ` and `C = Prysm.CommitteeIndex.Code.unmarshalSSZ`, the full declared
type of the reviewed hand theorem (binders before the colon included). So the frozen kind is the hand
statement kind, not new text.
The anchor of `Prysm.CommitteeIndex` is in `Prysm/CommitteeIndex/Uint64DecoderKindSameAsHand.lean`.
-/

open Machine Runtime

open Codec
namespace Prysm.Slot

theorem Decode.accept_kind_anchor : ∀ (h : Host), type_of% (@Prysm.Slot.Decode.accept h)
    = @uint64DecodeAcceptKind h Code.unmarshalSSZ := by
  intro h; with_reducible rfl

end Prysm.Slot
