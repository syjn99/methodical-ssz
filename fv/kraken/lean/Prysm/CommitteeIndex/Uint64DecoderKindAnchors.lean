import Codec.Kind.FieldPatterns
import Prysm.Slot.DecodeAccept

/-!
# Anchors of the P1 statement kind (review fix-r1 S1): the `CommitteeIndex` part

The declarations of the other types of this group are in `Prysm/Slot/Uint64DecoderKindAnchors.lean`.
-/

open Machine Runtime Prysm.AttestationData.Code

open Codec
namespace Prysm.CommitteeIndex

theorem Decode.accept_kind_anchor : ∀ (h : Host), type_of% (@Prysm.CommitteeIndex.Decode.accept h)
    = @u64DecAcceptKind h committeeIndexUnmarshalSSZ := by
  intro h; with_reducible rfl

end Prysm.CommitteeIndex
