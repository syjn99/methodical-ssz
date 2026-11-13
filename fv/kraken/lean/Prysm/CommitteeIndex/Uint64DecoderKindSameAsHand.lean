import Codec.Kind.FieldPatterns
import Prysm.Slot.DecodeAccept

/-!
# Anchors of the uint64 decoder statement kind: the `CommitteeIndex` part

The declarations of the other types of this group are in `Prysm/Slot/Uint64DecoderKindSameAsHand.lean`.
-/

open Machine Runtime Prysm.AttestationData.Code

open Codec
namespace Prysm.CommitteeIndex

theorem Decode.accept_kind_anchor : ∀ (h : Host), type_of% (@Prysm.CommitteeIndex.Decode.accept h)
    = @uint64DecodeAcceptKind h Code.unmarshalSSZ := by
  intro h; with_reducible rfl

end Prysm.CommitteeIndex
