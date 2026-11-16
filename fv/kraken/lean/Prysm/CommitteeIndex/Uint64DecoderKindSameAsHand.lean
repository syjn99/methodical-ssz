import Codec.Kind.FieldPatterns
import Prysm.CommitteeIndex.DecodeAccept
import Prysm.CommitteeIndex.Code

/-!
# Tie of the uint64 decoder kind to the hand accept theorem of `CommitteeIndex`

This theorem shows that the kind `Codec.uint64DecodeAcceptKind` is the statement of the hand theorem `Prysm.CommitteeIndex.Decode.accept`.
The identity covers the full declared type, with the binders before the colon.
-/

open Machine Runtime

open Codec
namespace Prysm.CommitteeIndex

theorem Decode.accept_kind_anchor : ∀ (h : Host), type_of% (@Prysm.CommitteeIndex.Decode.accept h)
    = @uint64DecodeAcceptKind h Code.unmarshalSSZ := by
  intro h; with_reducible rfl

end Prysm.CommitteeIndex
