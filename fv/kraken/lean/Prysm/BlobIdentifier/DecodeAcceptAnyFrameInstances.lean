import Codec.Kind.DecodeAcceptAnyFrame
import Prysm.BeaconBlockHeader.DecodeAccept
import Prysm.PendingPartialWithdrawal.DecodeAccept
import Prysm.SyncCommitteeMessage.Statements
import Prysm.PendingDeposit.Statements
import Prysm.Checkpoint.DecodeAccept
import Codec.Kind.DecodeAcceptAnyFrameInstances
import Prysm.BlobIdentifier.DecodeAcceptComposition

/-!
# Ties of `decodeAcceptKindAnyFrame` to the hand accept statements: the `BlobIdentifier` part

The declarations of the other types of this group are in `Codec/Kind/DecodeAcceptAnyFrameInstances.lean`.
-/

open Machine Runtime

open Codec
namespace Prysm.BlobIdentifier

/-! ## Class A: frame `0x20` -/

theorem Decode.accept_is_kind_any_frame : ∀ (h : Host), type_of% (@Prysm.BlobIdentifier.Decode.accept h)
    = @decodeAcceptKindAnyFrame h Prysm.BlobIdentifier.Code.unmarshalSSZ (layoutRuntimeCalls true 32 1) [.bytes 32, .uint64] := by
  intro h; rfl

/-! ## Relation to the composed accept kind `decodeAcceptKind` (the four types it is tied to) -/

theorem Decode.accept_kind_any_frame_is_kind : ∀ (h : Host),
    @decodeAcceptKindAnyFrame h Prysm.BlobIdentifier.Code.unmarshalSSZ (layoutRuntimeCalls true 32 1) [.bytes 32, .uint64]
    = @decodeAcceptKind h Prysm.BlobIdentifier.Code.unmarshalSSZ true [.bytes 32, .uint64] 32 :=
  fun h => (Prysm.BlobIdentifier.Decode.accept_is_kind_any_frame h).symm.trans (Prysm.BlobIdentifier.Decode.accept_is_kind h)

end Prysm.BlobIdentifier
