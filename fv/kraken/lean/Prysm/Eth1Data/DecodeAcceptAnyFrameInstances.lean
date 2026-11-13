import Codec.Kind.DecodeAcceptAnyFrame
import Prysm.BeaconBlockHeader.DecodeAccept
import Prysm.PendingPartialWithdrawal.DecodeAccept
import Prysm.SyncCommitteeMessage.Statements
import Prysm.PendingDeposit.Statements
import Prysm.Checkpoint.DecodeAccept
import Codec.Kind.DecodeAcceptAnyFrameInstances
import Prysm.Eth1Data.DecodeAcceptComposition

/-!
# Ties of `decodeAcceptKindAnyFrame` to the hand accept statements: the `Eth1Data` part

The declarations of the other types of this group are in `Codec/Kind/DecodeAcceptAnyFrameInstances.lean`.
-/

open Machine Runtime

open Codec
namespace Prysm.Eth1Data

theorem Decode.accept_is_kind_any_frame : ∀ (h : Host), type_of% (@Prysm.Eth1Data.Decode.accept h)
    = @decodeAcceptKindAnyFrame h Prysm.Eth1Data.Code.unmarshalSSZ (layoutRuntimeCalls true 70 2) [.bytes 32, .uint64, .bytes 32] := by
  intro h; rfl

theorem Decode.accept_kind_any_frame_is_kind : ∀ (h : Host),
    @decodeAcceptKindAnyFrame h Prysm.Eth1Data.Code.unmarshalSSZ (layoutRuntimeCalls true 70 2) [.bytes 32, .uint64, .bytes 32]
    = @decodeAcceptKind h Prysm.Eth1Data.Code.unmarshalSSZ true [.bytes 32, .uint64, .bytes 32] 70 :=
  fun h => (Prysm.Eth1Data.Decode.accept_is_kind_any_frame h).symm.trans (Prysm.Eth1Data.Decode.accept_is_kind h)

end Prysm.Eth1Data
