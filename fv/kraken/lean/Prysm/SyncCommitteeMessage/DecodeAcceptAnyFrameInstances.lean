import Codec.Kind.DecodeAcceptAnyFrame
import Prysm.BeaconBlockHeader.DecodeAccept
import Prysm.PendingPartialWithdrawal.DecodeAccept
import Prysm.SyncCommitteeMessage.Statements
import Prysm.PendingDeposit.Statements
import Prysm.Checkpoint.DecodeAccept
import Codec.Kind.DecodeAcceptAnyFrameInstances

/-!
# Ties of `decodeAcceptKindAnyFrame` to the hand accept statements: the `SyncCommitteeMessage` part

The declarations of the other types of this group are in `Codec/Kind/DecodeAcceptAnyFrameInstances.lean`.
-/

open Machine Runtime

open Codec
namespace Prysm.SyncCommitteeMessage

theorem Decode.accept_is_kind_any_frame : ∀ (h : Host), @Prysm.SyncCommitteeMessage.Decode.accept_statement h
    = @decodeAcceptKindAnyFrame h Prysm.SyncCommitteeMessage.Code.unmarshalSSZ
        (layoutMixedFrame60 [Prysm.Slot.Code.unmarshalSSZ, Prysm.ValidatorIndex.Code.unmarshalSSZ] 141 1)
        [.uint64, .bytes 32, .uint64, .bytes 96] := by
  intro h; rfl

end Prysm.SyncCommitteeMessage
