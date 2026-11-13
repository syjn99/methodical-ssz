import Codec.Kind.DecodeAcceptAnyFrame
import Prysm.BeaconBlockHeader.DecodeAccept
import Prysm.PendingPartialWithdrawal.DecodeAccept
import Prysm.SyncCommitteeMessage.Statements
import Prysm.PendingDeposit.Statements
import Prysm.Checkpoint.DecodeAccept
import Codec.Kind.DecodeAcceptAnyFrameInstances

/-!
# Ties of `decAcceptKindN` to the hand accept statements: the `BeaconBlockHeader` part

The declarations of the other types of this group are in `Codec/Kind/DecodeAcceptAnyFrameInstances.lean`.
-/

open Machine Runtime

open Codec
namespace Prysm.BeaconBlockHeader

theorem Decode.accept_is_kind_any_frame : ∀ (h : Host), type_of% (@Prysm.BeaconBlockHeader.Decode.accept h)
    = @decAcceptKindN h Prysm.BeaconBlockHeader.Code.unmarshalSSZ
        (layMix60 [Prysm.Slot.Code.unmarshalSSZ, Prysm.ValidatorIndex.Code.unmarshalSSZ] 179 2)
        [.u64, .u64, .bytes 32, .bytes 32, .bytes 32] := by
  intro h; rfl

end Prysm.BeaconBlockHeader
