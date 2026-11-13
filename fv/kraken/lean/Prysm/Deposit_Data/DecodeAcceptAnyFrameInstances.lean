import Codec.Kind.DecodeAcceptAnyFrame
import Prysm.BeaconBlockHeader.DecodeAccept
import Prysm.PendingPartialWithdrawal.DecodeAccept
import Prysm.SyncCommitteeMessage.Statements
import Prysm.PendingDeposit.Statements
import Prysm.Checkpoint.DecodeAccept
import Codec.Kind.DecodeAcceptAnyFrameInstances
import Prysm.Deposit_Data.DecodeAcceptComposition

/-!
# Ties of `decAcceptKindN` to the hand accept statements: the `Deposit_Data` part

The declarations of the other types of this group are in `Codec/Kind/DecodeAcceptAnyFrameInstances.lean`.
-/

open Machine Runtime

open Codec
namespace Prysm.Deposit_Data

theorem Decode.accept_is_kind_any_frame : ∀ (h : Host), @Prysm.Deposit_Data.Decode.accept_statement h
    = @decAcceptKindN h Prysm.Deposit_Data.Code.unmarshalSSZ (layRt true 106 3) [.bytes 48, .bytes 32, .u64, .bytes 96] := by
  intro h; rfl

theorem Decode.accept_kind_any_frame_is_kind : ∀ (h : Host),
    @decAcceptKindN h Prysm.Deposit_Data.Code.unmarshalSSZ (layRt true 106 3) [.bytes 48, .bytes 32, .u64, .bytes 96]
    = @decAcceptKind h Prysm.Deposit_Data.Code.unmarshalSSZ true [.bytes 48, .bytes 32, .u64, .bytes 96] 106 :=
  fun h => (Prysm.Deposit_Data.Decode.accept_is_kind_any_frame h).symm.trans (Prysm.Deposit_Data.Decode.accept_is_kind h)

end Prysm.Deposit_Data
