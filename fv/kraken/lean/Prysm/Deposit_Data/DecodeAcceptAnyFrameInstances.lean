import Codec.Kind.DecodeAcceptAnyFrame
import Prysm.BeaconBlockHeader.DecodeAccept
import Prysm.PendingPartialWithdrawal.DecodeAccept
import Prysm.SyncCommitteeMessage.Statements
import Prysm.PendingDeposit.Statements
import Prysm.Checkpoint.DecodeAccept
import Codec.Kind.DecodeAcceptAnyFrameInstances
import Prysm.Deposit_Data.DecodeAcceptComposition

/-!
# Ties of `decodeAcceptKindAnyFrame` to the hand accept statements: the `Deposit_Data` part

The declarations of the other types of this group are in `Codec/Kind/DecodeAcceptAnyFrameInstances.lean`.
-/

open Machine Runtime

open Codec
namespace Prysm.Deposit_Data

theorem Decode.accept_is_kind_any_frame : ∀ (h : Host), @Prysm.Deposit_Data.Decode.accept_statement h
    = @decodeAcceptKindAnyFrame h Prysm.Deposit_Data.Code.unmarshalSSZ (layoutRuntimeCalls true 106 3) [.bytes 48, .bytes 32, .uint64, .bytes 96] := by
  intro h; rfl

theorem Decode.accept_kind_any_frame_is_kind : ∀ (h : Host),
    @decodeAcceptKindAnyFrame h Prysm.Deposit_Data.Code.unmarshalSSZ (layoutRuntimeCalls true 106 3) [.bytes 48, .bytes 32, .uint64, .bytes 96]
    = @decodeAcceptKind h Prysm.Deposit_Data.Code.unmarshalSSZ true [.bytes 48, .bytes 32, .uint64, .bytes 96] 106 :=
  fun h => (Prysm.Deposit_Data.Decode.accept_is_kind_any_frame h).symm.trans (Prysm.Deposit_Data.Decode.accept_is_kind h)

end Prysm.Deposit_Data
