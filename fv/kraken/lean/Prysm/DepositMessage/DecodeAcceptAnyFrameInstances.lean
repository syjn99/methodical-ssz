import Codec.Kind.DecodeAcceptAnyFrame
import Prysm.BeaconBlockHeader.DecodeAccept
import Prysm.PendingPartialWithdrawal.DecodeAccept
import Prysm.SyncCommitteeMessage.Statements
import Prysm.PendingDeposit.Statements
import Prysm.Checkpoint.DecodeAccept
import Codec.Kind.DecodeAcceptAnyFrameInstances
import Prysm.DepositMessage.DecodeAcceptComposition

/-!
# GEN5 L1: ties of `decAcceptKindN` to the hand accept statements: the `DepositMessage` part

The declarations of the other types of this group are in `Codec/Kind/DecodeAcceptAnyFrameInstances.lean`.
-/

open Machine Runtime

open Codec
namespace Prysm.DepositMessage

theorem Decode.accept_is_kind_any_frame : ∀ (h : Host), type_of% (@Prysm.DepositMessage.Decode.accept h)
    = @decAcceptKindN h Prysm.DepositMessage.Code.unmarshalSSZ (layRt false 68 2) [.bytes 48, .bytes 32, .u64] := by
  intro h; rfl

theorem Decode.accept_kind_any_frame_is_kind : ∀ (h : Host),
    @decAcceptKindN h Prysm.DepositMessage.Code.unmarshalSSZ (layRt false 68 2) [.bytes 48, .bytes 32, .u64]
    = @decAcceptKind h Prysm.DepositMessage.Code.unmarshalSSZ false [.bytes 48, .bytes 32, .u64] 68 :=
  fun h => (Prysm.DepositMessage.Decode.accept_is_kind_any_frame h).symm.trans (Prysm.DepositMessage.Decode.accept_is_kind h)

end Prysm.DepositMessage
