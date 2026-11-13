import Codec.Kind.DecodeAcceptAnyFrame
import Prysm.BeaconBlockHeader.DecodeAccept
import Prysm.PendingPartialWithdrawal.DecodeAccept
import Prysm.SyncCommitteeMessage.Statements
import Prysm.PendingDeposit.Statements
import Prysm.Checkpoint.DecodeAccept
import Codec.Kind.DecodeAcceptAnyFrameInstances

/-!
# Ties of `decodeAcceptKindAnyFrame` to the hand accept statements: the `PendingDeposit` part

The declarations of the other types of this group are in `Codec/Kind/DecodeAcceptAnyFrameInstances.lean`.
-/

open Machine Runtime

open Codec
namespace Prysm.PendingDeposit

/-! ## Class C: frames `0x40`, `0x60` -/

theorem Decode.accept_is_kind_any_frame : ∀ (h : Host), @Prysm.PendingDeposit.Decode.accept_statement h
    = @decodeAcceptKindAnyFrame h Prysm.PendingDeposit.Code.unmarshalSSZ (layoutMixedFrame40 [Prysm.Slot.Code.unmarshalSSZ] 131 2)
        [.bytes 48, .bytes 32, .uint64, .bytes 96, .uint64] := by
  intro h; rfl

end Prysm.PendingDeposit
