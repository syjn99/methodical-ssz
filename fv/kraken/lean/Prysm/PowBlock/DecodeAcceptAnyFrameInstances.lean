import Codec.Kind.DecodeAcceptAnyFrame
import Prysm.BeaconBlockHeader.DecodeAccept
import Prysm.PendingPartialWithdrawal.DecodeAccept
import Prysm.SyncCommitteeMessage.Statements
import Prysm.PendingDeposit.Statements
import Prysm.Checkpoint.DecodeAccept
import Codec.Kind.DecodeAcceptAnyFrameInstances

/-!
# GEN5 L1: ties of `decAcceptKindN` to the hand accept statements: the `PowBlock` part

The declarations of the other types of this group are in `Codec/Kind/DecodeAcceptAnyFrameInstances.lean`.
-/

open Machine Runtime

open Codec
namespace Prysm.PowBlock

theorem Decode.accept_is_kind_any_frame : ∀ (h : Host), @Prysm.PowBlock.Decode.accept_statement h
    = @decAcceptKindN h Prysm.PowBlock.Code.unmarshalSSZ (layRt false 104 3) [.bytes 32, .bytes 32, .bytes 32] := by
  intro h; rfl

end Prysm.PowBlock
