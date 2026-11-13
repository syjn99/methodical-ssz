import Codec.Kind.DecodeAcceptAnyFrame
import Prysm.BeaconBlockHeader.DecodeAccept
import Prysm.PendingPartialWithdrawal.DecodeAccept
import Prysm.SyncCommitteeMessage.Statements
import Prysm.PendingDeposit.Statements
import Prysm.Checkpoint.DecodeAccept
import Codec.Kind.DecodeAcceptAnyFrameInstances

/-!
# Ties of `decAcceptKindN` to the hand accept statements: the `PendingConsolidation` part

The declarations of the other types of this group are in `Codec/Kind/DecodeAcceptAnyFrameInstances.lean`.
-/

open Machine Runtime

open Codec
namespace Prysm.PendingConsolidation

theorem Decode.accept_is_kind_any_frame : ∀ (h : Host), @Prysm.PendingConsolidation.Decode.accept_statement h
    = @decAcceptKindN h Prysm.PendingConsolidation.Code.unmarshalSSZ (layCal [Prysm.ValidatorIndex.Code.unmarshalSSZ] 56) [.u64, .u64] := by
  intro h; rfl

end Prysm.PendingConsolidation
