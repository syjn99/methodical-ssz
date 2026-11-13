import Codec.Kind.DecodeAcceptAnyFrame
import Prysm.BeaconBlockHeader.DecodeAccept
import Prysm.PendingPartialWithdrawal.DecodeAccept
import Prysm.SyncCommitteeMessage.Statements
import Prysm.PendingDeposit.Statements
import Prysm.Checkpoint.DecodeAccept
import Codec.Kind.DecodeAcceptAnyFrameInstances

/-!
# Ties of `decodeAcceptKindAnyFrame` to the hand accept statements: the `PendingConsolidation` part

The declarations of the other types of this group are in `Codec/Kind/DecodeAcceptAnyFrameInstances.lean`.
-/

open Machine Runtime

open Codec
namespace Prysm.PendingConsolidation

theorem Decode.accept_is_kind_any_frame : ∀ (h : Host), @Prysm.PendingConsolidation.Decode.accept_statement h
    = @decodeAcceptKindAnyFrame h Prysm.PendingConsolidation.Code.unmarshalSSZ (layoutCalleeCalls [Prysm.ValidatorIndex.Code.unmarshalSSZ] 56) [.uint64, .uint64] := by
  intro h; rfl

end Prysm.PendingConsolidation
