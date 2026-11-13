import Codec.Kind.DecodeAcceptAnyFrame
import Prysm.BeaconBlockHeader.DecodeAccept
import Prysm.PendingPartialWithdrawal.DecodeAccept
import Prysm.SyncCommitteeMessage.Statements
import Prysm.PendingDeposit.Statements
import Prysm.Checkpoint.DecodeAccept
import Codec.Kind.DecodeAcceptAnyFrameInstances

/-!
# Ties of `decAcceptKindAnyFrame` to the hand accept statements: the `PendingPartialWithdrawal` part

The declarations of the other types of this group are in `Codec/Kind/DecodeAcceptAnyFrameInstances.lean`.
-/

open Machine Runtime

open Codec
namespace Prysm.PendingPartialWithdrawal

/-! ## Class B: frame `0x48` -/

theorem Decode.accept_is_kind_any_frame : ∀ (h : Host), @Prysm.PendingPartialWithdrawal.Decode.accept_statement h
    = @decAcceptKindAnyFrame h Prysm.PendingPartialWithdrawal.Code.unmarshalSSZ
        (layoutCalleeCalls [Prysm.ValidatorIndex.Code.unmarshalSSZ, Prysm.Epoch.Code.unmarshalSSZ] 60) [.u64, .u64, .u64] := by
  intro h; rfl

end Prysm.PendingPartialWithdrawal
