import Prysm.BlobIdentifier.DecodeRejectSize
import Prysm.DepositMessage.DecodeRejectSize
import Prysm.Eth1Data.DecodeRejectSize
import Prysm.BeaconBlockHeader.DecodeRejectSize
import Prysm.Deposit_Data.DecodeRejectSize
import Prysm.PendingPartialWithdrawal.DecodeRejectSize
import Prysm.SyncCommitteeMessage.DecodeRejectSize
import Prysm.PendingConsolidation.DecodeRejectSize
import Prysm.PendingDeposit.DecodeRejectSize
import Prysm.PowBlock.DecodeRejectSize
import Prysm.AttestationData.DecodeRejectSize
import Codec.DecodeRejectSizeAnyFrame

/-!
# Ties of `decRejectKindAnyFrame` to the committed size-reject theorems: the `PendingConsolidation` part

The declarations of the other types of this group are in `Prysm/BlobIdentifier/DecodeRejectSizeKindInstances.lean`.
-/

open Machine Runtime

open Codec
namespace Prysm.PendingConsolidation

theorem Decode.reject_size_is_kind_any_frame : ∀ (h : Host), type_of% (@Prysm.PendingConsolidation.Decode.reject_size h)
    = @decRejectKindAnyFrame h Prysm.PendingConsolidation.Code.unmarshalSSZ 16 := by
  intro h; with_reducible rfl

end Prysm.PendingConsolidation
