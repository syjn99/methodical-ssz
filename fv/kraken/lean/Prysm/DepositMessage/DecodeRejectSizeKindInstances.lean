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
# Ties of `decRejectKindN` to the committed size-reject theorems: the `DepositMessage` part

The declarations of the other types of this group are in `Prysm/BlobIdentifier/DecodeRejectSizeKindInstances.lean`.
-/

open Machine Runtime

open Codec
namespace Prysm.DepositMessage

theorem Decode.reject_size_is_kind_any_frame : ∀ (h : Host), type_of% (@Prysm.DepositMessage.Decode.reject_size h)
    = @decRejectKindN h Prysm.DepositMessage.Code.unmarshalSSZ 88 := by
  intro h; with_reducible rfl

end Prysm.DepositMessage
