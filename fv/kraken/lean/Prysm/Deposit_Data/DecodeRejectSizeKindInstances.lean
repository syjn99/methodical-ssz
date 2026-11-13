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
# GEN5 L3: ties of `decRejectKindN` to the committed size-reject theorems: the `Deposit_Data` part

The declarations of the other types of this group are in `Prysm/BlobIdentifier/DecodeRejectSizeKindInstances.lean`.
-/

open Machine Runtime

open Codec
namespace Prysm.Deposit_Data

theorem Decode.reject_size_is_kind_any_frame : ∀ (h : Host), type_of% (@Prysm.Deposit_Data.Decode.reject_size h)
    = @decRejectKindN h Prysm.Deposit_Data.Code.unmarshalSSZ 184 := by
  intro h; with_reducible rfl

end Prysm.Deposit_Data
