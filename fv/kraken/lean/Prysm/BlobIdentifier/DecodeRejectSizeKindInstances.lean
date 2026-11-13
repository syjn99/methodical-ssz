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
import Prysm.AttestationData.DecodeRejectSizeKindInstances
import Prysm.BeaconBlockHeader.DecodeRejectSizeKindInstances
import Prysm.Checkpoint.DecodeRejectSizeKindInstances
import Prysm.DepositMessage.DecodeRejectSizeKindInstances
import Prysm.Deposit_Data.DecodeRejectSizeKindInstances
import Prysm.Eth1Data.DecodeRejectSizeKindInstances
import Prysm.PendingConsolidation.DecodeRejectSizeKindInstances
import Prysm.PendingDeposit.DecodeRejectSizeKindInstances
import Prysm.PendingPartialWithdrawal.DecodeRejectSizeKindInstances
import Prysm.PowBlock.DecodeRejectSizeKindInstances
import Prysm.SyncCommitteeMessage.DecodeRejectSizeKindInstances

/-!
# Ties of `decodeRejectKindAnyFrame` to the committed size-reject theorems

The declared type of each committed theorem `Prysm.<Type>.Decode.reject_size` (the 11 flat development types and
AttestationData) is the kind instance; `with_reducible rfl` (the kind is an `abbrev` and the text is the same).
After the split of this module, the declarations of the other types are in `Prysm/AttestationData/DecodeRejectSizeKindInstances.lean`, `Prysm/BeaconBlockHeader/DecodeRejectSizeKindInstances.lean`, `Prysm/Checkpoint/DecodeRejectSizeKindInstances.lean`, `Prysm/DepositMessage/DecodeRejectSizeKindInstances.lean`, `Prysm/Deposit_Data/DecodeRejectSizeKindInstances.lean`, `Prysm/Eth1Data/DecodeRejectSizeKindInstances.lean`, `Prysm/PendingConsolidation/DecodeRejectSizeKindInstances.lean`, `Prysm/PendingDeposit/DecodeRejectSizeKindInstances.lean`, `Prysm/PendingPartialWithdrawal/DecodeRejectSizeKindInstances.lean`, `Prysm/PowBlock/DecodeRejectSizeKindInstances.lean`, `Prysm/SyncCommitteeMessage/DecodeRejectSizeKindInstances.lean`.
-/

open Machine Runtime

open Codec
namespace Prysm.BlobIdentifier

theorem Decode.reject_size_is_kind_any_frame : ∀ (h : Host), type_of% (@Prysm.BlobIdentifier.Decode.reject_size h)
    = @decodeRejectKindAnyFrame h Prysm.BlobIdentifier.Code.unmarshalSSZ 40 := by
  intro h; with_reducible rfl

end Prysm.BlobIdentifier
