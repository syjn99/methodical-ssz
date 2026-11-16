import Prysm.BlobIdentifier.DecodeRejectSize
import Prysm.BeaconBlockHeader.DecodeRejectSize
import Prysm.PendingPartialWithdrawal.DecodeRejectSize
import Prysm.SyncCommitteeMessage.DecodeRejectSize
import Prysm.PendingConsolidation.DecodeRejectSize
import Prysm.PendingDeposit.DecodeRejectSize
import Prysm.PowBlock.DecodeRejectSize
import Prysm.AttestationData.DecodeRejectSize
import Codec.DecodeRejectSizeAnyFrame
import Prysm.BeaconBlockHeader.DecodeRejectSizeKindInstances
import Prysm.Checkpoint.DecodeRejectSizeKindInstances
import Prysm.PendingConsolidation.DecodeRejectSizeKindInstances
import Prysm.PendingDeposit.DecodeRejectSizeKindInstances
import Prysm.PowBlock.DecodeRejectSizeKindInstances
import Prysm.SyncCommitteeMessage.DecodeRejectSizeKindInstances

/-!
# Ties of `decodeRejectKindAnyFrame` to the committed size-reject theorems

The declared type of each committed theorem `Prysm.<Type>.Decode.reject_size` (9 flat development types and
AttestationData; the other types have the generated `Decode.generated_reject`, each with its own `_kind` line) is the kind instance; `with_reducible rfl` (the kind is an `abbrev` and the text is the same).
-/

open Machine Runtime

open Codec
namespace Prysm.BlobIdentifier

theorem Decode.reject_size_is_kind_any_frame : ∀ (h : Host), type_of% (@Prysm.BlobIdentifier.Decode.reject_size h)
    = @decodeRejectKindAnyFrame h Prysm.BlobIdentifier.Code.unmarshalSSZ 40 := by
  intro h; with_reducible rfl

end Prysm.BlobIdentifier
