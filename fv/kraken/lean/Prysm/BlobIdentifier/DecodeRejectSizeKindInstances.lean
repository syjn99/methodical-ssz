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
# GEN5 L3: ties of `decRejectKindN` to the committed size-reject theorems

The declared type of each committed theorem `*_e2e_reject_size_main` (the 11 flat development types and
AttestationData) is the kind instance; `with_reducible rfl` (the kind is an `abbrev` and the text is the same).
-/

open Machine Runtime TestTarget

open Codec
namespace Prysm.BlobIdentifier

theorem Decode.reject_size_is_kind_any_frame : ∀ (h : Host), type_of% (@Prysm.BlobIdentifier.Decode.reject_size h)
    = @decRejectKindN h Prysm.BlobIdentifier.Code.unmarshalSSZ 40 := by
  intro h; with_reducible rfl

theorem _root_.Prysm.DepositMessage.Decode.reject_size_is_kind_any_frame : ∀ (h : Host), type_of% (@Prysm.DepositMessage.Decode.reject_size h)
    = @decRejectKindN h Prysm.DepositMessage.Code.unmarshalSSZ 88 := by
  intro h; with_reducible rfl

theorem _root_.Prysm.Eth1Data.Decode.reject_size_is_kind_any_frame : ∀ (h : Host), type_of% (@Prysm.Eth1Data.Decode.reject_size h)
    = @decRejectKindN h Prysm.Eth1Data.Code.unmarshalSSZ 72 := by
  intro h; with_reducible rfl

theorem _root_.Prysm.BeaconBlockHeader.Decode.reject_size_is_kind_any_frame : ∀ (h : Host), type_of% (@Prysm.BeaconBlockHeader.Decode.reject_size h)
    = @decRejectKindN h Prysm.BeaconBlockHeader.Code.unmarshalSSZ 112 := by
  intro h; with_reducible rfl

theorem _root_.Prysm.Deposit_Data.Decode.reject_size_is_kind_any_frame : ∀ (h : Host), type_of% (@Prysm.Deposit_Data.Decode.reject_size h)
    = @decRejectKindN h Prysm.Deposit_Data.Code.unmarshalSSZ 184 := by
  intro h; with_reducible rfl

theorem _root_.Prysm.PendingPartialWithdrawal.Decode.reject_size_is_kind_any_frame : ∀ (h : Host), type_of% (@Prysm.PendingPartialWithdrawal.Decode.reject_size h)
    = @decRejectKindN h Prysm.PendingPartialWithdrawal.Code.unmarshalSSZ 24 := by
  intro h; with_reducible rfl

theorem _root_.Prysm.SyncCommitteeMessage.Decode.reject_size_is_kind_any_frame : ∀ (h : Host), type_of% (@Prysm.SyncCommitteeMessage.Decode.reject_size h)
    = @decRejectKindN h Prysm.SyncCommitteeMessage.Code.unmarshalSSZ 144 := by
  intro h; with_reducible rfl

theorem _root_.Prysm.PendingConsolidation.Decode.reject_size_is_kind_any_frame : ∀ (h : Host), type_of% (@Prysm.PendingConsolidation.Decode.reject_size h)
    = @decRejectKindN h Prysm.PendingConsolidation.Code.unmarshalSSZ 16 := by
  intro h; with_reducible rfl

theorem _root_.Prysm.PendingDeposit.Decode.reject_size_is_kind_any_frame : ∀ (h : Host), type_of% (@Prysm.PendingDeposit.Decode.reject_size h)
    = @decRejectKindN h Prysm.PendingDeposit.Code.unmarshalSSZ 192 := by
  intro h; with_reducible rfl

theorem _root_.Prysm.PowBlock.Decode.reject_size_is_kind_any_frame : ∀ (h : Host), type_of% (@Prysm.PowBlock.Decode.reject_size h)
    = @decRejectKindN h Prysm.PowBlock.Code.unmarshalSSZ 96 := by
  intro h; with_reducible rfl

theorem _root_.Prysm.Checkpoint.Decode.reject_size_is_kind_any_frame : ∀ (h : Host), type_of% (@Prysm.Checkpoint.Decode.reject_size h)
    = @decRejectKindN h Prysm.Checkpoint.Code.unmarshalSSZ 40 := by
  intro h; with_reducible rfl

theorem _root_.Prysm.AttestationData.Decode.reject_size_is_kind_any_frame : ∀ (h : Host), type_of% (@Prysm.AttestationData.Decode.reject_size h)
    = @decRejectKindN h Prysm.AttestationData.Code.unmarshalSSZ 128 := by
  intro h; with_reducible rfl

end Prysm.BlobIdentifier
