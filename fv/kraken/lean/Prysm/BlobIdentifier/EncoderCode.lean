import Kraken.X64.Parser
import Machine.Include

/-!
# Code of the flat encoder set (Go 1.26.10 ELF `c6403c02…911e`)

Each constant includes a `.S` file of `fv/kraken/prysm/go1.26.10/e2e/enc2/link/norm`
(`link/conv.py --norm` of the same ELF as `Prysm.Checkpoint.Code`, `Prysm.AttestationData.Code`, `Prysm.BeaconBlockHeader.Code`, `Prysm.Eth1Data.Code` and
`Prysm.PendingDeposit.Code`; `link/check.py` (a)–(f) PASS in `../RESULT`, bundle `c08ac537…`).
Code constants only: no theorem, no contract. Hand-written include file (not generator output;
the text of `H6Code.lean` with the function set changed).
Limit: the directory `enc2/link/norm` is not a Lake `input_dir` of the `E2eScal` library (a lakefile change
needs approval), so Lake does not rebuild these modules when a `.S` file changes. The `.S` files are
bound by the link bundle hash; a cold build is the check after any change.
-/

namespace Prysm.BlobIdentifier

/-- `(*v1alpha1.BlobIdentifier).MarshalSSZTo`. -/
def Code.marshalSSZTo : Program := include_x64_rt "../prysm/go1.26.10/e2e/enc2/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlobIdentifier.MarshalSSZTo.S"
/-- `(*v1alpha1.DepositMessage).MarshalSSZTo`. -/
def _root_.Prysm.DepositMessage.Code.marshalSSZTo : Program := include_x64_rt "../prysm/go1.26.10/e2e/enc2/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DepositMessage.MarshalSSZTo.S"
/-- `(*v1alpha1.Deposit_Data).MarshalSSZTo`. -/
def _root_.Prysm.Deposit_Data.Code.marshalSSZTo : Program := include_x64_rt "../prysm/go1.26.10/e2e/enc2/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Deposit_Data.MarshalSSZTo.S"
/-- `(*v1alpha1.PendingPartialWithdrawal).MarshalSSZTo`. -/
def _root_.Prysm.PendingPartialWithdrawal.Code.marshalSSZTo : Program := include_x64_rt "../prysm/go1.26.10/e2e/enc2/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingPartialWithdrawal.MarshalSSZTo.S"
/-- `(*v1alpha1.SyncCommitteeMessage).MarshalSSZTo`. -/
def _root_.Prysm.SyncCommitteeMessage.Code.marshalSSZTo : Program := include_x64_rt "../prysm/go1.26.10/e2e/enc2/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommitteeMessage.MarshalSSZTo.S"
/-- `(*v1alpha1.PendingConsolidation).MarshalSSZTo`. -/
def _root_.Prysm.PendingConsolidation.Code.marshalSSZTo : Program := include_x64_rt "../prysm/go1.26.10/e2e/enc2/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingConsolidation.MarshalSSZTo.S"
/-- `(*v1alpha1.PendingDeposit).MarshalSSZTo`. -/
def _root_.Prysm.PendingDeposit.Code.marshalSSZTo : Program := include_x64_rt "../prysm/go1.26.10/e2e/enc2/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingDeposit.MarshalSSZTo.S"
/-- `(*v1alpha1.PowBlock).MarshalSSZTo`. -/
def _root_.Prysm.PowBlock.Code.marshalSSZTo : Program := include_x64_rt "../prysm/go1.26.10/e2e/enc2/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PowBlock.MarshalSSZTo.S"
/-- `(*v1alpha1.HistoricalSummary).MarshalSSZTo`. -/
def _root_.Prysm.HistoricalSummary.Code.marshalSSZTo : Program := include_x64_rt "../prysm/go1.26.10/e2e/enc2/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.HistoricalSummary.MarshalSSZTo.S"
/-- `(*v1alpha1.SigningData).MarshalSSZTo`. -/
def _root_.Prysm.SigningData.Code.marshalSSZTo : Program := include_x64_rt "../prysm/go1.26.10/e2e/enc2/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SigningData.MarshalSSZTo.S"
/-- `(*v1alpha1.SyncAggregatorSelectionData).MarshalSSZTo`. -/
def _root_.Prysm.SyncAggregatorSelectionData.Code.marshalSSZTo : Program := include_x64_rt "../prysm/go1.26.10/e2e/enc2/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncAggregatorSelectionData.MarshalSSZTo.S"
/-- `(*v1alpha1.ValidatorBalance).MarshalSSZTo`. -/
def _root_.Prysm.ValidatorBalance.Code.marshalSSZTo : Program := include_x64_rt "../prysm/go1.26.10/e2e/enc2/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorBalance.MarshalSSZTo.S"
/-- `(*v1alpha1.VoluntaryExit).MarshalSSZTo`. -/
def _root_.Prysm.VoluntaryExit.Code.marshalSSZTo : Program := include_x64_rt "../prysm/go1.26.10/e2e/enc2/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.VoluntaryExit.MarshalSSZTo.S"

end Prysm.BlobIdentifier
