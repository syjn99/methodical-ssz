import Kraken.X64.Parser
import Fk.Include

/-!
# Code of the ENC2 encoder set (unit E2-P; Go 1.26.10 ELF `c6403c02…911e`)

Each constant includes a `.S` file of `fv/kraken/prysm/go1.26.10/e2e/enc2/link/norm`
(`link/conv.py --norm` of the same ELF as `E2e.Code`, `E2eAd.Code`, `E2eScal.BhCode`, `E2eScal.E1Code` and
`E2eScal.H6Code`; `link/check.py` (a)–(f) PASS in `../RESULT`, bundle `c08ac537…`).
Code constants only: no theorem, no contract. Hand-written include file of unit E2-P (not generator output;
the text of `H6Code.lean` with the function set changed).
Limit: the directory `enc2/link/norm` is not a Lake `input_dir` of the `E2eScal` library (a lakefile change
needs approval), so Lake does not rebuild these modules when a `.S` file changes. The `.S` files are
bound by the link bundle hash; a cold build is the check after any change.
-/

namespace E2eScal.Enc2Code

/-- `(*v1alpha1.BlobIdentifier).MarshalSSZTo`. -/
def BiMarshal : Program := include_x64_rt "../prysm/go1.26.10/e2e/enc2/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlobIdentifier.MarshalSSZTo.S"
/-- `(*v1alpha1.DepositMessage).MarshalSSZTo`. -/
def DmMarshal : Program := include_x64_rt "../prysm/go1.26.10/e2e/enc2/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DepositMessage.MarshalSSZTo.S"
/-- `(*v1alpha1.Deposit_Data).MarshalSSZTo`. -/
def DdMarshal : Program := include_x64_rt "../prysm/go1.26.10/e2e/enc2/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Deposit_Data.MarshalSSZTo.S"
/-- `(*v1alpha1.PendingPartialWithdrawal).MarshalSSZTo`. -/
def PwMarshal : Program := include_x64_rt "../prysm/go1.26.10/e2e/enc2/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingPartialWithdrawal.MarshalSSZTo.S"
/-- `(*v1alpha1.SyncCommitteeMessage).MarshalSSZTo`. -/
def ScMarshal : Program := include_x64_rt "../prysm/go1.26.10/e2e/enc2/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommitteeMessage.MarshalSSZTo.S"
/-- `(*v1alpha1.PendingConsolidation).MarshalSSZTo`. -/
def PcMarshal : Program := include_x64_rt "../prysm/go1.26.10/e2e/enc2/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingConsolidation.MarshalSSZTo.S"
/-- `(*v1alpha1.PendingDeposit).MarshalSSZTo`. -/
def PdMarshal : Program := include_x64_rt "../prysm/go1.26.10/e2e/enc2/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingDeposit.MarshalSSZTo.S"
/-- `(*v1alpha1.PowBlock).MarshalSSZTo`. -/
def PbMarshal : Program := include_x64_rt "../prysm/go1.26.10/e2e/enc2/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PowBlock.MarshalSSZTo.S"
/-- `(*v1alpha1.HistoricalSummary).MarshalSSZTo`. -/
def HsMarshal : Program := include_x64_rt "../prysm/go1.26.10/e2e/enc2/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.HistoricalSummary.MarshalSSZTo.S"
/-- `(*v1alpha1.SigningData).MarshalSSZTo`. -/
def SdMarshal : Program := include_x64_rt "../prysm/go1.26.10/e2e/enc2/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SigningData.MarshalSSZTo.S"
/-- `(*v1alpha1.SyncAggregatorSelectionData).MarshalSSZTo`. -/
def SaMarshal : Program := include_x64_rt "../prysm/go1.26.10/e2e/enc2/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncAggregatorSelectionData.MarshalSSZTo.S"
/-- `(*v1alpha1.ValidatorBalance).MarshalSSZTo`. -/
def VbMarshal : Program := include_x64_rt "../prysm/go1.26.10/e2e/enc2/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorBalance.MarshalSSZTo.S"
/-- `(*v1alpha1.VoluntaryExit).MarshalSSZTo`. -/
def VeMarshal : Program := include_x64_rt "../prysm/go1.26.10/e2e/enc2/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.VoluntaryExit.MarshalSSZTo.S"

end E2eScal.Enc2Code
