import Kraken.X64.Parser
import Machine.Include

/-!
# Code of the hold-out function set (Go 1.26.10 ELF `c6403c02…911e`)

Each constant includes a `.S` file of `fv/kraken/prysm/go1.26.10/e2e/h6/link/norm`
(`link/conv.py --norm` of the same ELF as `Prysm.Checkpoint.Code`, `Prysm.AttestationData.Code`, `E2eScal.BhCode`, `E2eScal.E1Code`,
`E2eScal.H3Code`, `E2eScal.H4Code` and `E2eScal.H5Code`; `link/check.py` (a)–(f) PASS in `../RESULT`,
bundle `eb1d6846…`). Hand-written include file (not generator output; the text of
`H5Code.lean` with the function set changed).
Limit: the directory `h6/link/norm` is not a Lake `input_dir` of the `E2eScal` library (a lakefile change
needs approval), so Lake does not rebuild these modules when a `.S` file changes. The `.S` files are
bound by the link bundle hash; a cold build is the check after any change.
-/

namespace E2eScal.H6Code

/-- `(*v1alpha1.PendingDeposit).UnmarshalSSZ`. -/
def PdUnmarshal : Program := include_x64_rt "../prysm/go1.26.10/e2e/h6/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingDeposit.UnmarshalSSZ.S"
/-- `(*v1alpha1.PowBlock).UnmarshalSSZ`. -/
def PbUnmarshal : Program := include_x64_rt "../prysm/go1.26.10/e2e/h6/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PowBlock.UnmarshalSSZ.S"
/-- `(*v1alpha1.HistoricalSummary).UnmarshalSSZ`. -/
def HsUnmarshal : Program := include_x64_rt "../prysm/go1.26.10/e2e/h6/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.HistoricalSummary.UnmarshalSSZ.S"
/-- `(*v1alpha1.SigningData).UnmarshalSSZ`. -/
def SdUnmarshal : Program := include_x64_rt "../prysm/go1.26.10/e2e/h6/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SigningData.UnmarshalSSZ.S"
/-- `(*v1alpha1.SyncAggregatorSelectionData).UnmarshalSSZ`. -/
def SaUnmarshal : Program := include_x64_rt "../prysm/go1.26.10/e2e/h6/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncAggregatorSelectionData.UnmarshalSSZ.S"
/-- `(*v1alpha1.ValidatorBalance).UnmarshalSSZ`. -/
def VbUnmarshal : Program := include_x64_rt "../prysm/go1.26.10/e2e/h6/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorBalance.UnmarshalSSZ.S"
/-- `(*v1alpha1.VoluntaryExit).UnmarshalSSZ`. -/
def VeUnmarshal : Program := include_x64_rt "../prysm/go1.26.10/e2e/h6/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.VoluntaryExit.UnmarshalSSZ.S"

end E2eScal.H6Code
