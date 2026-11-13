import Kraken.X64.Parser
import Machine.Include
import Prysm.HistoricalSummary.Code
import Prysm.PowBlock.Code
import Prysm.SigningData.Code
import Prysm.SyncAggregatorSelectionData.Code
import Prysm.ValidatorBalance.Code
import Prysm.VoluntaryExit.Code

/-!
# Code of the hold-out function set (Go 1.26.10 ELF `c6403c02…911e`)

Each constant includes a `.S` file of `fv/kraken/prysm/go1.26.10/e2e/h6/link/norm`
(`link/conv.py --norm` of the same ELF as `Prysm.Checkpoint.Code`, `Prysm.AttestationData.Code`, `Prysm.BeaconBlockHeader.Code`, `Prysm.Eth1Data.Code`,
`Prysm.BlobIdentifier.Code`, `Prysm.Deposit_Data.Code` and `Prysm.SyncCommitteeMessage.Code`; `link/check.py` (a)–(f) PASS in `../RESULT`,
bundle `eb1d6846…`). Hand-written include file (not generator output; the text of
`Prysm/SyncCommitteeMessage/Code.lean` with the function set changed).
Limit: the directory `h6/link/norm` is not a Lake `input_dir` of the `Prysm` library (a lakefile change
needs approval), so Lake does not rebuild these modules when a `.S` file changes. The `.S` files are
bound by the link bundle hash; a cold build is the check after any change.
After the split of this module, the declarations of the other types are in `Prysm/HistoricalSummary/Code.lean`, `Prysm/PowBlock/Code.lean`, `Prysm/SigningData/Code.lean`, `Prysm/SyncAggregatorSelectionData/Code.lean`, `Prysm/ValidatorBalance/Code.lean`, `Prysm/VoluntaryExit/Code.lean`.
-/

namespace Prysm.PendingDeposit

/-- `(*v1alpha1.PendingDeposit).UnmarshalSSZ`. -/
def Code.unmarshalSSZ : Program := include_x64_rt "../prysm/go1.26.10/e2e/h6/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingDeposit.UnmarshalSSZ.S"
end Prysm.PendingDeposit
