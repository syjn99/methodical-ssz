import Kraken.X64.Parser
import Machine.Include
import Prysm.DepositMessage.EncoderCode
import Prysm.Deposit_Data.EncoderCode
import Prysm.HistoricalSummary.EncoderCode
import Prysm.PendingConsolidation.EncoderCode
import Prysm.PendingDeposit.EncoderCode
import Prysm.PendingPartialWithdrawal.EncoderCode
import Prysm.PowBlock.EncoderCode
import Prysm.SigningData.EncoderCode
import Prysm.SyncAggregatorSelectionData.EncoderCode
import Prysm.SyncCommitteeMessage.EncoderCode
import Prysm.ValidatorBalance.EncoderCode
import Prysm.VoluntaryExit.EncoderCode

/-!
# Code of the encoders of the flat types (Go 1.26.10 ELF `c6403c02…911e`)

Each constant includes a `.S` file of `fv/kraken/prysm/go1.26.10/link-set/norm`
(`link/conv.py --norm` of the same ELF as `Prysm.Checkpoint.Code`, `Prysm.AttestationData.Code`, `Prysm.BeaconBlockHeader.Code`, `Prysm.Eth1Data.Code` and
`Prysm.PendingDeposit.Code`; `link/check.py` (a)–(f) PASS in `prysm/go1.26.10/link-set/RESULT`).
Code constants only: no theorem, no contract. Hand-written include file (not generator output;
the text of `Prysm/PendingDeposit/Code.lean` with the function set changed).
The directory `prysm/go1.26.10/link-set/norm` is a Lake `input_dir` of the `Prysm` library,
so Lake rebuilds these modules when a `.S` file changes.
After the split of this module, the declarations of the other types are in `Prysm/DepositMessage/EncoderCode.lean`, `Prysm/Deposit_Data/EncoderCode.lean`, `Prysm/HistoricalSummary/EncoderCode.lean`, `Prysm/PendingConsolidation/EncoderCode.lean`, `Prysm/PendingDeposit/EncoderCode.lean`, `Prysm/PendingPartialWithdrawal/EncoderCode.lean`, `Prysm/PowBlock/EncoderCode.lean`, `Prysm/SigningData/EncoderCode.lean`, `Prysm/SyncAggregatorSelectionData/EncoderCode.lean`, `Prysm/SyncCommitteeMessage/EncoderCode.lean`, `Prysm/ValidatorBalance/EncoderCode.lean`, `Prysm/VoluntaryExit/EncoderCode.lean`.
-/

namespace Prysm.BlobIdentifier

/-- `(*v1alpha1.BlobIdentifier).MarshalSSZTo`. -/
def Code.marshalSSZTo : Program := include_x64_code "../prysm/go1.26.10/link-set/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlobIdentifier.MarshalSSZTo.S"

end Prysm.BlobIdentifier
