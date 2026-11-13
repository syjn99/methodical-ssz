import Kraken.X64.Parser
import Machine.Include
import Prysm.BLSToExecutionChange.Code
import Prysm.BeaconBlocksByRangeRequest.Code
import Prysm.BlobSidecarsByRangeRequest.Code
import Prysm.Builder.Code
import Prysm.BuilderExitRequest.Code
import Prysm.BuilderPendingWithdrawal.Code
import Prysm.BuilderPreferences.Code
import Prysm.ConsolidationRequest.Code
import Prysm.DepositRequest.Code
import Prysm.ENRForkID.Code
import Prysm.ExecutionPayloadEnvelopesByRangeRequest.Code
import Prysm.Fork.Code
import Prysm.ForkData.Code
import Prysm.PartialDataColumnGroupID.Code
import Prysm.PayloadAttestationData.Code
import Prysm.ProposerPreferences.Code
import Prysm.Status.Code
import Prysm.StatusV2.Code
import Prysm.Validator.Code
import Prysm.ValidatorIdentity.Code
import Prysm.ValidatorRegistrationV1.Code
import Prysm.Withdrawal.Code
import Prysm.WithdrawalRequest.Code

/-!
# Code of the set of 24 flat types (Go 1.26.10 ELF `c6403c02…911e`)

Each constant includes a `.S` file of `fv/kraken/prysm/go1.26.10/link-set/norm`
(`link/conv.py --norm` of the same ELF as `Prysm.Checkpoint.Code`, `Prysm.PendingDeposit.Code` and `Prysm.BlobIdentifier.EncoderCode`;
`link/check.py` (a)–(f) PASS in `prysm/go1.26.10/link-set/RESULT`). The decoder and the encoder of each of the
24 flat fixed-size types that were not used to develop the proof generators.
Code constants only: no theorem, no contract. Hand-written include file (not generator
output; the text of `Prysm/BlobIdentifier/EncoderCode.lean` with the function set changed).
The directory `prysm/go1.26.10/link-set/norm` is a Lake `input_dir` of the `Prysm` library,
so Lake rebuilds these modules when a `.S` file changes.
After the split of this module, the declarations of the other types are in `Prysm/BLSToExecutionChange/Code.lean`, `Prysm/BeaconBlocksByRangeRequest/Code.lean`, `Prysm/BlobSidecarsByRangeRequest/Code.lean`, `Prysm/Builder/Code.lean`, `Prysm/BuilderExitRequest/Code.lean`, `Prysm/BuilderPendingWithdrawal/Code.lean`, `Prysm/BuilderPreferences/Code.lean`, `Prysm/ConsolidationRequest/Code.lean`, `Prysm/DepositRequest/Code.lean`, `Prysm/ENRForkID/Code.lean`, `Prysm/ExecutionPayloadEnvelopesByRangeRequest/Code.lean`, `Prysm/Fork/Code.lean`, `Prysm/ForkData/Code.lean`, `Prysm/PartialDataColumnGroupID/Code.lean`, `Prysm/PayloadAttestationData/Code.lean`, `Prysm/ProposerPreferences/Code.lean`, `Prysm/Status/Code.lean`, `Prysm/StatusV2/Code.lean`, `Prysm/Validator/Code.lean`, `Prysm/ValidatorIdentity/Code.lean`, `Prysm/ValidatorRegistrationV1/Code.lean`, `Prysm/Withdrawal/Code.lean`, `Prysm/WithdrawalRequest/Code.lean`.
-/

namespace Prysm.BuilderDepositRequest

/-- `(*v1.BuilderDepositRequest).UnmarshalSSZ`. -/
def Code.unmarshalSSZ : Program := include_x64_rt "../prysm/go1.26.10/link-set/norm/github.com_OffchainLabs_prysm_v7_proto_engine_v1.BuilderDepositRequest.UnmarshalSSZ.S"
/-- `(*v1.BuilderDepositRequest).MarshalSSZTo`. -/
def Code.marshalSSZTo : Program := include_x64_rt "../prysm/go1.26.10/link-set/norm/github.com_OffchainLabs_prysm_v7_proto_engine_v1.BuilderDepositRequest.MarshalSSZTo.S"

end Prysm.BuilderDepositRequest
