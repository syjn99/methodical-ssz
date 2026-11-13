import Kraken.X64.Parser
import Machine.Include

/-!
# Code of the set of 24 flat types (Go 1.26.10 ELF `c6403c02…911e`)

Each constant includes a `.S` file of `fv/kraken/prysm/go1.26.10/e2e/f24/link/norm`
(`link/conv.py --norm` of the same ELF as `Prysm.Checkpoint.Code`, `Prysm.PendingDeposit.Code` and `Prysm.BlobIdentifier.EncoderCode`;
`link/check.py` (a)–(f) PASS in `../RESULT`, bundle `942b10be…`). The decoder and the encoder of each of the
24 flat fixed-size types outside the development population.
Code constants only: no theorem, no contract. Hand-written include file (not generator
output; the text of `Enc2Code.lean` with the function set changed).
Limit: the directory `f24/link/norm` is not a Lake `input_dir` of the `E2eScal` library (a lakefile change
needs approval), so Lake does not rebuild these modules when a `.S` file changes. The `.S` files are
bound by the link bundle hash; a cold build is the check after any change.
-/

namespace Prysm.BuilderDepositRequest

/-- `(*v1.BuilderDepositRequest).UnmarshalSSZ`. -/
def Code.unmarshalSSZ : Program := include_x64_rt "../prysm/go1.26.10/e2e/f24/link/norm/github.com_OffchainLabs_prysm_v7_proto_engine_v1.BuilderDepositRequest.UnmarshalSSZ.S"
/-- `(*v1.BuilderDepositRequest).MarshalSSZTo`. -/
def Code.marshalSSZTo : Program := include_x64_rt "../prysm/go1.26.10/e2e/f24/link/norm/github.com_OffchainLabs_prysm_v7_proto_engine_v1.BuilderDepositRequest.MarshalSSZTo.S"
/-- `(*v1.BuilderExitRequest).UnmarshalSSZ`. -/
def _root_.Prysm.BuilderExitRequest.Code.unmarshalSSZ : Program := include_x64_rt "../prysm/go1.26.10/e2e/f24/link/norm/github.com_OffchainLabs_prysm_v7_proto_engine_v1.BuilderExitRequest.UnmarshalSSZ.S"
/-- `(*v1.BuilderExitRequest).MarshalSSZTo`. -/
def _root_.Prysm.BuilderExitRequest.Code.marshalSSZTo : Program := include_x64_rt "../prysm/go1.26.10/e2e/f24/link/norm/github.com_OffchainLabs_prysm_v7_proto_engine_v1.BuilderExitRequest.MarshalSSZTo.S"
/-- `(*v1.ConsolidationRequest).UnmarshalSSZ`. -/
def _root_.Prysm.ConsolidationRequest.Code.unmarshalSSZ : Program := include_x64_rt "../prysm/go1.26.10/e2e/f24/link/norm/github.com_OffchainLabs_prysm_v7_proto_engine_v1.ConsolidationRequest.UnmarshalSSZ.S"
/-- `(*v1.ConsolidationRequest).MarshalSSZTo`. -/
def _root_.Prysm.ConsolidationRequest.Code.marshalSSZTo : Program := include_x64_rt "../prysm/go1.26.10/e2e/f24/link/norm/github.com_OffchainLabs_prysm_v7_proto_engine_v1.ConsolidationRequest.MarshalSSZTo.S"
/-- `(*v1.DepositRequest).UnmarshalSSZ`. -/
def _root_.Prysm.DepositRequest.Code.unmarshalSSZ : Program := include_x64_rt "../prysm/go1.26.10/e2e/f24/link/norm/github.com_OffchainLabs_prysm_v7_proto_engine_v1.DepositRequest.UnmarshalSSZ.S"
/-- `(*v1.DepositRequest).MarshalSSZTo`. -/
def _root_.Prysm.DepositRequest.Code.marshalSSZTo : Program := include_x64_rt "../prysm/go1.26.10/e2e/f24/link/norm/github.com_OffchainLabs_prysm_v7_proto_engine_v1.DepositRequest.MarshalSSZTo.S"
/-- `(*v1.Withdrawal).UnmarshalSSZ`. -/
def _root_.Prysm.Withdrawal.Code.unmarshalSSZ : Program := include_x64_rt "../prysm/go1.26.10/e2e/f24/link/norm/github.com_OffchainLabs_prysm_v7_proto_engine_v1.Withdrawal.UnmarshalSSZ.S"
/-- `(*v1.Withdrawal).MarshalSSZTo`. -/
def _root_.Prysm.Withdrawal.Code.marshalSSZTo : Program := include_x64_rt "../prysm/go1.26.10/e2e/f24/link/norm/github.com_OffchainLabs_prysm_v7_proto_engine_v1.Withdrawal.MarshalSSZTo.S"
/-- `(*v1.WithdrawalRequest).UnmarshalSSZ`. -/
def _root_.Prysm.WithdrawalRequest.Code.unmarshalSSZ : Program := include_x64_rt "../prysm/go1.26.10/e2e/f24/link/norm/github.com_OffchainLabs_prysm_v7_proto_engine_v1.WithdrawalRequest.UnmarshalSSZ.S"
/-- `(*v1.WithdrawalRequest).MarshalSSZTo`. -/
def _root_.Prysm.WithdrawalRequest.Code.marshalSSZTo : Program := include_x64_rt "../prysm/go1.26.10/e2e/f24/link/norm/github.com_OffchainLabs_prysm_v7_proto_engine_v1.WithdrawalRequest.MarshalSSZTo.S"
/-- `(*v1alpha1.BLSToExecutionChange).UnmarshalSSZ`. -/
def _root_.Prysm.BLSToExecutionChange.Code.unmarshalSSZ : Program := include_x64_rt "../prysm/go1.26.10/e2e/f24/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BLSToExecutionChange.UnmarshalSSZ.S"
/-- `(*v1alpha1.BLSToExecutionChange).MarshalSSZTo`. -/
def _root_.Prysm.BLSToExecutionChange.Code.marshalSSZTo : Program := include_x64_rt "../prysm/go1.26.10/e2e/f24/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BLSToExecutionChange.MarshalSSZTo.S"
/-- `(*v1alpha1.BeaconBlocksByRangeRequest).UnmarshalSSZ`. -/
def _root_.Prysm.BeaconBlocksByRangeRequest.Code.unmarshalSSZ : Program := include_x64_rt "../prysm/go1.26.10/e2e/f24/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlocksByRangeRequest.UnmarshalSSZ.S"
/-- `(*v1alpha1.BeaconBlocksByRangeRequest).MarshalSSZTo`. -/
def _root_.Prysm.BeaconBlocksByRangeRequest.Code.marshalSSZTo : Program := include_x64_rt "../prysm/go1.26.10/e2e/f24/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlocksByRangeRequest.MarshalSSZTo.S"
/-- `(*v1alpha1.BlobSidecarsByRangeRequest).UnmarshalSSZ`. -/
def _root_.Prysm.BlobSidecarsByRangeRequest.Code.unmarshalSSZ : Program := include_x64_rt "../prysm/go1.26.10/e2e/f24/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlobSidecarsByRangeRequest.UnmarshalSSZ.S"
/-- `(*v1alpha1.BlobSidecarsByRangeRequest).MarshalSSZTo`. -/
def _root_.Prysm.BlobSidecarsByRangeRequest.Code.marshalSSZTo : Program := include_x64_rt "../prysm/go1.26.10/e2e/f24/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlobSidecarsByRangeRequest.MarshalSSZTo.S"
/-- `(*v1alpha1.Builder).UnmarshalSSZ`. -/
def _root_.Prysm.Builder.Code.unmarshalSSZ : Program := include_x64_rt "../prysm/go1.26.10/e2e/f24/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Builder.UnmarshalSSZ.S"
/-- `(*v1alpha1.Builder).MarshalSSZTo`. -/
def _root_.Prysm.Builder.Code.marshalSSZTo : Program := include_x64_rt "../prysm/go1.26.10/e2e/f24/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Builder.MarshalSSZTo.S"
/-- `(*v1alpha1.BuilderPendingWithdrawal).UnmarshalSSZ`. -/
def _root_.Prysm.BuilderPendingWithdrawal.Code.unmarshalSSZ : Program := include_x64_rt "../prysm/go1.26.10/e2e/f24/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BuilderPendingWithdrawal.UnmarshalSSZ.S"
/-- `(*v1alpha1.BuilderPendingWithdrawal).MarshalSSZTo`. -/
def _root_.Prysm.BuilderPendingWithdrawal.Code.marshalSSZTo : Program := include_x64_rt "../prysm/go1.26.10/e2e/f24/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BuilderPendingWithdrawal.MarshalSSZTo.S"
/-- `(*v1alpha1.BuilderPreferences).UnmarshalSSZ`. -/
def _root_.Prysm.BuilderPreferences.Code.unmarshalSSZ : Program := include_x64_rt "../prysm/go1.26.10/e2e/f24/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BuilderPreferences.UnmarshalSSZ.S"
/-- `(*v1alpha1.BuilderPreferences).MarshalSSZTo`. -/
def _root_.Prysm.BuilderPreferences.Code.marshalSSZTo : Program := include_x64_rt "../prysm/go1.26.10/e2e/f24/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BuilderPreferences.MarshalSSZTo.S"
/-- `(*v1alpha1.ENRForkID).UnmarshalSSZ`. -/
def _root_.Prysm.ENRForkID.Code.unmarshalSSZ : Program := include_x64_rt "../prysm/go1.26.10/e2e/f24/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ENRForkID.UnmarshalSSZ.S"
/-- `(*v1alpha1.ENRForkID).MarshalSSZTo`. -/
def _root_.Prysm.ENRForkID.Code.marshalSSZTo : Program := include_x64_rt "../prysm/go1.26.10/e2e/f24/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ENRForkID.MarshalSSZTo.S"
/-- `(*v1alpha1.ExecutionPayloadEnvelopesByRangeRequest).UnmarshalSSZ`. -/
def _root_.Prysm.ExecutionPayloadEnvelopesByRangeRequest.Code.unmarshalSSZ : Program := include_x64_rt "../prysm/go1.26.10/e2e/f24/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ExecutionPayloadEnvelopesByRangeRequest.UnmarshalSSZ.S"
/-- `(*v1alpha1.ExecutionPayloadEnvelopesByRangeRequest).MarshalSSZTo`. -/
def _root_.Prysm.ExecutionPayloadEnvelopesByRangeRequest.Code.marshalSSZTo : Program := include_x64_rt "../prysm/go1.26.10/e2e/f24/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ExecutionPayloadEnvelopesByRangeRequest.MarshalSSZTo.S"
/-- `(*v1alpha1.Fork).UnmarshalSSZ`. -/
def _root_.Prysm.Fork.Code.unmarshalSSZ : Program := include_x64_rt "../prysm/go1.26.10/e2e/f24/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Fork.UnmarshalSSZ.S"
/-- `(*v1alpha1.Fork).MarshalSSZTo`. -/
def _root_.Prysm.Fork.Code.marshalSSZTo : Program := include_x64_rt "../prysm/go1.26.10/e2e/f24/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Fork.MarshalSSZTo.S"
/-- `(*v1alpha1.ForkData).UnmarshalSSZ`. -/
def _root_.Prysm.ForkData.Code.unmarshalSSZ : Program := include_x64_rt "../prysm/go1.26.10/e2e/f24/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ForkData.UnmarshalSSZ.S"
/-- `(*v1alpha1.ForkData).MarshalSSZTo`. -/
def _root_.Prysm.ForkData.Code.marshalSSZTo : Program := include_x64_rt "../prysm/go1.26.10/e2e/f24/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ForkData.MarshalSSZTo.S"
/-- `(*v1alpha1.PartialDataColumnGroupID).UnmarshalSSZ`. -/
def _root_.Prysm.PartialDataColumnGroupID.Code.unmarshalSSZ : Program := include_x64_rt "../prysm/go1.26.10/e2e/f24/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PartialDataColumnGroupID.UnmarshalSSZ.S"
/-- `(*v1alpha1.PartialDataColumnGroupID).MarshalSSZTo`. -/
def _root_.Prysm.PartialDataColumnGroupID.Code.marshalSSZTo : Program := include_x64_rt "../prysm/go1.26.10/e2e/f24/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PartialDataColumnGroupID.MarshalSSZTo.S"
/-- `(*v1alpha1.PayloadAttestationData).UnmarshalSSZ`. -/
def _root_.Prysm.PayloadAttestationData.Code.unmarshalSSZ : Program := include_x64_rt "../prysm/go1.26.10/e2e/f24/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PayloadAttestationData.UnmarshalSSZ.S"
/-- `(*v1alpha1.PayloadAttestationData).MarshalSSZTo`. -/
def _root_.Prysm.PayloadAttestationData.Code.marshalSSZTo : Program := include_x64_rt "../prysm/go1.26.10/e2e/f24/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PayloadAttestationData.MarshalSSZTo.S"
/-- `(*v1alpha1.ProposerPreferences).UnmarshalSSZ`. -/
def _root_.Prysm.ProposerPreferences.Code.unmarshalSSZ : Program := include_x64_rt "../prysm/go1.26.10/e2e/f24/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ProposerPreferences.UnmarshalSSZ.S"
/-- `(*v1alpha1.ProposerPreferences).MarshalSSZTo`. -/
def _root_.Prysm.ProposerPreferences.Code.marshalSSZTo : Program := include_x64_rt "../prysm/go1.26.10/e2e/f24/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ProposerPreferences.MarshalSSZTo.S"
/-- `(*v1alpha1.Status).UnmarshalSSZ`. -/
def _root_.Prysm.Status.Code.unmarshalSSZ : Program := include_x64_rt "../prysm/go1.26.10/e2e/f24/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Status.UnmarshalSSZ.S"
/-- `(*v1alpha1.Status).MarshalSSZTo`. -/
def _root_.Prysm.Status.Code.marshalSSZTo : Program := include_x64_rt "../prysm/go1.26.10/e2e/f24/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Status.MarshalSSZTo.S"
/-- `(*v1alpha1.StatusV2).UnmarshalSSZ`. -/
def _root_.Prysm.StatusV2.Code.unmarshalSSZ : Program := include_x64_rt "../prysm/go1.26.10/e2e/f24/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.StatusV2.UnmarshalSSZ.S"
/-- `(*v1alpha1.StatusV2).MarshalSSZTo`. -/
def _root_.Prysm.StatusV2.Code.marshalSSZTo : Program := include_x64_rt "../prysm/go1.26.10/e2e/f24/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.StatusV2.MarshalSSZTo.S"
/-- `(*v1alpha1.Validator).UnmarshalSSZ`. -/
def _root_.Prysm.Validator.Code.unmarshalSSZ : Program := include_x64_rt "../prysm/go1.26.10/e2e/f24/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Validator.UnmarshalSSZ.S"
/-- `(*v1alpha1.Validator).MarshalSSZTo`. -/
def _root_.Prysm.Validator.Code.marshalSSZTo : Program := include_x64_rt "../prysm/go1.26.10/e2e/f24/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Validator.MarshalSSZTo.S"
/-- `(*v1alpha1.ValidatorIdentity).UnmarshalSSZ`. -/
def _root_.Prysm.ValidatorIdentity.Code.unmarshalSSZ : Program := include_x64_rt "../prysm/go1.26.10/e2e/f24/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorIdentity.UnmarshalSSZ.S"
/-- `(*v1alpha1.ValidatorIdentity).MarshalSSZTo`. -/
def _root_.Prysm.ValidatorIdentity.Code.marshalSSZTo : Program := include_x64_rt "../prysm/go1.26.10/e2e/f24/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorIdentity.MarshalSSZTo.S"
/-- `(*v1alpha1.ValidatorRegistrationV1).UnmarshalSSZ`. -/
def _root_.Prysm.ValidatorRegistrationV1.Code.unmarshalSSZ : Program := include_x64_rt "../prysm/go1.26.10/e2e/f24/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorRegistrationV1.UnmarshalSSZ.S"
/-- `(*v1alpha1.ValidatorRegistrationV1).MarshalSSZTo`. -/
def _root_.Prysm.ValidatorRegistrationV1.Code.marshalSSZTo : Program := include_x64_rt "../prysm/go1.26.10/e2e/f24/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorRegistrationV1.MarshalSSZTo.S"

end Prysm.BuilderDepositRequest
