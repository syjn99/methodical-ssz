import Kraken.X64.Parser
import Fk.Include

/-!
# Code of the set of 24 flat types (Go 1.26.10 ELF `c6403c02…911e`)

Each constant includes a `.S` file of `fv/kraken/prysm/go1.26.10/e2e/f24/link/norm`
(`link/conv.py --norm` of the same ELF as `E2e.Code`, `E2eScal.H6Code` and `E2eScal.Enc2Code`;
`link/check.py` (a)–(f) PASS in `../RESULT`, bundle `942b10be…`). The decoder and the encoder of each of the
24 flat fixed-size types outside the development population.
Code constants only: no theorem, no contract. Hand-written include file (not generator
output; the text of `Enc2Code.lean` with the function set changed).
Limit: the directory `f24/link/norm` is not a Lake `input_dir` of the `E2eScal` library (a lakefile change
needs approval), so Lake does not rebuild these modules when a `.S` file changes. The `.S` files are
bound by the link bundle hash; a cold build is the check after any change.
-/

namespace E2eScal.F24Code

/-- `(*v1.BuilderDepositRequest).UnmarshalSSZ`. -/
def BdrUnmarshal : Program := include_x64_rt "../prysm/go1.26.10/e2e/f24/link/norm/github.com_OffchainLabs_prysm_v7_proto_engine_v1.BuilderDepositRequest.UnmarshalSSZ.S"
/-- `(*v1.BuilderDepositRequest).MarshalSSZTo`. -/
def BdrMarshal : Program := include_x64_rt "../prysm/go1.26.10/e2e/f24/link/norm/github.com_OffchainLabs_prysm_v7_proto_engine_v1.BuilderDepositRequest.MarshalSSZTo.S"
/-- `(*v1.BuilderExitRequest).UnmarshalSSZ`. -/
def BerUnmarshal : Program := include_x64_rt "../prysm/go1.26.10/e2e/f24/link/norm/github.com_OffchainLabs_prysm_v7_proto_engine_v1.BuilderExitRequest.UnmarshalSSZ.S"
/-- `(*v1.BuilderExitRequest).MarshalSSZTo`. -/
def BerMarshal : Program := include_x64_rt "../prysm/go1.26.10/e2e/f24/link/norm/github.com_OffchainLabs_prysm_v7_proto_engine_v1.BuilderExitRequest.MarshalSSZTo.S"
/-- `(*v1.ConsolidationRequest).UnmarshalSSZ`. -/
def CnrUnmarshal : Program := include_x64_rt "../prysm/go1.26.10/e2e/f24/link/norm/github.com_OffchainLabs_prysm_v7_proto_engine_v1.ConsolidationRequest.UnmarshalSSZ.S"
/-- `(*v1.ConsolidationRequest).MarshalSSZTo`. -/
def CnrMarshal : Program := include_x64_rt "../prysm/go1.26.10/e2e/f24/link/norm/github.com_OffchainLabs_prysm_v7_proto_engine_v1.ConsolidationRequest.MarshalSSZTo.S"
/-- `(*v1.DepositRequest).UnmarshalSSZ`. -/
def DprUnmarshal : Program := include_x64_rt "../prysm/go1.26.10/e2e/f24/link/norm/github.com_OffchainLabs_prysm_v7_proto_engine_v1.DepositRequest.UnmarshalSSZ.S"
/-- `(*v1.DepositRequest).MarshalSSZTo`. -/
def DprMarshal : Program := include_x64_rt "../prysm/go1.26.10/e2e/f24/link/norm/github.com_OffchainLabs_prysm_v7_proto_engine_v1.DepositRequest.MarshalSSZTo.S"
/-- `(*v1.Withdrawal).UnmarshalSSZ`. -/
def WdlUnmarshal : Program := include_x64_rt "../prysm/go1.26.10/e2e/f24/link/norm/github.com_OffchainLabs_prysm_v7_proto_engine_v1.Withdrawal.UnmarshalSSZ.S"
/-- `(*v1.Withdrawal).MarshalSSZTo`. -/
def WdlMarshal : Program := include_x64_rt "../prysm/go1.26.10/e2e/f24/link/norm/github.com_OffchainLabs_prysm_v7_proto_engine_v1.Withdrawal.MarshalSSZTo.S"
/-- `(*v1.WithdrawalRequest).UnmarshalSSZ`. -/
def WdrUnmarshal : Program := include_x64_rt "../prysm/go1.26.10/e2e/f24/link/norm/github.com_OffchainLabs_prysm_v7_proto_engine_v1.WithdrawalRequest.UnmarshalSSZ.S"
/-- `(*v1.WithdrawalRequest).MarshalSSZTo`. -/
def WdrMarshal : Program := include_x64_rt "../prysm/go1.26.10/e2e/f24/link/norm/github.com_OffchainLabs_prysm_v7_proto_engine_v1.WithdrawalRequest.MarshalSSZTo.S"
/-- `(*v1alpha1.BLSToExecutionChange).UnmarshalSSZ`. -/
def BtcUnmarshal : Program := include_x64_rt "../prysm/go1.26.10/e2e/f24/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BLSToExecutionChange.UnmarshalSSZ.S"
/-- `(*v1alpha1.BLSToExecutionChange).MarshalSSZTo`. -/
def BtcMarshal : Program := include_x64_rt "../prysm/go1.26.10/e2e/f24/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BLSToExecutionChange.MarshalSSZTo.S"
/-- `(*v1alpha1.BeaconBlocksByRangeRequest).UnmarshalSSZ`. -/
def BbrUnmarshal : Program := include_x64_rt "../prysm/go1.26.10/e2e/f24/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlocksByRangeRequest.UnmarshalSSZ.S"
/-- `(*v1alpha1.BeaconBlocksByRangeRequest).MarshalSSZTo`. -/
def BbrMarshal : Program := include_x64_rt "../prysm/go1.26.10/e2e/f24/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlocksByRangeRequest.MarshalSSZTo.S"
/-- `(*v1alpha1.BlobSidecarsByRangeRequest).UnmarshalSSZ`. -/
def BsrUnmarshal : Program := include_x64_rt "../prysm/go1.26.10/e2e/f24/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlobSidecarsByRangeRequest.UnmarshalSSZ.S"
/-- `(*v1alpha1.BlobSidecarsByRangeRequest).MarshalSSZTo`. -/
def BsrMarshal : Program := include_x64_rt "../prysm/go1.26.10/e2e/f24/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlobSidecarsByRangeRequest.MarshalSSZTo.S"
/-- `(*v1alpha1.Builder).UnmarshalSSZ`. -/
def BldUnmarshal : Program := include_x64_rt "../prysm/go1.26.10/e2e/f24/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Builder.UnmarshalSSZ.S"
/-- `(*v1alpha1.Builder).MarshalSSZTo`. -/
def BldMarshal : Program := include_x64_rt "../prysm/go1.26.10/e2e/f24/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Builder.MarshalSSZTo.S"
/-- `(*v1alpha1.BuilderPendingWithdrawal).UnmarshalSSZ`. -/
def BpwUnmarshal : Program := include_x64_rt "../prysm/go1.26.10/e2e/f24/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BuilderPendingWithdrawal.UnmarshalSSZ.S"
/-- `(*v1alpha1.BuilderPendingWithdrawal).MarshalSSZTo`. -/
def BpwMarshal : Program := include_x64_rt "../prysm/go1.26.10/e2e/f24/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BuilderPendingWithdrawal.MarshalSSZTo.S"
/-- `(*v1alpha1.BuilderPreferences).UnmarshalSSZ`. -/
def BpfUnmarshal : Program := include_x64_rt "../prysm/go1.26.10/e2e/f24/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BuilderPreferences.UnmarshalSSZ.S"
/-- `(*v1alpha1.BuilderPreferences).MarshalSSZTo`. -/
def BpfMarshal : Program := include_x64_rt "../prysm/go1.26.10/e2e/f24/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BuilderPreferences.MarshalSSZTo.S"
/-- `(*v1alpha1.ENRForkID).UnmarshalSSZ`. -/
def EfiUnmarshal : Program := include_x64_rt "../prysm/go1.26.10/e2e/f24/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ENRForkID.UnmarshalSSZ.S"
/-- `(*v1alpha1.ENRForkID).MarshalSSZTo`. -/
def EfiMarshal : Program := include_x64_rt "../prysm/go1.26.10/e2e/f24/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ENRForkID.MarshalSSZTo.S"
/-- `(*v1alpha1.ExecutionPayloadEnvelopesByRangeRequest).UnmarshalSSZ`. -/
def EprUnmarshal : Program := include_x64_rt "../prysm/go1.26.10/e2e/f24/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ExecutionPayloadEnvelopesByRangeRequest.UnmarshalSSZ.S"
/-- `(*v1alpha1.ExecutionPayloadEnvelopesByRangeRequest).MarshalSSZTo`. -/
def EprMarshal : Program := include_x64_rt "../prysm/go1.26.10/e2e/f24/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ExecutionPayloadEnvelopesByRangeRequest.MarshalSSZTo.S"
/-- `(*v1alpha1.Fork).UnmarshalSSZ`. -/
def FrkUnmarshal : Program := include_x64_rt "../prysm/go1.26.10/e2e/f24/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Fork.UnmarshalSSZ.S"
/-- `(*v1alpha1.Fork).MarshalSSZTo`. -/
def FrkMarshal : Program := include_x64_rt "../prysm/go1.26.10/e2e/f24/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Fork.MarshalSSZTo.S"
/-- `(*v1alpha1.ForkData).UnmarshalSSZ`. -/
def FkdUnmarshal : Program := include_x64_rt "../prysm/go1.26.10/e2e/f24/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ForkData.UnmarshalSSZ.S"
/-- `(*v1alpha1.ForkData).MarshalSSZTo`. -/
def FkdMarshal : Program := include_x64_rt "../prysm/go1.26.10/e2e/f24/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ForkData.MarshalSSZTo.S"
/-- `(*v1alpha1.PartialDataColumnGroupID).UnmarshalSSZ`. -/
def PdcUnmarshal : Program := include_x64_rt "../prysm/go1.26.10/e2e/f24/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PartialDataColumnGroupID.UnmarshalSSZ.S"
/-- `(*v1alpha1.PartialDataColumnGroupID).MarshalSSZTo`. -/
def PdcMarshal : Program := include_x64_rt "../prysm/go1.26.10/e2e/f24/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PartialDataColumnGroupID.MarshalSSZTo.S"
/-- `(*v1alpha1.PayloadAttestationData).UnmarshalSSZ`. -/
def PadUnmarshal : Program := include_x64_rt "../prysm/go1.26.10/e2e/f24/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PayloadAttestationData.UnmarshalSSZ.S"
/-- `(*v1alpha1.PayloadAttestationData).MarshalSSZTo`. -/
def PadMarshal : Program := include_x64_rt "../prysm/go1.26.10/e2e/f24/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PayloadAttestationData.MarshalSSZTo.S"
/-- `(*v1alpha1.ProposerPreferences).UnmarshalSSZ`. -/
def PpfUnmarshal : Program := include_x64_rt "../prysm/go1.26.10/e2e/f24/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ProposerPreferences.UnmarshalSSZ.S"
/-- `(*v1alpha1.ProposerPreferences).MarshalSSZTo`. -/
def PpfMarshal : Program := include_x64_rt "../prysm/go1.26.10/e2e/f24/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ProposerPreferences.MarshalSSZTo.S"
/-- `(*v1alpha1.Status).UnmarshalSSZ`. -/
def StsUnmarshal : Program := include_x64_rt "../prysm/go1.26.10/e2e/f24/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Status.UnmarshalSSZ.S"
/-- `(*v1alpha1.Status).MarshalSSZTo`. -/
def StsMarshal : Program := include_x64_rt "../prysm/go1.26.10/e2e/f24/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Status.MarshalSSZTo.S"
/-- `(*v1alpha1.StatusV2).UnmarshalSSZ`. -/
def St2Unmarshal : Program := include_x64_rt "../prysm/go1.26.10/e2e/f24/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.StatusV2.UnmarshalSSZ.S"
/-- `(*v1alpha1.StatusV2).MarshalSSZTo`. -/
def St2Marshal : Program := include_x64_rt "../prysm/go1.26.10/e2e/f24/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.StatusV2.MarshalSSZTo.S"
/-- `(*v1alpha1.Validator).UnmarshalSSZ`. -/
def VldUnmarshal : Program := include_x64_rt "../prysm/go1.26.10/e2e/f24/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Validator.UnmarshalSSZ.S"
/-- `(*v1alpha1.Validator).MarshalSSZTo`. -/
def VldMarshal : Program := include_x64_rt "../prysm/go1.26.10/e2e/f24/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Validator.MarshalSSZTo.S"
/-- `(*v1alpha1.ValidatorIdentity).UnmarshalSSZ`. -/
def VidUnmarshal : Program := include_x64_rt "../prysm/go1.26.10/e2e/f24/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorIdentity.UnmarshalSSZ.S"
/-- `(*v1alpha1.ValidatorIdentity).MarshalSSZTo`. -/
def VidMarshal : Program := include_x64_rt "../prysm/go1.26.10/e2e/f24/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorIdentity.MarshalSSZTo.S"
/-- `(*v1alpha1.ValidatorRegistrationV1).UnmarshalSSZ`. -/
def Vr1Unmarshal : Program := include_x64_rt "../prysm/go1.26.10/e2e/f24/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorRegistrationV1.UnmarshalSSZ.S"
/-- `(*v1alpha1.ValidatorRegistrationV1).MarshalSSZTo`. -/
def Vr1Marshal : Program := include_x64_rt "../prysm/go1.26.10/e2e/f24/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorRegistrationV1.MarshalSSZTo.S"

end E2eScal.F24Code
