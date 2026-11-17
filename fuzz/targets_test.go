package fuzz

import (
	"testing"

	v1 "github.com/OffchainLabs/prysm/v7/proto/engine/v1"
	eth "github.com/OffchainLabs/prysm/v7/proto/prysm/v1alpha1"
)

// One target for each Prysm type that stands for an EthLib container at Fulu
// or Gloas. The name of a target is the name of the Go type.
//
// BuilderEntry and BuilderConfig have no target. EthLib reads BuilderEntry.url
// as UTF-8 text, but its SSZ type is a byte list, so EthLib rejects more.

// Types that Fulu and Gloas share.
func FuzzAttestationData(f *testing.F) { run[eth.AttestationData](f, "AttestationData", fulu, gloas) }
func FuzzBeaconBlockHeader(f *testing.F) {
	run[eth.BeaconBlockHeader](f, "BeaconBlockHeader", fulu, gloas)
}
func FuzzCheckpoint(f *testing.F)     { run[eth.Checkpoint](f, "Checkpoint", fulu, gloas) }
func FuzzDeposit(f *testing.F)        { run[eth.Deposit](f, "Deposit", fulu, gloas) }
func FuzzDepositMessage(f *testing.F) { run[eth.DepositMessage](f, "DepositMessage", fulu, gloas) }
func FuzzDepositData(f *testing.F)    { run[eth.Deposit_Data](f, "DepositData", fulu, gloas) }
func FuzzEth1Data(f *testing.F)       { run[eth.Eth1Data](f, "Eth1Data", fulu, gloas) }
func FuzzFork(f *testing.F)           { run[eth.Fork](f, "Fork", fulu, gloas) }
func FuzzForkData(f *testing.F)       { run[eth.ForkData](f, "ForkData", fulu, gloas) }
func FuzzProposerSlashing(f *testing.F) {
	run[eth.ProposerSlashing](f, "ProposerSlashing", fulu, gloas)
}
func FuzzSignedBeaconBlockHeader(f *testing.F) {
	run[eth.SignedBeaconBlockHeader](f, "SignedBeaconBlockHeader", fulu, gloas)
}
func FuzzSignedVoluntaryExit(f *testing.F) {
	run[eth.SignedVoluntaryExit](f, "SignedVoluntaryExit", fulu, gloas)
}
func FuzzSigningData(f *testing.F)   { run[eth.SigningData](f, "SigningData", fulu, gloas) }
func FuzzValidator(f *testing.F)     { run[eth.Validator](f, "Validator", fulu, gloas) }
func FuzzVoluntaryExit(f *testing.F) { run[eth.VoluntaryExit](f, "VoluntaryExit", fulu, gloas) }
func FuzzSyncCommitteeMessage(f *testing.F) {
	run[eth.SyncCommitteeMessage](f, "SyncCommitteeMessage", fulu, gloas)
}
func FuzzSyncCommitteeContribution(f *testing.F) {
	run[eth.SyncCommitteeContribution](f, "SyncCommitteeContribution", fulu, gloas)
}
func FuzzContributionAndProof(f *testing.F) {
	run[eth.ContributionAndProof](f, "ContributionAndProof", fulu, gloas)
}
func FuzzSignedContributionAndProof(f *testing.F) {
	run[eth.SignedContributionAndProof](f, "SignedContributionAndProof", fulu, gloas)
}
func FuzzSingleAttestation(f *testing.F) {
	run[eth.SingleAttestation](f, "SingleAttestation", fulu, gloas)
}
func FuzzSyncAggregate(f *testing.F) { run[eth.SyncAggregate](f, "SyncAggregate", fulu, gloas) }
func FuzzSyncAggregatorSelectionData(f *testing.F) {
	run[eth.SyncAggregatorSelectionData](f, "SyncAggregatorSelectionData", fulu, gloas)
}
func FuzzSyncCommittee(f *testing.F)    { run[eth.SyncCommittee](f, "SyncCommittee", fulu, gloas) }
func FuzzPowBlock(f *testing.F)         { run[eth.PowBlock](f, "PowBlock", fulu, gloas) }
func FuzzEngineWithdrawal(f *testing.F) { run[v1.Withdrawal](f, "Withdrawal", fulu, gloas) }
func FuzzHistoricalSummary(f *testing.F) {
	run[eth.HistoricalSummary](f, "HistoricalSummary", fulu, gloas)
}
func FuzzBLSToExecutionChange(f *testing.F) {
	run[eth.BLSToExecutionChange](f, "BLSToExecutionChange", fulu, gloas)
}
func FuzzSignedBLSToExecutionChange(f *testing.F) {
	run[eth.SignedBLSToExecutionChange](f, "SignedBLSToExecutionChange", fulu, gloas)
}
func FuzzPendingDeposit(f *testing.F) { run[eth.PendingDeposit](f, "PendingDeposit", fulu, gloas) }
func FuzzPendingPartialWithdrawal(f *testing.F) {
	run[eth.PendingPartialWithdrawal](f, "PendingPartialWithdrawal", fulu, gloas)
}
func FuzzPendingConsolidation(f *testing.F) {
	run[eth.PendingConsolidation](f, "PendingConsolidation", fulu, gloas)
}
func FuzzEngineWithdrawalRequest(f *testing.F) {
	run[v1.WithdrawalRequest](f, "WithdrawalRequest", fulu, gloas)
}
func FuzzEngineDepositRequest(f *testing.F) { run[v1.DepositRequest](f, "DepositRequest", fulu, gloas) }
func FuzzEngineConsolidationRequest(f *testing.F) {
	run[v1.ConsolidationRequest](f, "ConsolidationRequest", fulu, gloas)
}
func FuzzDataColumnsByRootIdentifier(f *testing.F) {
	run[eth.DataColumnsByRootIdentifier](f, "DataColumnsByRootIdentifier", fulu, gloas)
}

// Fulu.
func FuzzEngineExecutionPayloadDeneb(f *testing.F) {
	run[v1.ExecutionPayloadDeneb](f, "ExecutionPayload", fulu)
}
func FuzzEngineExecutionPayloadHeaderDeneb(f *testing.F) {
	run[v1.ExecutionPayloadHeaderDeneb](f, "ExecutionPayloadHeader", fulu)
}
func FuzzAttestationElectra(f *testing.F) { run[eth.AttestationElectra](f, "Attestation", fulu) }
func FuzzAttesterSlashingElectra(f *testing.F) {
	run[eth.AttesterSlashingElectra](f, "AttesterSlashing", fulu)
}
func FuzzAggregateAttestationAndProofElectra(f *testing.F) {
	run[eth.AggregateAttestationAndProofElectra](f, "AggregateAndProof", fulu)
}
func FuzzBeaconBlockElectra(f *testing.F) { run[eth.BeaconBlockElectra](f, "BeaconBlock", fulu) }
func FuzzBeaconBlockBodyElectra(f *testing.F) {
	run[eth.BeaconBlockBodyElectra](f, "BeaconBlockBody", fulu)
}
func FuzzBeaconStateFulu(f *testing.F) { run[eth.BeaconStateFulu](f, "BeaconState", fulu) }
func FuzzIndexedAttestationElectra(f *testing.F) {
	run[eth.IndexedAttestationElectra](f, "IndexedAttestation", fulu)
}
func FuzzSignedAggregateAttestationAndProofElectra(f *testing.F) {
	run[eth.SignedAggregateAttestationAndProofElectra](f, "SignedAggregateAndProof", fulu)
}
func FuzzSignedBeaconBlockElectra(f *testing.F) {
	run[eth.SignedBeaconBlockElectra](f, "SignedBeaconBlock", fulu)
}
func FuzzSignedBeaconBlockFulu(f *testing.F) {
	run[eth.SignedBeaconBlockFulu](f, "SignedBeaconBlock", fulu)
}
func FuzzLightClientOptimisticUpdateDeneb(f *testing.F) {
	run[eth.LightClientOptimisticUpdateDeneb](f, "LightClientOptimisticUpdate", fulu)
}
func FuzzLightClientFinalityUpdateElectra(f *testing.F) {
	run[eth.LightClientFinalityUpdateElectra](f, "LightClientFinalityUpdate", fulu)
}
func FuzzLightClientBootstrapElectra(f *testing.F) {
	run[eth.LightClientBootstrapElectra](f, "LightClientBootstrap", fulu)
}
func FuzzLightClientUpdateElectra(f *testing.F) {
	run[eth.LightClientUpdateElectra](f, "LightClientUpdate", fulu)
}
func FuzzLightClientHeaderDeneb(f *testing.F) {
	run[eth.LightClientHeaderDeneb](f, "LightClientHeader", fulu)
}
func FuzzEngineExecutionRequests(f *testing.F) {
	run[v1.ExecutionRequests](f, "ExecutionRequests", fulu)
}
func FuzzDataColumnSidecar(f *testing.F) { run[eth.DataColumnSidecar](f, "DataColumnSidecar", fulu) }
func FuzzPartialDataColumnHeader(f *testing.F) {
	run[eth.PartialDataColumnHeader](f, "PartialDataColumnHeader", fulu)
}
func FuzzPartialDataColumnPartsMetadata(f *testing.F) {
	run[eth.PartialDataColumnPartsMetadata](f, "PartialDataColumnPartsMetadata", fulu)
}
func FuzzPartialDataColumnSidecar(f *testing.F) {
	run[eth.PartialDataColumnSidecar](f, "PartialDataColumnSidecar", fulu)
}
func FuzzBlindedBeaconBlockElectra(f *testing.F) {
	run[eth.BlindedBeaconBlockElectra](f, "BlindedBeaconBlock", fulu)
}
func FuzzSignedBlindedBeaconBlockElectra(f *testing.F) {
	run[eth.SignedBlindedBeaconBlockElectra](f, "SignedBlindedBeaconBlock", fulu)
}
func FuzzBlindedBeaconBlockFulu(f *testing.F) {
	run[eth.BlindedBeaconBlockFulu](f, "BlindedBeaconBlock", fulu)
}
func FuzzSignedBlindedBeaconBlockFulu(f *testing.F) {
	run[eth.SignedBlindedBeaconBlockFulu](f, "SignedBlindedBeaconBlock", fulu)
}
func FuzzBlindedBeaconBlockBodyElectra(f *testing.F) {
	run[eth.BlindedBeaconBlockBodyElectra](f, "BlindedBeaconBlockBody", fulu)
}
func FuzzBuilderBidElectra(f *testing.F) { run[eth.BuilderBidElectra](f, "BuilderBid", fulu) }
func FuzzSignedBuilderBidElectra(f *testing.F) {
	run[eth.SignedBuilderBidElectra](f, "SignedBuilderBid", fulu)
}
func FuzzValidatorRegistrationV1(f *testing.F) {
	run[eth.ValidatorRegistrationV1](f, "ValidatorRegistrationV1", fulu)
}
func FuzzSignedValidatorRegistrationV1(f *testing.F) {
	run[eth.SignedValidatorRegistrationV1](f, "SignedValidatorRegistrationV1", fulu)
}
func FuzzEngineBlobsBundleV2(f *testing.F) { run[v1.BlobsBundleV2](f, "BlobsBundle", fulu) }
func FuzzEngineExecutionPayloadDenebAndBlobsBundleV2(f *testing.F) {
	run[v1.ExecutionPayloadDenebAndBlobsBundleV2](f, "ExecutionPayloadAndBlobsBundle", fulu)
}

// Gloas.
func FuzzExecutionPayloadBid(f *testing.F) {
	run[eth.ExecutionPayloadBid](f, "ExecutionPayloadBid", gloas)
}
func FuzzSignedExecutionPayloadBid(f *testing.F) {
	run[eth.SignedExecutionPayloadBid](f, "SignedExecutionPayloadBid", gloas)
}
func FuzzPayloadAttestationData(f *testing.F) {
	run[eth.PayloadAttestationData](f, "PayloadAttestationData", gloas)
}
func FuzzPayloadAttestation(f *testing.F) {
	run[eth.PayloadAttestation](f, "PayloadAttestation", gloas)
}
func FuzzPayloadAttestationMessage(f *testing.F) {
	run[eth.PayloadAttestationMessage](f, "PayloadAttestationMessage", gloas)
}
func FuzzBeaconBlockGloas(f *testing.F) { run[eth.BeaconBlockGloas](f, "BeaconBlock", gloas) }
func FuzzBeaconBlockBodyGloas(f *testing.F) {
	run[eth.BeaconBlockBodyGloas](f, "BeaconBlockBody", gloas)
}
func FuzzBeaconStateGloas(f *testing.F) { run[eth.BeaconStateGloas](f, "BeaconState", gloas) }
func FuzzBuilder(f *testing.F)          { run[eth.Builder](f, "Builder", gloas) }
func FuzzBuilderPendingPayment(f *testing.F) {
	run[eth.BuilderPendingPayment](f, "BuilderPendingPayment", gloas)
}
func FuzzBuilderPendingWithdrawal(f *testing.F) {
	run[eth.BuilderPendingWithdrawal](f, "BuilderPendingWithdrawal", gloas)
}
func FuzzExecutionPayloadEnvelope(f *testing.F) {
	run[eth.ExecutionPayloadEnvelope](f, "ExecutionPayloadEnvelope", gloas)
}
func FuzzSignedExecutionPayloadEnvelope(f *testing.F) {
	run[eth.SignedExecutionPayloadEnvelope](f, "SignedExecutionPayloadEnvelope", gloas)
}
func FuzzDataColumnSidecarGloas(f *testing.F) {
	run[eth.DataColumnSidecarGloas](f, "DataColumnSidecar", gloas)
}
func FuzzPartialDataColumnGroupID(f *testing.F) {
	run[eth.PartialDataColumnGroupID](f, "PartialDataColumnGroupID", gloas)
}
func FuzzPartialDataColumnSidecarGloas(f *testing.F) {
	run[eth.PartialDataColumnSidecarGloas](f, "PartialDataColumnSidecar", gloas)
}
func FuzzEngineExecutionPayloadGloas(f *testing.F) {
	run[v1.ExecutionPayloadGloas](f, "ExecutionPayload", gloas)
}
func FuzzAttestationGloas(f *testing.F) { run[eth.AttestationGloas](f, "Attestation", gloas) }
func FuzzAttesterSlashingGloas(f *testing.F) {
	run[eth.AttesterSlashingGloas](f, "AttesterSlashing", gloas)
}
func FuzzAggregateAttestationAndProofGloas(f *testing.F) {
	run[eth.AggregateAttestationAndProofGloas](f, "AggregateAndProof", gloas)
}
func FuzzIndexedAttestationGloas(f *testing.F) {
	run[eth.IndexedAttestationGloas](f, "IndexedAttestation", gloas)
}
func FuzzSignedAggregateAttestationAndProofGloas(f *testing.F) {
	run[eth.SignedAggregateAttestationAndProofGloas](f, "SignedAggregateAndProof", gloas)
}
func FuzzSignedBeaconBlockGloas(f *testing.F) {
	run[eth.SignedBeaconBlockGloas](f, "SignedBeaconBlock", gloas)
}
func FuzzLightClientOptimisticUpdateGloas(f *testing.F) {
	run[eth.LightClientOptimisticUpdateGloas](f, "LightClientOptimisticUpdate", gloas)
}
func FuzzLightClientFinalityUpdateGloas(f *testing.F) {
	run[eth.LightClientFinalityUpdateGloas](f, "LightClientFinalityUpdate", gloas)
}
func FuzzLightClientBootstrapGloas(f *testing.F) {
	run[eth.LightClientBootstrapGloas](f, "LightClientBootstrap", gloas)
}
func FuzzLightClientUpdateGloas(f *testing.F) {
	run[eth.LightClientUpdateGloas](f, "LightClientUpdate", gloas)
}
func FuzzLightClientHeaderGloas(f *testing.F) {
	run[eth.LightClientHeaderGloas](f, "LightClientHeader", gloas)
}
func FuzzEngineBuilderDepositRequest(f *testing.F) {
	run[v1.BuilderDepositRequest](f, "BuilderDepositRequest", gloas)
}
func FuzzEngineBuilderExitRequest(f *testing.F) {
	run[v1.BuilderExitRequest](f, "BuilderExitRequest", gloas)
}
func FuzzEngineExecutionRequestsGloas(f *testing.F) {
	run[v1.ExecutionRequestsGloas](f, "ExecutionRequests", gloas)
}
func FuzzProposerPreferences(f *testing.F) {
	run[eth.ProposerPreferences](f, "ProposerPreferences", gloas)
}
func FuzzSignedProposerPreferences(f *testing.F) {
	run[eth.SignedProposerPreferences](f, "SignedProposerPreferences", gloas)
}
func FuzzBuilderPreferences(f *testing.F) {
	run[eth.BuilderPreferences](f, "BuilderPreferences", gloas)
}
func FuzzBuilderPreferencesRequest(f *testing.F) {
	run[eth.BuilderPreferencesRequest](f, "BuilderPreferencesRequest", gloas)
}
func FuzzBuilderRequestAuth(f *testing.F) {
	run[eth.BuilderRequestAuth](f, "BuilderRequestAuth", gloas)
}
func FuzzSignedBuilderRequestAuth(f *testing.F) {
	run[eth.SignedBuilderRequestAuth](f, "SignedBuilderRequestAuth", gloas)
}
