#!/bin/bash
# One gated `decoder --whole-accept` run and one gated `encoder --fast-path` run per type (48 jobs, NN 10..57). No rerun.
# Run records: <GoTypeName>.<mode>.{rc,stdout,stderr,summary.json} in <evidence dir>/raw (mode: whole-accept, fast-path).
# The records of the first run have earlier names; record-names.tsv next to this script maps them to these names.
E=$1; K=$2  # evidence dir (holds g.sh: the gate wrapper), fv/kraken
N=prysm/go1.26.10/link-set/norm; R=$E/raw
NN=10
while read k t; do
  case $k in v1) PK=github.com_OffchainLabs_prysm_v7_proto_engine_v1;; *) PK=github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1;; esac
  [ -e $R/$t.whole-accept.rc ] && { echo "already ran $t whole-accept: refusing a rerun"; exit 9; }
  $E/g.sh $NN "whole-accept $t" 300 $K -- bash -c "python3 -I -B gen/generator/generator.py decoder --whole-accept --S $N/$PK.$t.UnmarshalSSZ.S --const unmarshalSSZ --ir prysm/ir/ir-mainnet.json --type $k.$t --prefix Decode.generated --imports Prysm.$t.Code --open Prysm.$t.Code --summary $R/$t.whole-accept.summary.json > $R/$t.whole-accept.stdout 2> $R/$t.whole-accept.stderr"
  echo $? > $R/$t.whole-accept.rc; NN=$((NN+1))
  [ -e $R/$t.fast-path.rc ] && { echo "already ran $t fast-path: refusing a rerun"; exit 9; }
  $E/g.sh $NN "fast-path $t" 300 $K -- bash -c "python3 -I -B gen/generator/generator.py encoder --fast-path --S $N/$PK.$t.MarshalSSZTo.S --const marshalSSZTo --ir prysm/ir/ir-mainnet.json --type $k.$t --prefix Encode.generated --imports Prysm.$t.Code --open Prysm.$t.Code --summary $R/$t.fast-path.summary.json > $R/$t.fast-path.stdout 2> $R/$t.fast-path.stderr"
  echo $? > $R/$t.fast-path.rc; NN=$((NN+1))
done <<'TYPES'
v1 BuilderDepositRequest
v1 BuilderExitRequest
v1 ConsolidationRequest
v1 DepositRequest
v1 Withdrawal
v1 WithdrawalRequest
v1alpha1 BLSToExecutionChange
v1alpha1 BeaconBlocksByRangeRequest
v1alpha1 BlobSidecarsByRangeRequest
v1alpha1 Builder
v1alpha1 BuilderPendingWithdrawal
v1alpha1 BuilderPreferences
v1alpha1 ENRForkID
v1alpha1 ExecutionPayloadEnvelopesByRangeRequest
v1alpha1 Fork
v1alpha1 ForkData
v1alpha1 PartialDataColumnGroupID
v1alpha1 PayloadAttestationData
v1alpha1 ProposerPreferences
v1alpha1 Status
v1alpha1 StatusV2
v1alpha1 Validator
v1alpha1 ValidatorIdentity
v1alpha1 ValidatorRegistrationV1
TYPES
echo GENERATOR-RUNS-DONE
