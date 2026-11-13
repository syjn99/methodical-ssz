#!/bin/bash
# Part 1: ONE gated p2dec --gen5 and ONE gated p2enc --gen6 run per type (48 jobs, NN 10..57). No rerun.
E=$1; K=$2  # evidence dir (holds g.sh: the gate wrapper), fv/kraken
N=prysm/go1.26.10/link-set/norm; R=$E/raw
NN=10
while read k t p; do
  X=$(echo $p | sed 's/./\U&/')
  case $k in v1) PK=github.com_OffchainLabs_prysm_v7_proto_engine_v1;; *) PK=github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1;; esac
  [ -e $R/$X.gen5.rc ] && { echo "already ran $X gen5: refusing a rerun"; exit 9; }
  $E/g.sh $NN "gen5 $t" 300 $K -- bash -c "python3 -I -B gen/scal/scalgen.py p2dec --gen5 --S $N/$PK.$t.UnmarshalSSZ.S --const unmarshalSSZ --ir prysm/ir/ir-mainnet.json --type $k.$t --prefix Decode.generated --imports Prysm.$t.Code --open Prysm.$t.Code --summary $R/$X.gen5.summary.json > $R/$X.gen5.stdout 2> $R/$X.gen5.stderr"
  echo $? > $R/$X.gen5.rc; NN=$((NN+1))
  [ -e $R/$X.gen6.rc ] && { echo "already ran $X gen6: refusing a rerun"; exit 9; }
  $E/g.sh $NN "gen6 $t" 300 $K -- bash -c "python3 -I -B gen/scal/scalgen.py p2enc --gen6 --S $N/$PK.$t.MarshalSSZTo.S --const marshalSSZTo --ir prysm/ir/ir-mainnet.json --type $k.$t --prefix Encode.generated --imports Prysm.$t.Code --open Prysm.$t.Code --summary $R/$X.gen6.summary.json > $R/$X.gen6.stdout 2> $R/$X.gen6.stderr"
  echo $? > $R/$X.gen6.rc; NN=$((NN+1))
done <<'TYPES'
v1 BuilderDepositRequest bdr
v1 BuilderExitRequest ber
v1 ConsolidationRequest cnr
v1 DepositRequest dpr
v1 Withdrawal wdl
v1 WithdrawalRequest wdr
v1alpha1 BLSToExecutionChange btc
v1alpha1 BeaconBlocksByRangeRequest bbr
v1alpha1 BlobSidecarsByRangeRequest bsr
v1alpha1 Builder bld
v1alpha1 BuilderPendingWithdrawal bpw
v1alpha1 BuilderPreferences bpf
v1alpha1 ENRForkID efi
v1alpha1 ExecutionPayloadEnvelopesByRangeRequest epr
v1alpha1 Fork frk
v1alpha1 ForkData fkd
v1alpha1 PartialDataColumnGroupID pdc
v1alpha1 PayloadAttestationData pad
v1alpha1 ProposerPreferences ppf
v1alpha1 Status sts
v1alpha1 StatusV2 st2
v1alpha1 Validator vld
v1alpha1 ValidatorIdentity vid
v1alpha1 ValidatorRegistrationV1 vr1
TYPES
echo PART1-RUNS-DONE
