#!/bin/sh
# Run the generator on the flat types of the list below. It writes nothing into the tree.
# Usage: sh fv/kraken/gen/flat-types/run_generators.sh <out dir>   (from any directory; <out dir> must exist)
# For each type it writes into <out dir>:
#   <GoTypeName>.whole-accept.{lean,rc,stderr,summary.json}  `generator.py decoder --whole-accept` on UnmarshalSSZ
#   <GoTypeName>.fast-path.{lean,rc,stderr,summary.json}     `generator.py encoder --fast-path` on MarshalSSZTo
# The generator refuses some types (rc not 0). The tree has the outputs with rc 0 as
# lean/Prysm/<GoTypeName>/GeneratedDecodeAccept.lean and lean/Prysm/<GoTypeName>/GeneratedEncodeFastPath.lean.
# gen/checks/regenerate_and_compare.py reads the type list of this file and compares those files.
O=$(cd "$1" && pwd)
cd "$(dirname "$0")/../.."
N=prysm/go1.26.10/link-set/norm
while read k t; do
  case $k in v1) PK=github.com_OffchainLabs_prysm_v7_proto_engine_v1;; *) PK=github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1;; esac
  python3 -I -B gen/generator/generator.py decoder --whole-accept --assembly $N/$PK.$t.UnmarshalSSZ.S --const unmarshalSSZ --ir prysm/ir/ir-mainnet.json --type $k.$t --prefix Decode.generated --imports Prysm.$t.Code --open Prysm.$t.Code --summary "$O/$t.whole-accept.summary.json" > "$O/$t.whole-accept.lean" 2> "$O/$t.whole-accept.stderr"
  echo $? > "$O/$t.whole-accept.rc"
  python3 -I -B gen/generator/generator.py encoder --fast-path --assembly $N/$PK.$t.MarshalSSZTo.S --const marshalSSZTo --ir prysm/ir/ir-mainnet.json --type $k.$t --prefix Encode.generated --imports Prysm.$t.Code --open Prysm.$t.Code --summary "$O/$t.fast-path.summary.json" > "$O/$t.fast-path.lean" 2> "$O/$t.fast-path.stderr"
  echo $? > "$O/$t.fast-path.rc"
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
