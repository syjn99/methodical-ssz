#!/bin/sh
# Regenerate the generated files of generator.py that are not in the type list of gen/flat-types/run_generators.sh.
# Run from anywhere; the paths are relative to fv/kraken. Check the outputs with gen/checks/regenerate_and_compare.py.
# Each output is in lean/Prysm/<GoTypeName>/ and its namespace is Prysm.<GoTypeName> (from --type, or for uint64 from the
# name of the .S file).
# The code constant (--const) is the short name in the code namespace that --open opens.
# The prefix of the generated names (--prefix) names the mode:
#   Decode.generated_root (decoder), Decode.generated_accept (uint64), Decode.generated_step (decoder --steps),
#   Decode.generated (decoder --whole-accept), Encode.generated (encoder --fast-path).
set -e
cd "$(dirname "$0")/../.."
G="python3 -I gen/generator/generator.py"
N=prysm/go1.26.10/link-set/norm
P=github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1
# decoder: the 32-byte field segments of Checkpoint
$G decoder --assembly $N/$P.Checkpoint.UnmarshalSSZ.S --const unmarshalSSZ --ir prysm/ir/ir-mainnet.json --type v1alpha1.Checkpoint --prefix Decode.generated_root --imports Codec.Bytes32Decode,Prysm.Checkpoint.Code --open Prysm.Checkpoint.Code > lean/Prysm/Checkpoint/GeneratedDecodeRootFieldSegments.lean
# uint64: the accept path of the ValidatorIndex decoder
$G uint64 --assembly $N/github.com_OffchainLabs_prysm_v7_consensus_types_primitives.ValidatorIndex.UnmarshalSSZ.S --const unmarshalSSZ --name Decode.generated_accept --imports Codec.Uint64Decoder,Prysm.BeaconBlockHeader.Code --open Prysm.ValidatorIndex.Code > lean/Prysm/ValidatorIndex/GeneratedDecodeAccept.lean
# decoder --steps: the step chain of Checkpoint
$G decoder --steps --assembly $N/$P.Checkpoint.UnmarshalSSZ.S --const unmarshalSSZ --ir prysm/ir/ir-mainnet.json --type v1alpha1.Checkpoint --prefix Decode.generated_step --imports Prysm.Checkpoint.Code --open Prysm.Checkpoint.Code > lean/Prysm/Checkpoint/GeneratedDecodeSteps.lean
# decoder --whole-accept: one run per type. Row: Go type name, module of the code constants.
# The statement check is the kind; kindcheck.py rule 12 recomputes its parameters.
# The generator refuses PendingPartialWithdrawal (interleaved fields) and AttestationData (nested containers): exit 2, no file.
for row in "Checkpoint Prysm.Checkpoint.Code" "BeaconBlockHeader Prysm.BeaconBlockHeader.Code" "Eth1Data Prysm.Eth1Data.Code" \
  "BlobIdentifier Prysm.BlobIdentifier.Code" "DepositMessage Prysm.BlobIdentifier.Code" "Deposit_Data Prysm.Deposit_Data.Code" \
  "SyncCommitteeMessage Prysm.SyncCommitteeMessage.Code" "PendingConsolidation Prysm.SyncCommitteeMessage.Code" \
  "PendingDeposit Prysm.PendingDeposit.Code" "PowBlock Prysm.PendingDeposit.Code" "HistoricalSummary Prysm.PendingDeposit.Code" \
  "SigningData Prysm.PendingDeposit.Code" "SyncAggregatorSelectionData Prysm.PendingDeposit.Code" \
  "ValidatorBalance Prysm.PendingDeposit.Code" "VoluntaryExit Prysm.PendingDeposit.Code"; do
  set -- $row
  $G decoder --whole-accept --assembly $N/$P.$1.UnmarshalSSZ.S --const unmarshalSSZ --ir prysm/ir/ir-mainnet.json --type v1alpha1.$1 --prefix Decode.generated --imports $2 --open Prysm.$1.Code > lean/Prysm/$1/GeneratedDecodeAccept.lean
done
# encoder --fast-path: one run per type. Encoder fast path only (premises len + SizeSSZ <= cap, byte-vector fields of
# exact length). The statement check is the kind; kindcheck.py rule 13 recomputes its parameters. For three types the
# identity `_statement` with the hand statement is a second check (Checkpoint through Prysm.Checkpoint.Encode.fast_path_of_kind).
# Row: Go type name, the modules to import (code constants; for Eth1Data also its hand layout, which no other import
# brings), the hand layout and identity options.
LT="--hand-layout-src=lean/Prysm/BeaconBlockHeader/EncodeFastPathKindInstances.lean"
for row in "Checkpoint Prysm.Checkpoint.Code --hand-layout=Prysm.Checkpoint.encodeLayout --hand-layout-src=lean/Prysm/Checkpoint/EncodeFastPathKindInstances.lean --same-as=Prysm.Checkpoint.Encode.fast_path --same-as-via=Prysm.Checkpoint.Encode.fast_path_of_kind" \
  "BeaconBlockHeader Prysm.BeaconBlockHeader.Code --hand-layout=Prysm.BeaconBlockHeader.encodeLayout $LT --same-as=Prysm.BeaconBlockHeader.Encode.fast_path" \
  "Eth1Data Prysm.Eth1Data.Code,Prysm.Eth1Data.EncodeFastPathKindInstances --hand-layout=Prysm.Eth1Data.encodeLayout --hand-layout-src=lean/Prysm/Eth1Data/EncodeFastPathKindInstances.lean --same-as=Prysm.Eth1Data.Encode.fast_path" \
  "BlobIdentifier Prysm.BlobIdentifier.EncoderCode" "DepositMessage Prysm.DepositMessage.EncoderCode" \
  "Deposit_Data Prysm.Deposit_Data.EncoderCode" "PendingPartialWithdrawal Prysm.PendingPartialWithdrawal.EncoderCode" \
  "SyncCommitteeMessage Prysm.SyncCommitteeMessage.EncoderCode" "PendingConsolidation Prysm.PendingConsolidation.EncoderCode" \
  "PendingDeposit Prysm.PendingDeposit.EncoderCode" "PowBlock Prysm.PowBlock.EncoderCode" \
  "HistoricalSummary Prysm.HistoricalSummary.EncoderCode" "SigningData Prysm.SigningData.EncoderCode" \
  "SyncAggregatorSelectionData Prysm.SyncAggregatorSelectionData.EncoderCode" "ValidatorBalance Prysm.ValidatorBalance.EncoderCode" \
  "VoluntaryExit Prysm.VoluntaryExit.EncoderCode"; do
  set -- $row
  t=$1; o=$2; shift 2
  $G encoder --fast-path --assembly $N/$P.$t.MarshalSSZTo.S --const marshalSSZTo --ir prysm/ir/ir-mainnet.json --type v1alpha1.$t --prefix Encode.generated --imports $o --open Prysm.$t.Code "$@" > lean/Prysm/$t/GeneratedEncodeFastPath.lean
done
