#!/bin/sh
# Regenerate the generated files of generator.py that are not in the type list of gen/flat-types/run_generators.sh.
# Run from anywhere; the paths are relative to fv/kraken. Check the outputs with gen/checks/regenerate_and_compare.py.
# Each output is in lean/Prysm/<GoTypeName>/ and its namespace is Prysm.<GoTypeName> (from --type, or for uint64 from the
# name of the .S file).
# The code constant (--const) is the short name in the code namespace that --open opens.
# The prefix of the generated names (--prefix) names the mode:
#   Decode.generated_accept (uint64), Decode.generated (decoder --whole-accept), Encode.generated (encoder --fast-path).
set -e
cd "$(dirname "$0")/../.."
G="python3 -I gen/generator/generator.py"
N=prysm/go1.26.10/link-set/norm
P=github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1
# uint64: the accept path of the uint64 primitive decoders, one run per Go type name.
# The code constants are in Prysm.<GoTypeName>.Code. The statement check is the kind.
for t in ValidatorIndex Epoch Slot CommitteeIndex; do
  $G uint64 --assembly $N/github.com_OffchainLabs_prysm_v7_consensus_types_primitives.$t.UnmarshalSSZ.S --const unmarshalSSZ --name Decode.generated_accept --imports Codec.Uint64Decoder,Prysm.$t.Code --open Prysm.$t.Code > lean/Prysm/$t/GeneratedDecodeAccept.lean
done
# decoder --whole-accept: one run per Go type name. The code constants are in Prysm.<GoTypeName>.Code.
# The statement check is the kind; kindcheck.py rule 12 recomputes its parameters.
# The generator refuses PendingPartialWithdrawal (interleaved fields) and AttestationData (nested containers): exit 2, no file.
for t in BeaconBlockHeader Eth1Data BlobIdentifier DepositMessage Deposit_Data SyncCommitteeMessage PendingConsolidation \
  PendingDeposit PowBlock HistoricalSummary SigningData SyncAggregatorSelectionData ValidatorBalance VoluntaryExit; do
  $G decoder --whole-accept --assembly $N/$P.$t.UnmarshalSSZ.S --const unmarshalSSZ --ir prysm/ir/ir-mainnet.json --type v1alpha1.$t --prefix Decode.generated --imports Prysm.$t.Code --open Prysm.$t.Code > lean/Prysm/$t/GeneratedDecodeAccept.lean
done
# encoder --fast-path: one run per type. Encoder fast path only (premises len + SizeSSZ <= cap, byte-vector fields of
# exact length). The statement check is the kind; kindcheck.py rule 13 recomputes its parameters. For Checkpoint the
# identity `_statement` with the hand statement is a second check, through Prysm.Checkpoint.Encode.fast_path_of_kind.
# Row: Go type name, then the options of the type: the module of its hand layout, the hand layout and, for Checkpoint, the identity.
# The code constants are in Prysm.<GoTypeName>.Code.
for row in "Checkpoint --imports=Prysm.Checkpoint.EncodeFastPathKindInstances --hand-layout=Prysm.Checkpoint.encodeLayout --hand-layout-src=lean/Prysm/Checkpoint/EncodeFastPathKindInstances.lean --same-as=Prysm.Checkpoint.Encode.fast_path --same-as-via=Prysm.Checkpoint.Encode.fast_path_of_kind" \
  "BeaconBlockHeader --imports=Prysm.BeaconBlockHeader.EncodeLayout --hand-layout=Prysm.BeaconBlockHeader.encodeLayout --hand-layout-src=lean/Prysm/BeaconBlockHeader/EncodeLayout.lean" \
  "Eth1Data --imports=Prysm.Eth1Data.EncodeLayout --hand-layout=Prysm.Eth1Data.encodeLayout --hand-layout-src=lean/Prysm/Eth1Data/EncodeLayout.lean" \
  BlobIdentifier DepositMessage Deposit_Data PendingPartialWithdrawal SyncCommitteeMessage PendingConsolidation PendingDeposit \
  PowBlock HistoricalSummary SigningData SyncAggregatorSelectionData ValidatorBalance VoluntaryExit; do
  set -- $row
  t=$1; shift
  $G encoder --fast-path --assembly $N/$P.$t.MarshalSSZTo.S --const marshalSSZTo --ir prysm/ir/ir-mainnet.json --type v1alpha1.$t --prefix Encode.generated --imports Prysm.$t.Code --open Prysm.$t.Code "$@" > lean/Prysm/$t/GeneratedEncodeFastPath.lean
done
