#!/bin/sh
# Regenerate the committed generated files (run from anywhere; paths are relative to fv/kraken):
# one development-set file (Checkpoint), then the file of ValidatorIndex.
# Gate it like any generator run. Check with the skill's regen_check.sh (see README).
# Each output is in lean/Prysm/<GoTypeName>/ and its namespace is Prysm.<GoTypeName> (from the name of the .S file).
# The code constant (--const) is the short name in the code namespace that --open opens.
# The prefix of the generated names (--prefix) says the generator mode in words:
#   Decode.generated_root (decoder), Decode.generated_field (--field-segments), Decode.generated_call (--call-segments),
#   Decode.generated_step (--steps), Decode.generated (--whole-accept), Encode.generated (encoder --fast-path).
set -e
cd "$(dirname "$0")/../.."
G="python3 -I gen/generator/generator.py"
N=prysm/go1.26.10/link-set/norm
$G decoder --assembly prysm/go1.26.10/link-set/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Checkpoint.UnmarshalSSZ.S --const unmarshalSSZ --ir prysm/ir/ir-mainnet.json --type v1alpha1.Checkpoint --prefix Decode.generated_root --imports Codec.Bytes32Decode,Prysm.Checkpoint.Code --open Prysm.Checkpoint.Code > lean/Prysm/Checkpoint/GeneratedDecodeRootFieldSegments.lean
# ValidatorIndex (raw output, not edited).
B=prysm/go1.26.10/link-set/norm
$G uint64 --assembly $B/github.com_OffchainLabs_prysm_v7_consensus_types_primitives.ValidatorIndex.UnmarshalSSZ.S --const unmarshalSSZ --name Decode.generated_accept --imports Codec.Uint64Decoder,Prysm.BeaconBlockHeader.Code --open Prysm.ValidatorIndex.Code > lean/Prysm/ValidatorIndex/GeneratedDecodeAccept.lean
# `decoder --field-segments` on the development set (BlobIdentifier is in-sample).
# Separate files; the files above do not change.
H=prysm/go1.26.10/link-set/norm
$G decoder --field-segments --assembly $H/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlobIdentifier.UnmarshalSSZ.S --const unmarshalSSZ --ir prysm/ir/ir-mainnet.json --type v1alpha1.BlobIdentifier --prefix Decode.generated_field --imports Codec.Bytes32Decode,Codec.Bytes32DecodeOffsetZero,Codec.InlineUint64,Prysm.BlobIdentifier.Code --open Prysm.BlobIdentifier.Code > lean/Prysm/BlobIdentifier/GeneratedDecodeFieldSegments.lean
# field-segment composition (`decoder --field-segments --compose`): the whole accept theorem from the generated segments above; the
# statement check is the `_type` identity with the hand theorem (`--same-as`), available for these development
# types only. For a type without a hand theorem, the composed statement would be unchecked.
$G decoder --field-segments --compose --name Decode.accept_generated_composition --same-as Prysm.BlobIdentifier.Decode.accept --assembly $H/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlobIdentifier.UnmarshalSSZ.S --const unmarshalSSZ --ir prysm/ir/ir-mainnet.json --type v1alpha1.BlobIdentifier --prefix Decode.generated_field --imports Codec.DecoderHeadEpilogue,Prysm.BlobIdentifier.GeneratedDecodeFieldSegments,Prysm.BlobIdentifier.DecodeAccept --open Prysm.BlobIdentifier.Code > lean/Prysm/BlobIdentifier/GeneratedDecodeAcceptComposition.lean
# `decoder --steps` on 6 development types
# (all in-sample). Separate files; the files above do not change.
# Row: Go type name, link set directory, module of the code constants (the code namespace is Prysm.<Go type name>.Code).
P=github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1
E=prysm/go1.26.10/link-set
for row in "Checkpoint norm Prysm.Checkpoint.Code" "BlobIdentifier norm Prysm.BlobIdentifier.Code"; do
  set -- $row
  $G decoder --steps --assembly $E/$2/$P.$1.UnmarshalSSZ.S --const unmarshalSSZ --ir prysm/ir/ir-mainnet.json --type v1alpha1.$1 --prefix Decode.generated_step --imports $3 --open Prysm.$1.Code > lean/Prysm/$1/GeneratedDecodeSteps.lean
done
# `decoder --whole-accept` on the flat development types
# (all in-sample). One run per type; raw output committed unedited. The statement check is the kind (parameters
# recomputed by kindcheck.py rule 12) and, where a hand statement exists, the identity `_statement` / `_same`. Checkpoint:
# kind instance only (the implication `Prysm.Checkpoint.Decode.accept_of_kind` needs the layout `Prysm.Checkpoint.decodeLayout`, whose chunk order differs).
# PendingPartialWithdrawal (interleaved fields) and AttestationData (nested fields) are refused (exit 2, no file).
for row in "Checkpoint norm Prysm.Checkpoint.Code -" "BeaconBlockHeader norm Prysm.BeaconBlockHeader.Code -" "Eth1Data norm Prysm.Eth1Data.Code -" "BlobIdentifier norm Prysm.BlobIdentifier.Code --same-as=Prysm.BlobIdentifier.Decode.accept" "DepositMessage norm Prysm.BlobIdentifier.Code -" "Deposit_Data norm Prysm.Deposit_Data.Code -" "SyncCommitteeMessage norm Prysm.SyncCommitteeMessage.Code -" "PendingConsolidation norm Prysm.SyncCommitteeMessage.Code -" "PendingDeposit norm Prysm.PendingDeposit.Code --same-as-prop=Prysm.PendingDeposit.Decode.accept_statement" "PowBlock norm Prysm.PendingDeposit.Code -" "HistoricalSummary norm Prysm.PendingDeposit.Code -" "SigningData norm Prysm.PendingDeposit.Code -" "SyncAggregatorSelectionData norm Prysm.PendingDeposit.Code -" "ValidatorBalance norm Prysm.PendingDeposit.Code -" "VoluntaryExit norm Prysm.PendingDeposit.Code -"; do
  set -- $row
  X=$4; [ "$X" = - ] && X=""
  $G decoder --whole-accept --assembly $E/$2/$P.$1.UnmarshalSSZ.S --const unmarshalSSZ --ir prysm/ir/ir-mainnet.json --type v1alpha1.$1 --prefix Decode.generated --imports $3 --open Prysm.$1.Code $X > lean/Prysm/$1/GeneratedDecodeAccept.lean
done
# refused by design (exit 2, nothing on stdout): kept as comments so that `set -e` does not stop this script
# $G decoder --whole-accept --assembly $E/norm/$P.PendingPartialWithdrawal.UnmarshalSSZ.S --const unmarshalSSZ --ir prysm/ir/ir-mainnet.json --type v1alpha1.PendingPartialWithdrawal --prefix Decode.generated --imports Prysm.Deposit_Data.Code --open Prysm.PendingPartialWithdrawal.Code --same-as-prop=Prysm.PendingPartialWithdrawal.Decode.accept_statement
# $G decoder --whole-accept --assembly $N/$P.AttestationData.UnmarshalSSZ.S --const unmarshalSSZ --ir prysm/ir/ir-mainnet.json --type v1alpha1.AttestationData --prefix Decode.generated --imports Prysm.AttestationData.Code --open Prysm.AttestationData.Code
# `encoder --fast-path` on the 16 flat development
# types (all in-sample). One run per type; raw output committed unedited. Encoder FAST PATH only (premises
# len + SizeSSZ <= cap, byte-vector fields of exact length). Statement check: the kind (kindcheck.py rule 13 recomputes
# its parameters) and, for the three hand types, the identity `_statement` (Checkpoint through Prysm.Checkpoint.Encode.fast_path_of_kind).
# Row: Go type name, link set directory, the modules to import (code constants; for Eth1Data also its hand layout,
# which no other import brings), the hand layout and identity options.
PP=github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1
LT="--hand-layout-src=lean/Prysm/BeaconBlockHeader/EncodeFastPathKindInstances.lean"
for row in "Checkpoint norm Prysm.Checkpoint.Code --hand-layout=Prysm.Checkpoint.encodeLayout --hand-layout-src=lean/Prysm/Checkpoint/EncodeFastPathKindInstances.lean --same-as=Prysm.Checkpoint.Encode.fast_path --same-as-via=Prysm.Checkpoint.Encode.fast_path_of_kind" \
  "BeaconBlockHeader norm Prysm.BeaconBlockHeader.Code --hand-layout=Prysm.BeaconBlockHeader.encodeLayout $LT --same-as=Prysm.BeaconBlockHeader.Encode.fast_path" \
  "Eth1Data norm Prysm.Eth1Data.Code,Prysm.Eth1Data.EncodeFastPathKindInstances --hand-layout=Prysm.Eth1Data.encodeLayout --hand-layout-src=lean/Prysm/Eth1Data/EncodeFastPathKindInstances.lean --same-as=Prysm.Eth1Data.Encode.fast_path" \
  "BlobIdentifier norm Prysm.BlobIdentifier.EncoderCode" "DepositMessage norm Prysm.DepositMessage.EncoderCode" \
  "Deposit_Data norm Prysm.Deposit_Data.EncoderCode" "PendingPartialWithdrawal norm Prysm.PendingPartialWithdrawal.EncoderCode" \
  "SyncCommitteeMessage norm Prysm.SyncCommitteeMessage.EncoderCode" "PendingConsolidation norm Prysm.PendingConsolidation.EncoderCode" \
  "PendingDeposit norm Prysm.PendingDeposit.EncoderCode" "PowBlock norm Prysm.PowBlock.EncoderCode" \
  "HistoricalSummary norm Prysm.HistoricalSummary.EncoderCode" "SigningData norm Prysm.SigningData.EncoderCode" \
  "SyncAggregatorSelectionData norm Prysm.SyncAggregatorSelectionData.EncoderCode" "ValidatorBalance norm Prysm.ValidatorBalance.EncoderCode" \
  "VoluntaryExit norm Prysm.VoluntaryExit.EncoderCode"; do
  set -- $row
  t=$1; d=$2; o=$3; shift 3
  $G encoder --fast-path --assembly $E/$d/$PP.$t.MarshalSSZTo.S --const marshalSSZTo --ir prysm/ir/ir-mainnet.json --type v1alpha1.$t --prefix Encode.generated --imports $o --open Prysm.$t.Code "$@" > lean/Prysm/$t/GeneratedEncodeFastPath.lean
done
