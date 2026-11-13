#!/bin/sh
# Regenerate the committed generated files (run from anywhere; paths are relative to fv/kraken):
# three development-set files, then the two files of the BeaconBlockHeader hold-out (one run each), then
# the output of the generator extension for a 32-byte field at SSZ offset 0 (Eth1Data, development data for the extension; not a hold-out run).
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
$G uint64 --S $N/github.com_OffchainLabs_prysm_v7_consensus_types_primitives.CommitteeIndex.UnmarshalSSZ.S --const unmarshalSSZ --name Decode.generated_accept --same-as Prysm.CommitteeIndex.Decode.accept --imports Codec.Uint64Decoder,Prysm.Slot.DecodeAccept --open Prysm.CommitteeIndex.Code > lean/Prysm/CommitteeIndex/GeneratedDecodeAccept.lean
$G decoder --S $N/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttestationData.UnmarshalSSZ.S --const unmarshalSSZ --ir prysm/ir/ir-mainnet.json --type v1alpha1.AttestationData --prefix Decode.generated_root --imports Codec.Bytes32Decode,Prysm.AttestationData.Code --open Prysm.AttestationData.Code > lean/Prysm/AttestationData/GeneratedDecodeRootFieldSegments.lean
$G decoder --S prysm/go1.26.10/link-set/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Checkpoint.UnmarshalSSZ.S --const unmarshalSSZ --ir prysm/ir/ir-mainnet.json --type v1alpha1.Checkpoint --prefix Decode.generated_root --imports Codec.Bytes32Decode,Prysm.Checkpoint.Code --open Prysm.Checkpoint.Code > lean/Prysm/Checkpoint/GeneratedDecodeRootFieldSegments.lean
# BeaconBlockHeader hold-out: ValidatorIndex and BeaconBlockHeader (opened 2026-11-10T17:53:24Z under the method freeze 56dfc27; raw output committed unedited).
B=prysm/go1.26.10/link-set/norm
$G uint64 --S $B/github.com_OffchainLabs_prysm_v7_consensus_types_primitives.ValidatorIndex.UnmarshalSSZ.S --const unmarshalSSZ --name Decode.generated_accept --imports Codec.Uint64Decoder,Prysm.BeaconBlockHeader.Code --open Prysm.ValidatorIndex.Code > lean/Prysm/ValidatorIndex/GeneratedDecodeAccept.lean
$G decoder --S $B/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockHeader.UnmarshalSSZ.S --const unmarshalSSZ --ir prysm/ir/ir-mainnet.json --type v1alpha1.BeaconBlockHeader --prefix Decode.generated_root --imports Codec.Bytes32Decode,Prysm.BeaconBlockHeader.Code --open Prysm.BeaconBlockHeader.Code > lean/Prysm/BeaconBlockHeader/GeneratedDecodeRootFieldSegments.lean
# Eth1Data hold-out (opened 2026-11-11T01:59:11Z): the one run exits 2 and writes nothing (no template for a 32-byte field at SSZ offset 0; record
# prysm/go1.26.10/evidence/eth1-data/gen-e1dec.raw.txt). The empty file of that run was not kept; the GeneratedDecodeRootFieldSegments.lean of Eth1Data
# now is the offset-0 extension output of the last command below. The Eth1Data hold-out command stays as a comment so that `set -e` does not stop this script:
# $G decoder --S prysm/go1.26.10/link-set/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Eth1Data.UnmarshalSSZ.S --const unmarshalSSZ --ir prysm/ir/ir-mainnet.json --type v1alpha1.Eth1Data --prefix Decode.generated_root --imports Codec.Bytes32Decode,Prysm.Eth1Data.Code --open Prysm.Eth1Data.Code > lean/Prysm/Eth1Data/GeneratedDecodeRootFieldSegments.lean
# Generator extension for a 32-byte field at SSZ offset 0 (after both hold-outs were opened; Eth1Data is development data for it).
# The frozen generator's Eth1Data hold-out run above stays the historical negative result. Raw output committed unedited.
$G decoder --S prysm/go1.26.10/link-set/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Eth1Data.UnmarshalSSZ.S --const unmarshalSSZ --ir prysm/ir/ir-mainnet.json --type v1alpha1.Eth1Data --prefix Decode.generated_root --imports Codec.Bytes32Decode,Codec.Bytes32DecodeOffsetZero,Prysm.Eth1Data.Code --open Prysm.Eth1Data.Code > lean/Prysm/Eth1Data/GeneratedDecodeRootFieldSegments.lean
# Generator change after the hold-out of BlobIdentifier and DepositMessage (development work): `decoder --field-segments` on the development
# set (Eth1Data, BlobIdentifier, DepositMessage are in-sample). New files; the files above stay as they are.
H=prysm/go1.26.10/link-set/norm
$G decoder --field-segments --S prysm/go1.26.10/link-set/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Eth1Data.UnmarshalSSZ.S --const unmarshalSSZ --ir prysm/ir/ir-mainnet.json --type v1alpha1.Eth1Data --prefix Decode.generated_field --imports Codec.Bytes32Decode,Codec.Bytes32DecodeOffsetZero,Codec.InlineUint64,Prysm.Eth1Data.Code --open Prysm.Eth1Data.Code > lean/Prysm/Eth1Data/GeneratedDecodeFieldSegments.lean
$G decoder --field-segments --S $H/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlobIdentifier.UnmarshalSSZ.S --const unmarshalSSZ --ir prysm/ir/ir-mainnet.json --type v1alpha1.BlobIdentifier --prefix Decode.generated_field --imports Codec.Bytes32Decode,Codec.Bytes32DecodeOffsetZero,Codec.InlineUint64,Prysm.BlobIdentifier.Code --open Prysm.BlobIdentifier.Code > lean/Prysm/BlobIdentifier/GeneratedDecodeFieldSegments.lean
$G decoder --field-segments --S $H/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DepositMessage.UnmarshalSSZ.S --const unmarshalSSZ --ir prysm/ir/ir-mainnet.json --type v1alpha1.DepositMessage --prefix Decode.generated_field --imports Codec.Bytes32Decode,Codec.FixedBytesDecode,Codec.InlineUint64,Prysm.BlobIdentifier.Code --open Prysm.DepositMessage.Code > lean/Prysm/DepositMessage/GeneratedDecodeFieldSegments.lean
# field-segment composition (`decoder --field-segments --compose`): the whole accept theorem from the generated segments above; the
# statement check is the `_type` identity with the hand theorem (`--same-as`), available for these development
# types only. A hold-out type has no hand theorem: its composed statement would be unchecked.
$G decoder --field-segments --compose --name Decode.accept_generated_composition --same-as Prysm.BlobIdentifier.Decode.accept --S $H/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlobIdentifier.UnmarshalSSZ.S --const unmarshalSSZ --ir prysm/ir/ir-mainnet.json --type v1alpha1.BlobIdentifier --prefix Decode.generated_field --imports Codec.DecoderHeadEpilogue,Prysm.BlobIdentifier.GeneratedDecodeFieldSegments,Prysm.BlobIdentifier.DecodeAccept --open Prysm.BlobIdentifier.Code > lean/Prysm/BlobIdentifier/GeneratedDecodeAcceptComposition.lean
$G decoder --field-segments --compose --name Decode.accept_generated_composition --same-as Prysm.DepositMessage.Decode.accept --S $H/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DepositMessage.UnmarshalSSZ.S --const unmarshalSSZ --ir prysm/ir/ir-mainnet.json --type v1alpha1.DepositMessage --prefix Decode.generated_field --imports Codec.DecoderHeadEpilogue,Prysm.DepositMessage.GeneratedDecodeFieldSegments,Prysm.DepositMessage.DecodeAccept --open Prysm.DepositMessage.Code > lean/Prysm/DepositMessage/GeneratedDecodeAcceptComposition.lean
$G decoder --field-segments --compose --name Decode.accept_generated_composition --same-as Prysm.Eth1Data.Decode.accept --S prysm/go1.26.10/link-set/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Eth1Data.UnmarshalSSZ.S --const unmarshalSSZ --ir prysm/ir/ir-mainnet.json --type v1alpha1.Eth1Data --prefix Decode.generated_field --imports Codec.DecoderHeadEpilogue,Prysm.Eth1Data.GeneratedDecodeFieldSegments,Prysm.Eth1Data.DecodeAccept --open Prysm.Eth1Data.Code > lean/Prysm/Eth1Data/GeneratedDecodeAcceptComposition.lean
# field-segment partial output (BeaconBlockHeader is in-sample): `--field-segments --partial-out`
# writes a Lean module with the covered fields (3 of 5; Slot, ProposerIndex are delegated overlay fields) and
# exits 3 with nothing on stdout. `kindcheck.py` rejects the file; `kindcheck.py --partial` exits 3.
$G decoder --field-segments --partial-out lean/Prysm/BeaconBlockHeader/GeneratedDecodeFieldSegmentsPartial.lean --S $B/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockHeader.UnmarshalSSZ.S --const unmarshalSSZ --ir prysm/ir/ir-mainnet.json --type v1alpha1.BeaconBlockHeader --prefix Decode.generated_field --imports Codec.Bytes32Decode,Prysm.BeaconBlockHeader.Code --open Prysm.BeaconBlockHeader.Code || [ $? -eq 3 ]
# Generator change after the hold-out of Deposit_Data and PendingPartialWithdrawal (development work): `decoder --call-segments` on the development set
# (PendingPartialWithdrawal, Deposit_Data, BeaconBlockHeader, AttestationData are in-sample). New files; the files
# above stay as they are. AttestationData is partial (Source / Target are nested containers): exit 3.
HOLD_OUT=prysm/go1.26.10/link-set/norm
$G decoder --call-segments --S $HOLD_OUT/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingPartialWithdrawal.UnmarshalSSZ.S --const unmarshalSSZ --ir prysm/ir/ir-mainnet.json --type v1alpha1.PendingPartialWithdrawal --prefix Decode.generated_call --imports Prysm.Deposit_Data.Code --open Prysm.PendingPartialWithdrawal.Code > lean/Prysm/PendingPartialWithdrawal/GeneratedDecodeCallSegments.lean
$G decoder --call-segments --S $HOLD_OUT/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Deposit_Data.UnmarshalSSZ.S --const unmarshalSSZ --ir prysm/ir/ir-mainnet.json --type v1alpha1.Deposit_Data --prefix Decode.generated_call --imports Codec.Bytes32Decode,Codec.Bytes32DecodeOffsetZero,Codec.FixedBytesDecode,Codec.FixedBytesDecodePadding,Codec.InlineUint64,Prysm.Deposit_Data.Code --open Prysm.Deposit_Data.Code > lean/Prysm/Deposit_Data/GeneratedDecodeCallSegments.lean
$G decoder --call-segments --S $B/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockHeader.UnmarshalSSZ.S --const unmarshalSSZ --ir prysm/ir/ir-mainnet.json --type v1alpha1.BeaconBlockHeader --prefix Decode.generated_call --imports Codec.Bytes32Decode,Prysm.BeaconBlockHeader.Code --open Prysm.BeaconBlockHeader.Code > lean/Prysm/BeaconBlockHeader/GeneratedDecodeCallSegments.lean
$G decoder --call-segments --partial-out lean/Prysm/AttestationData/GeneratedDecodeCallSegmentsPartial.lean --S $N/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttestationData.UnmarshalSSZ.S --const unmarshalSSZ --ir prysm/ir/ir-mainnet.json --type v1alpha1.AttestationData --prefix Decode.generated_call --imports Codec.Bytes32Decode,Prysm.AttestationData.Code --open Prysm.AttestationData.Code || [ $? -eq 3 ]
# call-segment composition: Deposit_Data (byte / inline-uint64 fields, frame 0x20) with the composed-statement kind
# `decAcceptKind` (`_kind`) and the identity with the hand statement `Prysm.Deposit_Data.Decode.accept_statement`. PendingPartialWithdrawal and
# BeaconBlockHeader (callee fields) are refused by `--compose` (exit 2): their accept theorems are hand compositions.
# Run 1 of this command did not parse: the generator wrote a doc comment before
# `set_option … in`. That raw output is not in the tree; the fixed generator
# writes GeneratedDecodeAcceptComposition.lean.
$G decoder --call-segments --compose --name Decode.accept_generated_composition --same-as-prop Prysm.Deposit_Data.Decode.accept_statement --S $HOLD_OUT/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Deposit_Data.UnmarshalSSZ.S --const unmarshalSSZ --ir prysm/ir/ir-mainnet.json --type v1alpha1.Deposit_Data --prefix Decode.generated_call --imports Codec.DecoderHeadEpilogue,Prysm.Deposit_Data.GeneratedDecodeCallSegments,Prysm.Deposit_Data.Statements --open Prysm.Deposit_Data.Code > lean/Prysm/Deposit_Data/GeneratedDecodeAcceptComposition.lean
# Generator change after the hold-out of PendingConsolidation and SyncCommitteeMessage (development work): `decoder --steps` on the 10 development types
# (all in-sample). New files; the files above stay as they are. AttestationData is partial (Source / Target are nested
# containers): exit 3 with --partial-out.
# Row: Go type name, link set directory, module of the code constants (the code namespace is Prysm.<Go type name>.Code).
P=github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1
E=prysm/go1.26.10/link-set
for row in "Checkpoint norm Prysm.Checkpoint.Code" "BeaconBlockHeader norm Prysm.BeaconBlockHeader.Code" "Eth1Data norm Prysm.Eth1Data.Code" "BlobIdentifier norm Prysm.BlobIdentifier.Code" "DepositMessage norm Prysm.BlobIdentifier.Code" "Deposit_Data norm Prysm.Deposit_Data.Code" "PendingPartialWithdrawal norm Prysm.Deposit_Data.Code" "SyncCommitteeMessage norm Prysm.SyncCommitteeMessage.Code" "PendingConsolidation norm Prysm.SyncCommitteeMessage.Code"; do
  set -- $row
  $G decoder --steps --S $E/$2/$P.$1.UnmarshalSSZ.S --const unmarshalSSZ --ir prysm/ir/ir-mainnet.json --type v1alpha1.$1 --prefix Decode.generated_step --imports $3 --open Prysm.$1.Code > lean/Prysm/$1/GeneratedDecodeSteps.lean
done
$G decoder --steps --partial-out lean/Prysm/AttestationData/GeneratedDecodeStepsPartial.lean --S $N/$P.AttestationData.UnmarshalSSZ.S --const unmarshalSSZ --ir prysm/ir/ir-mainnet.json --type v1alpha1.AttestationData --prefix Decode.generated_step --imports Prysm.AttestationData.Code --open Prysm.AttestationData.Code || [ $? -eq 3 ]
# Generator change after the hold-out of PendingDeposit and PowBlock (development work): `decoder --whole-accept` on the flat development types
# (all in-sample). One run per type; raw output committed unedited. The statement check is the kind (parameters
# recomputed by kindcheck.py rule 12) and, where a hand statement exists, the identity `_statement` / `_same`. Checkpoint:
# kind instance only (the implication `Prysm.Checkpoint.Decode.accept_of_kind` needs the layout `Prysm.Checkpoint.decodeLayout`, whose chunk order differs).
# PendingPartialWithdrawal (interleaved fields) and AttestationData (nested fields) are refused (exit 2, no file).
for row in "Checkpoint norm Prysm.Checkpoint.Code -" "BeaconBlockHeader norm Prysm.BeaconBlockHeader.Code --same-as=Prysm.BeaconBlockHeader.Decode.accept" "Eth1Data norm Prysm.Eth1Data.Code --same-as=Prysm.Eth1Data.Decode.accept" "BlobIdentifier norm Prysm.BlobIdentifier.Code --same-as=Prysm.BlobIdentifier.Decode.accept" "DepositMessage norm Prysm.BlobIdentifier.Code --same-as=Prysm.DepositMessage.Decode.accept" "Deposit_Data norm Prysm.Deposit_Data.Code --same-as-prop=Prysm.Deposit_Data.Decode.accept_statement" "SyncCommitteeMessage norm Prysm.SyncCommitteeMessage.Code --same-as-prop=Prysm.SyncCommitteeMessage.Decode.accept_statement" "PendingConsolidation norm Prysm.SyncCommitteeMessage.Code --same-as-prop=Prysm.PendingConsolidation.Decode.accept_statement" "PendingDeposit norm Prysm.PendingDeposit.Code --same-as-prop=Prysm.PendingDeposit.Decode.accept_statement" "PowBlock norm Prysm.PendingDeposit.Code --same-as-prop=Prysm.PowBlock.Decode.accept_statement" "HistoricalSummary norm Prysm.PendingDeposit.Code -" "SigningData norm Prysm.PendingDeposit.Code -" "SyncAggregatorSelectionData norm Prysm.PendingDeposit.Code -" "ValidatorBalance norm Prysm.PendingDeposit.Code -" "VoluntaryExit norm Prysm.PendingDeposit.Code -"; do
  set -- $row
  X=$4; [ "$X" = - ] && X=""
  $G decoder --whole-accept --S $E/$2/$P.$1.UnmarshalSSZ.S --const unmarshalSSZ --ir prysm/ir/ir-mainnet.json --type v1alpha1.$1 --prefix Decode.generated --imports $3 --open Prysm.$1.Code $X > lean/Prysm/$1/GeneratedDecodeAccept.lean
done
# refused by design (exit 2, nothing on stdout): kept as comments so that `set -e` does not stop this script
# $G decoder --whole-accept --S $E/norm/$P.PendingPartialWithdrawal.UnmarshalSSZ.S --const unmarshalSSZ --ir prysm/ir/ir-mainnet.json --type v1alpha1.PendingPartialWithdrawal --prefix Decode.generated --imports Prysm.Deposit_Data.Code --open Prysm.PendingPartialWithdrawal.Code --same-as-prop=Prysm.PendingPartialWithdrawal.Decode.accept_statement
# $G decoder --whole-accept --S $N/$P.AttestationData.UnmarshalSSZ.S --const unmarshalSSZ --ir prysm/ir/ir-mainnet.json --type v1alpha1.AttestationData --prefix Decode.generated --imports Prysm.AttestationData.Code --open Prysm.AttestationData.Code
# Generator change after the hold-out of PendingDeposit and PowBlock (development work): `encoder --fast-path` on the 16 flat development
# types (all in-sample). One run per type; raw output committed unedited. Encoder FAST PATH only (premises
# len + SizeSSZ <= cap, byte-vector fields of exact length). Statement check: the kind (kindcheck.py rule 13 recomputes
# its parameters) and, for the three hand types, the identity `_statement` (Checkpoint through Prysm.Checkpoint.Encode.fast_path_of_kind).
# Row: Go type name, link set directory, module of the code constants, the hand layout and identity options.
PP=github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1
LT="--hand-layout-src=lean/Prysm/BeaconBlockHeader/EncodeFastPathKindInstances.lean"
for row in "Checkpoint norm Prysm.Checkpoint.Code --hand-layout=Prysm.Checkpoint.encodeLayout --hand-layout-src=lean/Prysm/Checkpoint/EncodeFastPathKindInstances.lean --same-as=Prysm.Checkpoint.Encode.fast_path --same-as-via=Prysm.Checkpoint.Encode.fast_path_of_kind" \
  "BeaconBlockHeader norm Prysm.BeaconBlockHeader.Code --hand-layout=Prysm.BeaconBlockHeader.encodeLayout $LT --same-as=Prysm.BeaconBlockHeader.Encode.fast_path" \
  "Eth1Data norm Prysm.Eth1Data.Code --hand-layout=Prysm.Eth1Data.encodeLayout --hand-layout-src=lean/Prysm/Eth1Data/EncodeFastPathKindInstances.lean --same-as=Prysm.Eth1Data.Encode.fast_path" \
  "BlobIdentifier norm Prysm.BlobIdentifier.EncoderCode" "DepositMessage norm Prysm.DepositMessage.EncoderCode" \
  "Deposit_Data norm Prysm.Deposit_Data.EncoderCode" "PendingPartialWithdrawal norm Prysm.PendingPartialWithdrawal.EncoderCode" \
  "SyncCommitteeMessage norm Prysm.SyncCommitteeMessage.EncoderCode" "PendingConsolidation norm Prysm.PendingConsolidation.EncoderCode" \
  "PendingDeposit norm Prysm.PendingDeposit.EncoderCode" "PowBlock norm Prysm.PowBlock.EncoderCode" \
  "HistoricalSummary norm Prysm.HistoricalSummary.EncoderCode" "SigningData norm Prysm.SigningData.EncoderCode" \
  "SyncAggregatorSelectionData norm Prysm.SyncAggregatorSelectionData.EncoderCode" "ValidatorBalance norm Prysm.ValidatorBalance.EncoderCode" \
  "VoluntaryExit norm Prysm.VoluntaryExit.EncoderCode"; do
  set -- $row
  t=$1; d=$2; o=$3; shift 3
  $G encoder --fast-path --S $E/$d/$PP.$t.MarshalSSZTo.S --const marshalSSZTo --ir prysm/ir/ir-mainnet.json --type v1alpha1.$t --prefix Encode.generated --imports $o --open Prysm.$t.Code "$@" > lean/Prysm/$t/GeneratedEncodeFastPath.lean
done
