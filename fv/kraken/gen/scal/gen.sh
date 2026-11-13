#!/bin/sh
# Regenerate the committed generated files (run from anywhere; paths are relative to fv/kraken):
# three development-set files, then the two files of the BeaconBlockHeader hold-out (one run each), then
# the output of the generator extension for a 32-byte field at SSZ offset 0 (Eth1Data, development data for the extension; not a hold-out run).
# Gate it like any generator run. Check with the skill's regen_check.sh (see README).
# Each output is in lean/Prysm/<GoTypeName>/ and its namespace is Prysm.<GoTypeName> (from the name of the .S file).
# The code constant (--const) is the short name in the code namespace that --open opens.
# The prefix of the generated names (--prefix) says the generator mode in words:
#   Decode.generated_root (p2dec), Decode.generated_field (--gen2), Decode.generated_call (--gen3),
#   Decode.generated_step (--gen4), Decode.generated (--gen5), Encode.generated (p2enc --gen6).
set -e
cd "$(dirname "$0")/../.."
G="python3 -I gen/scal/scalgen.py"
N=prysm/go1.26.10/e2e/ad/link/norm
$G p1 --S $N/github.com_OffchainLabs_prysm_v7_consensus_types_primitives.CommitteeIndex.UnmarshalSSZ.S --const unmarshalSSZ --name Decode.generated_accept --same-as Prysm.CommitteeIndex.Decode.accept --imports Codec.Uint64Decoder,Prysm.Slot.DecodeAccept --open Prysm.CommitteeIndex.Code > lean/Prysm/CommitteeIndex/GeneratedDecodeAccept.lean
$G p2dec --S $N/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttestationData.UnmarshalSSZ.S --const unmarshalSSZ --ir prysm/ir/ir-mainnet.json --type v1alpha1.AttestationData --prefix Decode.generated_root --imports Codec.Bytes32Decode,Prysm.AttestationData.Code --open Prysm.AttestationData.Code > lean/Prysm/AttestationData/GeneratedDecodeRootFieldSegments.lean
$G p2dec --S prysm/go1.26.10/e2e/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Checkpoint.UnmarshalSSZ.S --const unmarshalSSZ --ir prysm/ir/ir-mainnet.json --type v1alpha1.Checkpoint --prefix Decode.generated_root --imports Codec.Bytes32Decode,Prysm.Checkpoint.Code --open Prysm.Checkpoint.Code > lean/Prysm/Checkpoint/GeneratedDecodeRootFieldSegments.lean
# BeaconBlockHeader hold-out: ValidatorIndex and BeaconBlockHeader (opened 2026-11-10T17:53:24Z under the method freeze 56dfc27; raw output committed unedited).
B=prysm/go1.26.10/e2e/bh/link/norm
$G p1 --S $B/github.com_OffchainLabs_prysm_v7_consensus_types_primitives.ValidatorIndex.UnmarshalSSZ.S --const unmarshalSSZ --name Decode.generated_accept --imports Codec.Uint64Decoder,Prysm.BeaconBlockHeader.Code --open Prysm.ValidatorIndex.Code > lean/Prysm/ValidatorIndex/GeneratedDecodeAccept.lean
$G p2dec --S $B/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockHeader.UnmarshalSSZ.S --const unmarshalSSZ --ir prysm/ir/ir-mainnet.json --type v1alpha1.BeaconBlockHeader --prefix Decode.generated_root --imports Codec.Bytes32Decode,Prysm.BeaconBlockHeader.Code --open Prysm.BeaconBlockHeader.Code > lean/Prysm/BeaconBlockHeader/GeneratedDecodeRootFieldSegments.lean
# Eth1Data hold-out (opened 2026-11-11T01:59:11Z): the one run exits 2 and writes nothing (no template for a 32-byte field at SSZ offset 0; record
# prysm/go1.26.10/e2e/e1/gen-e1dec.raw.txt). The empty file of that run was not kept; the GeneratedDecodeRootFieldSegments.lean of Eth1Data
# now is the offset-0 extension output of the last command below. The Eth1Data hold-out command stays as a comment so that `set -e` does not stop this script:
# $G p2dec --S prysm/go1.26.10/e2e/e1/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Eth1Data.UnmarshalSSZ.S --const unmarshalSSZ --ir prysm/ir/ir-mainnet.json --type v1alpha1.Eth1Data --prefix Decode.generated_root --imports Codec.Bytes32Decode,Prysm.Eth1Data.Code --open Prysm.Eth1Data.Code > lean/Prysm/Eth1Data/GeneratedDecodeRootFieldSegments.lean
# Generator extension for a 32-byte field at SSZ offset 0 (after both hold-outs were opened; Eth1Data is development data for it).
# The frozen generator's Eth1Data hold-out run above stays the historical negative result. Raw output committed unedited.
$G p2dec --S prysm/go1.26.10/e2e/e1/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Eth1Data.UnmarshalSSZ.S --const unmarshalSSZ --ir prysm/ir/ir-mainnet.json --type v1alpha1.Eth1Data --prefix Decode.generated_root --imports Codec.Bytes32Decode,Codec.Bytes32DecodeOffsetZero,Prysm.Eth1Data.Code --open Prysm.Eth1Data.Code > lean/Prysm/Eth1Data/GeneratedDecodeRootFieldSegments.lean
# Generator change after the H3 hold-out (development work): `p2dec --gen2` on the development
# set (Eth1Data, BlobIdentifier, DepositMessage are in-sample). New files; the files above stay as they are.
H=prysm/go1.26.10/e2e/h3/link/norm
$G p2dec --gen2 --S prysm/go1.26.10/e2e/e1/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Eth1Data.UnmarshalSSZ.S --const unmarshalSSZ --ir prysm/ir/ir-mainnet.json --type v1alpha1.Eth1Data --prefix Decode.generated_field --imports Codec.Bytes32Decode,Codec.Bytes32DecodeOffsetZero,Codec.InlineUint64,Prysm.Eth1Data.Code --open Prysm.Eth1Data.Code > lean/Prysm/Eth1Data/GeneratedDecodeFieldSegments.lean
$G p2dec --gen2 --S $H/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlobIdentifier.UnmarshalSSZ.S --const unmarshalSSZ --ir prysm/ir/ir-mainnet.json --type v1alpha1.BlobIdentifier --prefix Decode.generated_field --imports Codec.Bytes32Decode,Codec.Bytes32DecodeOffsetZero,Codec.InlineUint64,Prysm.BlobIdentifier.Code --open Prysm.BlobIdentifier.Code > lean/Prysm/BlobIdentifier/GeneratedDecodeFieldSegments.lean
$G p2dec --gen2 --S $H/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DepositMessage.UnmarshalSSZ.S --const unmarshalSSZ --ir prysm/ir/ir-mainnet.json --type v1alpha1.DepositMessage --prefix Decode.generated_field --imports Codec.Bytes32Decode,Codec.FixedBytesDecode,Codec.InlineUint64,Prysm.BlobIdentifier.Code --open Prysm.DepositMessage.Code > lean/Prysm/DepositMessage/GeneratedDecodeFieldSegments.lean
# GEN2 composition (`p2dec --gen2 --compose`): the whole accept theorem from the generated segments above; the
# statement check is the `_type` identity with the hand theorem (`--same-as`), available for these development
# types only. A hold-out type has no hand theorem: its composed statement would be unchecked.
$G p2dec --gen2 --compose --name Decode.accept_generated_composition --same-as Prysm.BlobIdentifier.Decode.accept --S $H/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlobIdentifier.UnmarshalSSZ.S --const unmarshalSSZ --ir prysm/ir/ir-mainnet.json --type v1alpha1.BlobIdentifier --prefix Decode.generated_field --imports Codec.DecoderHeadEpilogue,Prysm.BlobIdentifier.GeneratedDecodeFieldSegments,Prysm.BlobIdentifier.DecodeAccept --open Prysm.BlobIdentifier.Code > lean/Prysm/BlobIdentifier/GeneratedDecodeAcceptComposition.lean
$G p2dec --gen2 --compose --name Decode.accept_generated_composition --same-as Prysm.DepositMessage.Decode.accept --S $H/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DepositMessage.UnmarshalSSZ.S --const unmarshalSSZ --ir prysm/ir/ir-mainnet.json --type v1alpha1.DepositMessage --prefix Decode.generated_field --imports Codec.DecoderHeadEpilogue,Prysm.DepositMessage.GeneratedDecodeFieldSegments,Prysm.DepositMessage.DecodeAccept --open Prysm.DepositMessage.Code > lean/Prysm/DepositMessage/GeneratedDecodeAcceptComposition.lean
$G p2dec --gen2 --compose --name Decode.accept_generated_composition --same-as Prysm.Eth1Data.Decode.accept --S prysm/go1.26.10/e2e/e1/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Eth1Data.UnmarshalSSZ.S --const unmarshalSSZ --ir prysm/ir/ir-mainnet.json --type v1alpha1.Eth1Data --prefix Decode.generated_field --imports Codec.DecoderHeadEpilogue,Prysm.Eth1Data.GeneratedDecodeFieldSegments,Prysm.Eth1Data.DecodeAccept --open Prysm.Eth1Data.Code > lean/Prysm/Eth1Data/GeneratedDecodeAcceptComposition.lean
# GEN2 partial output (BeaconBlockHeader is in-sample): `--gen2 --partial-out`
# writes a Lean module with the covered fields (3 of 5; Slot, ProposerIndex are delegated overlay fields) and
# exits 3 with nothing on stdout. `kindcheck.py` rejects the file; `kindcheck.py --partial` exits 3.
$G p2dec --gen2 --partial-out lean/Prysm/BeaconBlockHeader/GeneratedDecodeFieldSegmentsPartial.lean --S $B/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockHeader.UnmarshalSSZ.S --const unmarshalSSZ --ir prysm/ir/ir-mainnet.json --type v1alpha1.BeaconBlockHeader --prefix Decode.generated_field --imports Codec.Bytes32Decode,Prysm.BeaconBlockHeader.Code --open Prysm.BeaconBlockHeader.Code || [ $? -eq 3 ]
# Generator change after the H4 hold-out (development work): `p2dec --gen3` on the development set
# (PendingPartialWithdrawal, Deposit_Data, BeaconBlockHeader, AttestationData are in-sample). New files; the files
# above stay as they are. AttestationData is partial (Source / Target are nested containers): exit 3.
H4=prysm/go1.26.10/e2e/h4/link/norm
$G p2dec --gen3 --S $H4/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingPartialWithdrawal.UnmarshalSSZ.S --const unmarshalSSZ --ir prysm/ir/ir-mainnet.json --type v1alpha1.PendingPartialWithdrawal --prefix Decode.generated_call --imports Prysm.Deposit_Data.Code --open Prysm.PendingPartialWithdrawal.Code > lean/Prysm/PendingPartialWithdrawal/GeneratedDecodeCallSegments.lean
$G p2dec --gen3 --S $H4/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Deposit_Data.UnmarshalSSZ.S --const unmarshalSSZ --ir prysm/ir/ir-mainnet.json --type v1alpha1.Deposit_Data --prefix Decode.generated_call --imports Codec.Bytes32Decode,Codec.Bytes32DecodeOffsetZero,Codec.FixedBytesDecode,Codec.FixedBytesDecodePadding,Codec.InlineUint64,Prysm.Deposit_Data.Code --open Prysm.Deposit_Data.Code > lean/Prysm/Deposit_Data/GeneratedDecodeCallSegments.lean
$G p2dec --gen3 --S $B/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockHeader.UnmarshalSSZ.S --const unmarshalSSZ --ir prysm/ir/ir-mainnet.json --type v1alpha1.BeaconBlockHeader --prefix Decode.generated_call --imports Codec.Bytes32Decode,Prysm.BeaconBlockHeader.Code --open Prysm.BeaconBlockHeader.Code > lean/Prysm/BeaconBlockHeader/GeneratedDecodeCallSegments.lean
$G p2dec --gen3 --partial-out lean/Prysm/AttestationData/GeneratedDecodeCallSegmentsPartial.lean --S $N/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttestationData.UnmarshalSSZ.S --const unmarshalSSZ --ir prysm/ir/ir-mainnet.json --type v1alpha1.AttestationData --prefix Decode.generated_call --imports Codec.Bytes32Decode,Prysm.AttestationData.Code --open Prysm.AttestationData.Code || [ $? -eq 3 ]
# GEN3 composition: Deposit_Data (byte / inline-uint64 fields, frame 0x20) with the composed-statement kind
# `decAcceptKind` (`_kind`) and the identity with the hand statement `Prysm.Deposit_Data.Decode.accept_statement`. PendingPartialWithdrawal and
# BeaconBlockHeader (callee fields) are refused by `--compose` (exit 2): their accept theorems are hand compositions.
# Run 1 of this command did not parse: the generator wrote a doc comment before
# `set_option … in`. That raw output is not in the tree; the fixed generator
# writes GeneratedDecodeAcceptComposition.lean.
$G p2dec --gen3 --compose --name Decode.accept_generated_composition --same-as-prop Prysm.Deposit_Data.Decode.accept_statement --S $H4/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Deposit_Data.UnmarshalSSZ.S --const unmarshalSSZ --ir prysm/ir/ir-mainnet.json --type v1alpha1.Deposit_Data --prefix Decode.generated_call --imports Codec.DecoderHeadEpilogue,Prysm.Deposit_Data.GeneratedDecodeCallSegments,Prysm.Deposit_Data.Statements --open Prysm.Deposit_Data.Code > lean/Prysm/Deposit_Data/GeneratedDecodeAcceptComposition.lean
# Generator change after the H5 hold-out (development work): `p2dec --gen4` on the 10 development types
# (all in-sample). New files; the files above stay as they are. AttestationData is partial (Source / Target are nested
# containers): exit 3 with --partial-out.
# Row: Go type name, link set directory, module of the code constants (the code namespace is Prysm.<Go type name>.Code).
P=github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1
E=prysm/go1.26.10/e2e
for row in "Checkpoint link/norm Prysm.Checkpoint.Code" "BeaconBlockHeader bh/link/norm Prysm.BeaconBlockHeader.Code" "Eth1Data e1/link/norm Prysm.Eth1Data.Code" "BlobIdentifier h3/link/norm Prysm.BlobIdentifier.Code" "DepositMessage h3/link/norm Prysm.BlobIdentifier.Code" "Deposit_Data h4/link/norm Prysm.Deposit_Data.Code" "PendingPartialWithdrawal h4/link/norm Prysm.Deposit_Data.Code" "SyncCommitteeMessage h5/link/norm Prysm.SyncCommitteeMessage.Code" "PendingConsolidation h5/link/norm Prysm.SyncCommitteeMessage.Code"; do
  set -- $row
  $G p2dec --gen4 --S $E/$2/$P.$1.UnmarshalSSZ.S --const unmarshalSSZ --ir prysm/ir/ir-mainnet.json --type v1alpha1.$1 --prefix Decode.generated_step --imports $3 --open Prysm.$1.Code > lean/Prysm/$1/GeneratedDecodeSteps.lean
done
$G p2dec --gen4 --partial-out lean/Prysm/AttestationData/GeneratedDecodeStepsPartial.lean --S $N/$P.AttestationData.UnmarshalSSZ.S --const unmarshalSSZ --ir prysm/ir/ir-mainnet.json --type v1alpha1.AttestationData --prefix Decode.generated_step --imports Prysm.AttestationData.Code --open Prysm.AttestationData.Code || [ $? -eq 3 ]
# Generator change after the H6 hold-out (development work): `p2dec --gen5` on the flat development types
# (all in-sample). One run per type; raw output committed unedited. The statement check is the kind (parameters
# recomputed by kindcheck.py rule 12) and, where a hand statement exists, the identity `_stmt` / `_same`. Checkpoint:
# kind instance only (the implication `Prysm.Checkpoint.Decode.accept_of_kind` needs the layout `Prysm.Checkpoint.decodeLayout`, whose chunk order differs).
# PendingPartialWithdrawal (interleaved fields) and AttestationData (nested fields) are refused (exit 2, no file).
for row in "Checkpoint link/norm Prysm.Checkpoint.Code -" "BeaconBlockHeader bh/link/norm Prysm.BeaconBlockHeader.Code --same-as=Prysm.BeaconBlockHeader.Decode.accept" "Eth1Data e1/link/norm Prysm.Eth1Data.Code --same-as=Prysm.Eth1Data.Decode.accept" "BlobIdentifier h3/link/norm Prysm.BlobIdentifier.Code --same-as=Prysm.BlobIdentifier.Decode.accept" "DepositMessage h3/link/norm Prysm.BlobIdentifier.Code --same-as=Prysm.DepositMessage.Decode.accept" "Deposit_Data h4/link/norm Prysm.Deposit_Data.Code --same-as-prop=Prysm.Deposit_Data.Decode.accept_statement" "SyncCommitteeMessage h5/link/norm Prysm.SyncCommitteeMessage.Code --same-as-prop=Prysm.SyncCommitteeMessage.Decode.accept_statement" "PendingConsolidation h5/link/norm Prysm.SyncCommitteeMessage.Code --same-as-prop=Prysm.PendingConsolidation.Decode.accept_statement" "PendingDeposit h6/link/norm Prysm.PendingDeposit.Code --same-as-prop=Prysm.PendingDeposit.Decode.accept_statement" "PowBlock h6/link/norm Prysm.PendingDeposit.Code --same-as-prop=Prysm.PowBlock.Decode.accept_statement" "HistoricalSummary h6/link/norm Prysm.PendingDeposit.Code -" "SigningData h6/link/norm Prysm.PendingDeposit.Code -" "SyncAggregatorSelectionData h6/link/norm Prysm.PendingDeposit.Code -" "ValidatorBalance h6/link/norm Prysm.PendingDeposit.Code -" "VoluntaryExit h6/link/norm Prysm.PendingDeposit.Code -"; do
  set -- $row
  X=$4; [ "$X" = - ] && X=""
  $G p2dec --gen5 --S $E/$2/$P.$1.UnmarshalSSZ.S --const unmarshalSSZ --ir prysm/ir/ir-mainnet.json --type v1alpha1.$1 --prefix Decode.generated --imports $3 --open Prysm.$1.Code $X > lean/Prysm/$1/GeneratedDecodeAccept.lean
done
# refused by design (exit 2, nothing on stdout): kept as comments so that `set -e` does not stop this script
# $G p2dec --gen5 --S $E/h4/link/norm/$P.PendingPartialWithdrawal.UnmarshalSSZ.S --const unmarshalSSZ --ir prysm/ir/ir-mainnet.json --type v1alpha1.PendingPartialWithdrawal --prefix Decode.generated --imports Prysm.Deposit_Data.Code --open Prysm.PendingPartialWithdrawal.Code --same-as-prop=Prysm.PendingPartialWithdrawal.Decode.accept_statement
# $G p2dec --gen5 --S $N/$P.AttestationData.UnmarshalSSZ.S --const unmarshalSSZ --ir prysm/ir/ir-mainnet.json --type v1alpha1.AttestationData --prefix Decode.generated --imports Prysm.AttestationData.Code --open Prysm.AttestationData.Code
# Generator change after the H6 hold-out (development work): `p2enc --gen6` on the 16 flat development
# types (all in-sample). One run per type; raw output committed unedited. Encoder FAST PATH only (premises
# len + SizeSSZ <= cap, byte-vector fields of exact length). Statement check: the kind (kindcheck.py rule 13 recomputes
# its parameters) and, for the three hand types, the identity `_stmt` (Checkpoint through Prysm.Checkpoint.Encode.fast_path_of_kind).
# Row: Go type name, link set directory, module of the code constants, the hand layout and identity options.
PP=github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1
LT="--hand-layout-src=lean/Prysm/BeaconBlockHeader/EncodeFastPathKindInstances.lean"
for row in "Checkpoint link Prysm.Checkpoint.Code --hand-layout=Prysm.Checkpoint.encodeLayout --hand-layout-src=lean/Prysm/Checkpoint/EncodeFastPathKindInstances.lean --same-as=Prysm.Checkpoint.Encode.fast_path --same-as-via=Prysm.Checkpoint.Encode.fast_path_of_kind" \
  "BeaconBlockHeader bh/link Prysm.BeaconBlockHeader.Code --hand-layout=Prysm.BeaconBlockHeader.encodeLayout $LT --same-as=Prysm.BeaconBlockHeader.Encode.fast_path" \
  "Eth1Data e1/link Prysm.Eth1Data.Code --hand-layout=Prysm.Eth1Data.encodeLayout --hand-layout-src=lean/Prysm/Eth1Data/EncodeFastPathKindInstances.lean --same-as=Prysm.Eth1Data.Encode.fast_path" \
  "BlobIdentifier enc2/link Prysm.BlobIdentifier.EncoderCode" "DepositMessage enc2/link Prysm.DepositMessage.EncoderCode" \
  "Deposit_Data enc2/link Prysm.Deposit_Data.EncoderCode" "PendingPartialWithdrawal enc2/link Prysm.PendingPartialWithdrawal.EncoderCode" \
  "SyncCommitteeMessage enc2/link Prysm.SyncCommitteeMessage.EncoderCode" "PendingConsolidation enc2/link Prysm.PendingConsolidation.EncoderCode" \
  "PendingDeposit enc2/link Prysm.PendingDeposit.EncoderCode" "PowBlock enc2/link Prysm.PowBlock.EncoderCode" \
  "HistoricalSummary enc2/link Prysm.HistoricalSummary.EncoderCode" "SigningData enc2/link Prysm.SigningData.EncoderCode" \
  "SyncAggregatorSelectionData enc2/link Prysm.SyncAggregatorSelectionData.EncoderCode" "ValidatorBalance enc2/link Prysm.ValidatorBalance.EncoderCode" \
  "VoluntaryExit enc2/link Prysm.VoluntaryExit.EncoderCode"; do
  set -- $row
  t=$1; d=$2; o=$3; shift 3
  $G p2enc --gen6 --S $E/$d/norm/$PP.$t.MarshalSSZTo.S --const marshalSSZTo --ir prysm/ir/ir-mainnet.json --type v1alpha1.$t --prefix Encode.generated --imports $o --open Prysm.$t.Code "$@" > lean/Prysm/$t/GeneratedEncodeFastPath.lean
done
