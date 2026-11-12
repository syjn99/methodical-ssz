#!/bin/sh
# Regenerate the committed generated files (run from anywhere; paths are relative to fv/kraken):
# three development-set files, then the two files of the BeaconBlockHeader hold-out (one run each), then
# the output of the generator extension for a 32-byte field at SSZ offset 0 (Eth1Data, development data for the extension; not a hold-out run).
# Gate it like any generator run. Check with the skill's regen_check.sh (see README).
set -e
cd "$(dirname "$0")/../.."
G="python3 -I gen/scal/scalgen.py"
N=prysm/go1.26.10/e2e/ad/link/norm
$G p1 --S $N/github.com_OffchainLabs_prysm_v7_consensus_types_primitives.CommitteeIndex.UnmarshalSSZ.S --const CiUnmarshal --name ci_unmarshal_accept_main_g --same-as E2eAd.ci_unmarshal_accept_main --imports Codec.Uint64Decoder,E2eAd.Prims --open E2eAd.Code > lean/E2eScal/GenCi.lean
$G p2dec --S $N/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttestationData.UnmarshalSSZ.S --const AdUnmarshal --ir prysm/ir/ir-mainnet.json --type v1alpha1.AttestationData --prefix ad_dec --imports Codec.Bytes32Decode,E2eAd.Code --open E2eAd.Code > lean/E2eScal/GenAdDec.lean
$G p2dec --S prysm/go1.26.10/e2e/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Checkpoint.UnmarshalSSZ.S --const CpUnmarshal --ir prysm/ir/ir-mainnet.json --type v1alpha1.Checkpoint --prefix cp_dec --imports Codec.Bytes32Decode,E2e.Code --open E2e.Code > lean/E2eScal/GenCpDec.lean
# BeaconBlockHeader hold-out: ValidatorIndex and BeaconBlockHeader (opened 2026-11-10T17:53:24Z under the method freeze 56dfc27; raw output committed unedited).
B=prysm/go1.26.10/e2e/bh/link/norm
$G p1 --S $B/github.com_OffchainLabs_prysm_v7_consensus_types_primitives.ValidatorIndex.UnmarshalSSZ.S --const ViUnmarshal --name vi_unmarshal_accept_main_g --imports Codec.Uint64Decoder,E2eScal.BhCode --open E2eScal.BhCode > lean/E2eScal/GenVi.lean
$G p2dec --S $B/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockHeader.UnmarshalSSZ.S --const BhUnmarshal --ir prysm/ir/ir-mainnet.json --type v1alpha1.BeaconBlockHeader --prefix bh_dec --imports Codec.Bytes32Decode,E2eScal.BhCode --open E2eScal.BhCode > lean/E2eScal/GenBhDec.lean
# Eth1Data hold-out (opened 2026-11-11T01:59:11Z): the one run exits 2 and writes nothing (no template for a 32-byte field at SSZ offset 0; record
# prysm/go1.26.10/e2e/e1/gen-e1dec.raw.txt). The empty file of that run was not kept; the GenE1Dec.lean in the library
# glob now is the offset-0 extension output of the last command below. The Eth1Data hold-out command stays as a comment so that `set -e` does not stop this script:
# $G p2dec --S prysm/go1.26.10/e2e/e1/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Eth1Data.UnmarshalSSZ.S --const E1Unmarshal --ir prysm/ir/ir-mainnet.json --type v1alpha1.Eth1Data --prefix e1_dec --imports Codec.Bytes32Decode,E2eScal.E1Code --open E2eScal.E1Code > lean/E2eScal/GenE1Dec.lean
# Generator extension for a 32-byte field at SSZ offset 0 (after both hold-outs were opened; Eth1Data is development data for it).
# The frozen generator's Eth1Data hold-out run above stays the historical negative result. Raw output committed unedited.
$G p2dec --S prysm/go1.26.10/e2e/e1/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Eth1Data.UnmarshalSSZ.S --const E1Unmarshal --ir prysm/ir/ir-mainnet.json --type v1alpha1.Eth1Data --prefix e1_dec --imports Codec.Bytes32Decode,Codec.Bytes32DecodeOffsetZero,E2eScal.E1Code --open E2eScal.E1Code > lean/E2eScal/GenE1Dec.lean
# Generator change after the H3 hold-out (development work): `p2dec --gen2` on the development
# set (Eth1Data, BlobIdentifier, DepositMessage are in-sample). New files; the files above stay as they are.
H=prysm/go1.26.10/e2e/h3/link/norm
$G p2dec --gen2 --S prysm/go1.26.10/e2e/e1/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Eth1Data.UnmarshalSSZ.S --const E1Unmarshal --ir prysm/ir/ir-mainnet.json --type v1alpha1.Eth1Data --prefix e1_g2dec --imports Codec.Bytes32Decode,Codec.Bytes32DecodeOffsetZero,Codec.InlineUint64,E2eScal.E1Code --open E2eScal.E1Code > lean/E2eScal/Gen2E1Dec.lean
$G p2dec --gen2 --S $H/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlobIdentifier.UnmarshalSSZ.S --const BiUnmarshal --ir prysm/ir/ir-mainnet.json --type v1alpha1.BlobIdentifier --prefix bi_g2dec --imports Codec.Bytes32Decode,Codec.Bytes32DecodeOffsetZero,Codec.InlineUint64,E2eScal.H3Code --open E2eScal.H3Code > lean/E2eScal/Gen2BiDec.lean
$G p2dec --gen2 --S $H/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DepositMessage.UnmarshalSSZ.S --const DmUnmarshal --ir prysm/ir/ir-mainnet.json --type v1alpha1.DepositMessage --prefix dm_g2dec --imports Codec.Bytes32Decode,Codec.FixedBytesDecode,Codec.InlineUint64,E2eScal.H3Code --open E2eScal.H3Code > lean/E2eScal/Gen2DmDec.lean
# GEN2 composition (`p2dec --gen2 --compose`): the whole accept theorem from the generated segments above; the
# statement check is the `_type` identity with the hand theorem (`--same-as`), available for these development
# types only. A hold-out type has no hand theorem: its composed statement would be unchecked.
$G p2dec --gen2 --compose --name bi_e2e_accept_main_gc --same-as E2eScal.Bi.bi_e2e_accept_main --S $H/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlobIdentifier.UnmarshalSSZ.S --const BiUnmarshal --ir prysm/ir/ir-mainnet.json --type v1alpha1.BlobIdentifier --prefix bi_g2dec --imports Codec.DecoderHeadEpilogue,E2eScal.Gen2BiDec,E2eScal.BiAccept --open E2eScal.H3Code > lean/E2eScal/Gen2BiAccept.lean
$G p2dec --gen2 --compose --name dm_e2e_accept_main_gc --same-as E2eScal.Dm.dm_e2e_accept_main --S $H/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DepositMessage.UnmarshalSSZ.S --const DmUnmarshal --ir prysm/ir/ir-mainnet.json --type v1alpha1.DepositMessage --prefix dm_g2dec --imports Codec.DecoderHeadEpilogue,E2eScal.Gen2DmDec,E2eScal.DmAccept --open E2eScal.H3Code > lean/E2eScal/Gen2DmAccept.lean
$G p2dec --gen2 --compose --name e1_e2e_accept_main_gc --same-as E2eScal.E1.e1_e2e_accept_main --S prysm/go1.26.10/e2e/e1/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Eth1Data.UnmarshalSSZ.S --const E1Unmarshal --ir prysm/ir/ir-mainnet.json --type v1alpha1.Eth1Data --prefix e1_g2dec --imports Codec.DecoderHeadEpilogue,E2eScal.Gen2E1Dec,E2eScal.E1Accept --open E2eScal.E1Code > lean/E2eScal/Gen2E1Accept.lean
# GEN2 partial output (BeaconBlockHeader is in-sample): `--gen2 --partial-out`
# writes a Lean module with the covered fields (3 of 5; Slot, ProposerIndex are delegated overlay fields) and
# exits 3 with nothing on stdout. `kindcheck.py` rejects the file; `kindcheck.py --partial` exits 3.
$G p2dec --gen2 --partial-out lean/E2eScal/Gen2BhDecPartial.lean --S $B/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockHeader.UnmarshalSSZ.S --const BhUnmarshal --ir prysm/ir/ir-mainnet.json --type v1alpha1.BeaconBlockHeader --prefix bh_g2dec --imports Codec.Bytes32Decode,E2eScal.BhCode --open E2eScal.BhCode || [ $? -eq 3 ]
# Generator change after the H4 hold-out (development work): `p2dec --gen3` on the development set
# (PendingPartialWithdrawal, Deposit_Data, BeaconBlockHeader, AttestationData are in-sample). New files; the files
# above stay as they are. AttestationData is partial (Source / Target are nested containers): exit 3.
H4=prysm/go1.26.10/e2e/h4/link/norm
$G p2dec --gen3 --S $H4/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingPartialWithdrawal.UnmarshalSSZ.S --const PwUnmarshal --ir prysm/ir/ir-mainnet.json --type v1alpha1.PendingPartialWithdrawal --prefix pw_g3dec --imports E2eScal.H4Code --open E2eScal.H4Code > lean/E2eScal/Gen3PwDec.lean
$G p2dec --gen3 --S $H4/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Deposit_Data.UnmarshalSSZ.S --const DdUnmarshal --ir prysm/ir/ir-mainnet.json --type v1alpha1.Deposit_Data --prefix dd_g3dec --imports Codec.Bytes32Decode,Codec.Bytes32DecodeOffsetZero,Codec.FixedBytesDecode,E2eScal.SegNPad,Codec.InlineUint64,E2eScal.H4Code --open E2eScal.H4Code > lean/E2eScal/Gen3DdDec.lean
$G p2dec --gen3 --S $B/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockHeader.UnmarshalSSZ.S --const BhUnmarshal --ir prysm/ir/ir-mainnet.json --type v1alpha1.BeaconBlockHeader --prefix bh_g3dec --imports Codec.Bytes32Decode,E2eScal.BhCode --open E2eScal.BhCode > lean/E2eScal/Gen3BhDec.lean
$G p2dec --gen3 --partial-out lean/E2eScal/Gen3AdDecPartial.lean --S $N/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttestationData.UnmarshalSSZ.S --const AdUnmarshal --ir prysm/ir/ir-mainnet.json --type v1alpha1.AttestationData --prefix ad_g3dec --imports Codec.Bytes32Decode,E2eAd.Code --open E2eAd.Code || [ $? -eq 3 ]
# GEN3 composition: Deposit_Data (byte / inline-uint64 fields, frame 0x20) with the composed-statement kind
# `decAcceptKind` (`_kind`) and the identity with the hand statement `H4.dd_accept_stmt`. PendingPartialWithdrawal and
# BeaconBlockHeader (callee fields) are refused by `--compose` (exit 2): their accept theorems are hand compositions.
# Run 1 of this command (file Gen3DdAccept.lean) did not parse: the generator wrote a doc comment before
# `set_option … in`. That raw output is not in the tree; the fixed generator
# writes Gen3DdAccept2.lean.
$G p2dec --gen3 --compose --name dd_e2e_accept_main_g3 --same-as-prop E2eScal.H4.dd_accept_stmt --S $H4/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Deposit_Data.UnmarshalSSZ.S --const DdUnmarshal --ir prysm/ir/ir-mainnet.json --type v1alpha1.Deposit_Data --prefix dd_g3dec --imports Codec.DecoderHeadEpilogue,E2eScal.Gen3DdDec,E2eScal.H4Stmt --open E2eScal.H4Code > lean/E2eScal/Gen3DdAccept2.lean
# Generator change after the H5 hold-out (development work): `p2dec --gen4` on the 10 development types
# (all in-sample). New files; the files above stay as they are. AttestationData is partial (Source / Target are nested
# containers): exit 3 with --partial-out.
P=github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1
E=prysm/go1.26.10/e2e
for row in "Checkpoint link/norm CpUnmarshal E2e.Code cp Gen4CpDec" "BeaconBlockHeader bh/link/norm BhUnmarshal E2eScal.BhCode bh Gen4BhDec" "Eth1Data e1/link/norm E1Unmarshal E2eScal.E1Code e1 Gen4E1Dec" "BlobIdentifier h3/link/norm BiUnmarshal E2eScal.H3Code bi Gen4BiDec" "DepositMessage h3/link/norm DmUnmarshal E2eScal.H3Code dm Gen4DmDec" "Deposit_Data h4/link/norm DdUnmarshal E2eScal.H4Code dd Gen4DdDec" "PendingPartialWithdrawal h4/link/norm PwUnmarshal E2eScal.H4Code pw Gen4PwDec" "SyncCommitteeMessage h5/link/norm SmUnmarshal E2eScal.H5Code sm Gen4SmDec" "PendingConsolidation h5/link/norm PcUnmarshal E2eScal.H5Code pc Gen4PcDec"; do
  set -- $row
  $G p2dec --gen4 --S $E/$2/$P.$1.UnmarshalSSZ.S --const $3 --ir prysm/ir/ir-mainnet.json --type v1alpha1.$1 --prefix $5_g4dec --imports $4 --open $4 > lean/E2eScal/$6.lean
done
$G p2dec --gen4 --partial-out lean/E2eScal/Gen4AdDecPartial.lean --S $N/$P.AttestationData.UnmarshalSSZ.S --const AdUnmarshal --ir prysm/ir/ir-mainnet.json --type v1alpha1.AttestationData --prefix ad_g4dec --imports E2eAd.Code --open E2eAd.Code || [ $? -eq 3 ]
# Generator change after the H6 hold-out (development work): `p2dec --gen5` on the flat development types
# (all in-sample). One run per type; raw output committed unedited. The statement check is the kind (parameters
# recomputed by kindcheck.py rule 12) and, where a hand statement exists, the identity `_stmt` / `_same`. Checkpoint:
# kind instance only (the implication `cp_accept_of_kind` needs the layout `layCp`, whose chunk order differs).
# PendingPartialWithdrawal (interleaved fields) and AttestationData (nested fields) are refused (exit 2, no file).
for row in "Checkpoint link/norm CpUnmarshal E2e.Code cp Gen5CpDec -" "BeaconBlockHeader bh/link/norm BhUnmarshal E2eScal.BhCode bh Gen5BhDec --same-as=E2eScal.Bh.bh_e2e_accept_main" "Eth1Data e1/link/norm E1Unmarshal E2eScal.E1Code e1 Gen5E1Dec --same-as=E2eScal.E1.e1_e2e_accept_main" "BlobIdentifier h3/link/norm BiUnmarshal E2eScal.H3Code bi Gen5BiDec --same-as=E2eScal.Bi.bi_e2e_accept_main" "DepositMessage h3/link/norm DmUnmarshal E2eScal.H3Code dm Gen5DmDec --same-as=E2eScal.Dm.dm_e2e_accept_main" "Deposit_Data h4/link/norm DdUnmarshal E2eScal.H4Code dd Gen5DdDec --same-as-prop=E2eScal.H4.dd_accept_stmt" "SyncCommitteeMessage h5/link/norm SmUnmarshal E2eScal.H5Code sm Gen5SmDec --same-as-prop=E2eScal.H5.sm_accept_stmt" "PendingConsolidation h5/link/norm PcUnmarshal E2eScal.H5Code pc Gen5PcDec --same-as-prop=E2eScal.H5.pc_accept_stmt" "PendingDeposit h6/link/norm PdUnmarshal E2eScal.H6Code pd Gen5PdDec --same-as-prop=E2eScal.H6.pd_accept_stmt" "PowBlock h6/link/norm PbUnmarshal E2eScal.H6Code pb Gen5PbDec --same-as-prop=E2eScal.H6.pb_accept_stmt" "HistoricalSummary h6/link/norm HsUnmarshal E2eScal.H6Code hs Gen5HsDec -" "SigningData h6/link/norm SdUnmarshal E2eScal.H6Code sd Gen5SdDec -" "SyncAggregatorSelectionData h6/link/norm SaUnmarshal E2eScal.H6Code sa Gen5SaDec -" "ValidatorBalance h6/link/norm VbUnmarshal E2eScal.H6Code vb Gen5VbDec -" "VoluntaryExit h6/link/norm VeUnmarshal E2eScal.H6Code ve Gen5VeDec -"; do
  set -- $row
  X=$7; [ "$X" = - ] && X=""
  $G p2dec --gen5 --S $E/$2/$P.$1.UnmarshalSSZ.S --const $3 --ir prysm/ir/ir-mainnet.json --type v1alpha1.$1 --prefix $5_g5dec --imports $4 --open $4 $X > lean/E2eScal/$6.lean
done
# refused by design (exit 2, nothing on stdout): kept as comments so that `set -e` does not stop this script
# $G p2dec --gen5 --S $E/h4/link/norm/$P.PendingPartialWithdrawal.UnmarshalSSZ.S --const PwUnmarshal --ir prysm/ir/ir-mainnet.json --type v1alpha1.PendingPartialWithdrawal --prefix pw_g5dec --imports E2eScal.H4Code --open E2eScal.H4Code --same-as-prop=E2eScal.H4.pw_accept_stmt
# $G p2dec --gen5 --S $N/$P.AttestationData.UnmarshalSSZ.S --const AdUnmarshal --ir prysm/ir/ir-mainnet.json --type v1alpha1.AttestationData --prefix ad_g5dec --imports E2eAd.Code --open E2eAd.Code
# Generator change after the H6 hold-out (development work): `p2enc --gen6` on the 16 flat development
# types (all in-sample). One run per type; raw output committed unedited. Encoder FAST PATH only (premises
# len + SizeSSZ <= cap, byte-vector fields of exact length). Statement check: the kind (kindcheck.py rule 13 recomputes
# its parameters) and, for the three hand types, the identity `_stmt` (Checkpoint through cp_marshal_of_kind).
PP=github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1
LT="--hand-layout-src=lean/E2eScal/EncTies.lean"
for row in "Checkpoint link CpMarshal E2e.Code cp --hand-layout=E2eScal.layEncCp $LT --same-as=E2e.cp_e2e_marshal_main --same-as-via=E2eScal.cp_marshal_of_kind" \
  "BeaconBlockHeader bh/link BhMarshal E2eScal.BhCode bh --hand-layout=E2eScal.layEncBh $LT --same-as=E2eScal.Bh.bh_e2e_marshal_main" \
  "Eth1Data e1/link E1Marshal E2eScal.E1Code e1 --hand-layout=E2eScal.layEncE1 $LT --same-as=E2eScal.E1.e1_e2e_marshal_main" \
  "BlobIdentifier enc2/link BiMarshal E2eScal.Enc2Code bi" "DepositMessage enc2/link DmMarshal E2eScal.Enc2Code dm" \
  "Deposit_Data enc2/link DdMarshal E2eScal.Enc2Code dd" "PendingPartialWithdrawal enc2/link PwMarshal E2eScal.Enc2Code pw" \
  "SyncCommitteeMessage enc2/link ScMarshal E2eScal.Enc2Code sc" "PendingConsolidation enc2/link PcMarshal E2eScal.Enc2Code pc" \
  "PendingDeposit enc2/link PdMarshal E2eScal.Enc2Code pd" "PowBlock enc2/link PbMarshal E2eScal.Enc2Code pb" \
  "HistoricalSummary enc2/link HsMarshal E2eScal.Enc2Code hs" "SigningData enc2/link SdMarshal E2eScal.Enc2Code sd" \
  "SyncAggregatorSelectionData enc2/link SaMarshal E2eScal.Enc2Code sa" "ValidatorBalance enc2/link VbMarshal E2eScal.Enc2Code vb" \
  "VoluntaryExit enc2/link VeMarshal E2eScal.Enc2Code ve"; do
  set -- $row
  t=$1; d=$2; c=$3; o=$4; px=$5; shift 5
  X=$(printf '%s' "$px" | cut -c1 | tr '[:lower:]' '[:upper:]')$(printf '%s' "$px" | cut -c2-)
  $G p2enc --gen6 --S $E/$d/norm/$PP.$t.MarshalSSZTo.S --const $c --ir prysm/ir/ir-mainnet.json --type v1alpha1.$t --prefix ${px}_g6e --imports $o --open $o "$@" > lean/E2eScal/Gen6${X}Enc.lean
done
