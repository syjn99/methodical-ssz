#!/bin/sh
# Regenerate the committed generated files (run from anywhere; paths are relative to fv/kraken):
# three development-set files, then the two hold-out H1 files (one run each in gate jobs 299 and 312), then
# the SG-1 extension output (Eth1Data, development data for the extension; not a hold-out run).
# Gate it like any generator run. Check with the skill's regen_check.sh (see README).
set -e
cd "$(dirname "$0")/../.."
G="python3 -I gen/scal/scalgen.py"
N=prysm/go1.26.10/e2e/ad/link/norm
$G p1 --S $N/github.com_OffchainLabs_prysm_v7_consensus_types_primitives.CommitteeIndex.UnmarshalSSZ.S --const CiUnmarshal --name ci_unmarshal_accept_main_g --same-as E2eAd.ci_unmarshal_accept_main --imports E2eScal.P1,E2eAd.Prims --open E2eAd.Code > lean/E2eScal/GenCi.lean
$G p2dec --S $N/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttestationData.UnmarshalSSZ.S --const AdUnmarshal --ir prysm/ir/ir-mainnet.json --type v1alpha1.AttestationData --prefix ad_dec --imports E2eScal.P2Dec,E2eAd.Code --open E2eAd.Code > lean/E2eScal/GenAdDec.lean
$G p2dec --S prysm/go1.26.10/e2e/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Checkpoint.UnmarshalSSZ.S --const CpUnmarshal --ir prysm/ir/ir-mainnet.json --type v1alpha1.Checkpoint --prefix cp_dec --imports E2eScal.P2Dec,E2e.Code --open E2e.Code > lean/E2eScal/GenCpDec.lean
# Hold-out H1 (opened 2026-11-10T17:53:24Z under the method freeze 56dfc27; raw output committed unedited).
B=prysm/go1.26.10/e2e/bh/link/norm
$G p1 --S $B/github.com_OffchainLabs_prysm_v7_consensus_types_primitives.ValidatorIndex.UnmarshalSSZ.S --const ViUnmarshal --name vi_unmarshal_accept_main_g --imports E2eScal.P1,E2eScal.BhCode --open E2eScal.BhCode > lean/E2eScal/GenVi.lean
$G p2dec --S $B/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockHeader.UnmarshalSSZ.S --const BhUnmarshal --ir prysm/ir/ir-mainnet.json --type v1alpha1.BeaconBlockHeader --prefix bh_dec --imports E2eScal.P2Dec,E2eScal.BhCode --open E2eScal.BhCode > lean/E2eScal/GenBhDec.lean
# Hold-out H2 (opened 2026-11-11T01:59:11Z): the one run exits 2 and writes nothing (FINDINGS SG-1; record
# prysm/go1.26.10/e2e/e1/gen-e1dec.raw.txt). The empty file of that run was not kept; the GenE1Dec.lean in the library
# glob now is the SG-1 output of the last command below. The H2 command stays as a comment so that `set -e` does not stop this script:
# $G p2dec --S prysm/go1.26.10/e2e/e1/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Eth1Data.UnmarshalSSZ.S --const E1Unmarshal --ir prysm/ir/ir-mainnet.json --type v1alpha1.Eth1Data --prefix e1_dec --imports E2eScal.P2Dec,E2eScal.E1Code --open E2eScal.E1Code > lean/E2eScal/GenE1Dec.lean
# SG-1 extension (after both hold-outs were opened; Eth1Data is development data for it, CONTAMINATION.md §8).
# The frozen generator's H2 run above stays the historical negative result. Raw output committed unedited.
$G p2dec --S prysm/go1.26.10/e2e/e1/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Eth1Data.UnmarshalSSZ.S --const E1Unmarshal --ir prysm/ir/ir-mainnet.json --type v1alpha1.Eth1Data --prefix e1_dec --imports E2eScal.P2Dec,E2eScal.P2DecZ,E2eScal.E1Code --open E2eScal.E1Code > lean/E2eScal/GenE1Dec.lean
# GEN2 (unit G2-G; generator change after H3, CONTAMINATION.md section 14): `p2dec --gen2` on the development
# set (Eth1Data, BlobIdentifier, DepositMessage are in-sample). New files; the files above stay as they are.
H=prysm/go1.26.10/e2e/h3/link/norm
$G p2dec --gen2 --S prysm/go1.26.10/e2e/e1/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Eth1Data.UnmarshalSSZ.S --const E1Unmarshal --ir prysm/ir/ir-mainnet.json --type v1alpha1.Eth1Data --prefix e1_g2dec --imports E2eScal.P2Dec,E2eScal.P2DecZ,E2eScal.U64Inline,E2eScal.E1Code --open E2eScal.E1Code > lean/E2eScal/Gen2E1Dec.lean
$G p2dec --gen2 --S $H/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlobIdentifier.UnmarshalSSZ.S --const BiUnmarshal --ir prysm/ir/ir-mainnet.json --type v1alpha1.BlobIdentifier --prefix bi_g2dec --imports E2eScal.P2Dec,E2eScal.P2DecZ,E2eScal.U64Inline,E2eScal.H3Code --open E2eScal.H3Code > lean/E2eScal/Gen2BiDec.lean
$G p2dec --gen2 --S $H/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DepositMessage.UnmarshalSSZ.S --const DmUnmarshal --ir prysm/ir/ir-mainnet.json --type v1alpha1.DepositMessage --prefix dm_g2dec --imports E2eScal.P2Dec,E2eScal.SegN,E2eScal.U64Inline,E2eScal.H3Code --open E2eScal.H3Code > lean/E2eScal/Gen2DmDec.lean
