#!/bin/sh
# Regenerate the committed generated files (run from anywhere; paths are relative to fv/kraken):
# three development-set files, then the two hold-out H1 files (one run each in gate jobs 299 and 312).
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
# prysm/go1.26.10/e2e/e1/gen-e1dec.raw.txt). Kept as a comment so that `set -e` does not stop this script:
# $G p2dec --S prysm/go1.26.10/e2e/e1/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Eth1Data.UnmarshalSSZ.S --const E1Unmarshal --ir prysm/ir/ir-mainnet.json --type v1alpha1.Eth1Data --prefix e1_dec --imports E2eScal.P2Dec,E2eScal.E1Code --open E2eScal.E1Code > lean/E2eScal/GenE1Dec.lean
