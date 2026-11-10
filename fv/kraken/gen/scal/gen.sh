#!/bin/sh
# Regenerate the three committed generated files (run from anywhere; paths are relative to fv/kraken).
# Gate it like any generator run. Check with the skill's regen_check.sh (see README).
set -e
cd "$(dirname "$0")/../.."
G="python3 -I gen/scal/scalgen.py"
N=prysm/go1.26.10/e2e/ad/link/norm
$G p1 --S $N/github.com_OffchainLabs_prysm_v7_consensus_types_primitives.CommitteeIndex.UnmarshalSSZ.S --const CiUnmarshal --name ci_unmarshal_accept_main_g --same-as E2eAd.ci_unmarshal_accept_main --imports E2eScal.P1,E2eAd.Prims --open E2eAd.Code > lean/E2eScal/GenCi.lean
$G p2dec --S $N/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttestationData.UnmarshalSSZ.S --const AdUnmarshal --ir prysm/ir/ir-mainnet.json --type v1alpha1.AttestationData --prefix ad_dec --imports E2eScal.P2Dec,E2eAd.Code --open E2eAd.Code > lean/E2eScal/GenAdDec.lean
$G p2dec --S prysm/go1.26.10/e2e/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Checkpoint.UnmarshalSSZ.S --const CpUnmarshal --ir prysm/ir/ir-mainnet.json --type v1alpha1.Checkpoint --prefix cp_dec --imports E2eScal.P2Dec,E2e.Code --open E2e.Code > lean/E2eScal/GenCpDec.lean
