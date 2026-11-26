module

public import Kraken.X64.Parser
public import Machine.Include

@[expose] public section

/-!
# Code of `v1alpha1.Checkpoint`

This module holds the program constants `Code.unmarshalSSZ`, `Code.marshalSSZTo` and `Code.sizeSSZ` of `v1alpha1.Checkpoint`.
It also holds the label abbreviations `Code.unmarshalSSZLabel` and `Code.marshalSSZToLabel`.
Each program constant includes a `.S` file of the link set `prysm/go1.26.10/link-set/norm`.
The link set comes from the ELF of `prysm/go1.26.10/build-ids.txt`.
This file is written by hand.
-/

namespace Prysm.Checkpoint

/-- `(*v1alpha1.Checkpoint).UnmarshalSSZ` (protoc type, `phase0.ssz.go:1976`). -/
def Code.unmarshalSSZ : Program := include_x64_code "../prysm/go1.26.10/link-set/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Checkpoint.UnmarshalSSZ.S"
/-- `(*v1alpha1.Checkpoint).MarshalSSZTo` (`phase0.ssz.go:1959`; `Epoch.MarshalSSZTo` inlined). -/
def Code.marshalSSZTo : Program := include_x64_code "../prysm/go1.26.10/link-set/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Checkpoint.MarshalSSZTo.S"
/-- `(*v1alpha1.Checkpoint).SizeSSZ`. -/
def Code.sizeSSZ : Program := include_x64_code "../prysm/go1.26.10/link-set/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Checkpoint.SizeSSZ.S"

abbrev Code.unmarshalSSZLabel : String := "github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Checkpoint.UnmarshalSSZ"
abbrev Code.marshalSSZToLabel : String := "github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Checkpoint.MarshalSSZTo"

end Prysm.Checkpoint
