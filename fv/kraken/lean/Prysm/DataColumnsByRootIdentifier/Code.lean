module

public import Kraken.X64.Parser
public import Machine.Include

@[expose] public section

/-!
# Code of `v1alpha1.DataColumnsByRootIdentifier`

This module holds the program constants `Code.unmarshalSSZ` and `Code.marshalSSZTo` of `v1alpha1.DataColumnsByRootIdentifier`.
Each program constant includes a `.S` file of the link set `prysm/go1.26.10/link-set/norm`.
The link set comes from the ELF of `prysm/go1.26.10/build-ids.txt`.
This file is written by hand.
-/

namespace Prysm.DataColumnsByRootIdentifier

/-- `(*v1alpha1.DataColumnsByRootIdentifier).UnmarshalSSZ` (protoc type, `fulu.ssz.go:1778`). -/
def Code.unmarshalSSZ : Program := include_x64_code "../prysm/go1.26.10/link-set/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DataColumnsByRootIdentifier.UnmarshalSSZ.S"

/-- `(*v1alpha1.DataColumnsByRootIdentifier).MarshalSSZTo` (protoc type, `fulu.ssz.go:1754`). -/
def Code.marshalSSZTo : Program := include_x64_code "../prysm/go1.26.10/link-set/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DataColumnsByRootIdentifier.MarshalSSZTo.S"

end Prysm.DataColumnsByRootIdentifier
