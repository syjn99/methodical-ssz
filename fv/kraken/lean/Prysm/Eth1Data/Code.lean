import Kraken.X64.Parser
import Machine.Include

/-!
# Code of `v1alpha1.Eth1Data`

This module holds the program constants `Code.unmarshalSSZ` and `Code.marshalSSZTo` of `v1alpha1.Eth1Data`.
Each program constant includes a `.S` file of the link set `prysm/go1.26.10/link-set/norm`.
The link set comes from the ELF of `prysm/go1.26.10/build-ids.txt`.
This file is written by hand.
-/

namespace Prysm.Eth1Data

/-- `(*v1alpha1.Eth1Data).UnmarshalSSZ` (protoc type, `phase0.ssz.go`). -/
def Code.unmarshalSSZ : Program := include_x64_code "../prysm/go1.26.10/link-set/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Eth1Data.UnmarshalSSZ.S"
/-- `(*v1alpha1.Eth1Data).MarshalSSZTo` (`phase0.ssz.go`). -/
def Code.marshalSSZTo : Program := include_x64_code "../prysm/go1.26.10/link-set/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Eth1Data.MarshalSSZTo.S"

end Prysm.Eth1Data
