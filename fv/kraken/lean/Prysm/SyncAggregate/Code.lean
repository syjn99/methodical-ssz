import Kraken.X64.Parser
import Machine.Include

/-!
# Code of `v1alpha1.SyncAggregate`

This module holds the program constant `Code.unmarshalSSZ` of `v1alpha1.SyncAggregate`.
Each program constant includes a `.S` file of the link set `prysm/go1.26.10/link-set/norm`.
The link set comes from the ELF of `prysm/go1.26.10/build-ids.txt`.
This file is written by hand.
-/

namespace Prysm.SyncAggregate

/-- `(*v1alpha1.SyncAggregate).UnmarshalSSZ` (protoc type, `altair.ssz.go`). -/
def Code.unmarshalSSZ : Program := include_x64_code "../prysm/go1.26.10/link-set/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncAggregate.UnmarshalSSZ.S"

end Prysm.SyncAggregate
