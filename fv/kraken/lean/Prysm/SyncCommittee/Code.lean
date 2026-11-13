import Kraken.X64.Parser
import Machine.Include

/-!
# Code of the SyncAggregate and SyncCommittee function set (Go 1.26.10 ELF `c6403c02…911e`): the `SyncCommittee` part

The declarations of the other types of this group are in `Prysm/SyncAggregate/Code.lean`.
-/

namespace Prysm.SyncCommittee

/-- `(*v1alpha1.SyncCommittee).UnmarshalSSZ` (protoc type, `altair.ssz.go`). -/
def Code.unmarshalSSZ : Program := include_x64_rt "../prysm/go1.26.10/link-set/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommittee.UnmarshalSSZ.S"

end Prysm.SyncCommittee
