import Prysm.Checkpoint.Spec

/-!
# Independent hand `Desc` of `v1alpha1.SyncAggregate` and `v1alpha1.SyncCommittee`: the `SyncCommittee` part

The declarations of the other types of this group are in `Prysm/SyncAggregate/SpecDescription.lean`.
-/

namespace Prysm.SyncCommittee
open EthLib.Serialization.Ssz

/-- consensus-specs altair `SyncCommittee` (mainnet). -/
def desc : Desc := .container ["pubkeys", "aggregate_pubkey"]
  [.vector (.byteVector 48) 512, .byteVector 48]

end Prysm.SyncCommittee
