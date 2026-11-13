import Prysm.Checkpoint.Spec

/-!
# Independent hand `Desc` of the eight types with a generated theorem: the `BeaconBlocksByRangeRequest` part

The declarations of the other types of this group are in `Prysm/DepositRequest/SpecDescription.lean`.
-/

namespace Prysm.BeaconBlocksByRangeRequest
open EthLib.Serialization.Ssz

/-- Prysm `v1alpha1.BeaconBlocksByRangeRequest`. -/
def desc : Desc := .container ["start_slot", "count", "step"]
  [.uint 8, .uint 8, .uint 8]

end Prysm.BeaconBlocksByRangeRequest
