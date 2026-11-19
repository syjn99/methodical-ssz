module

public import EthLib.Serialization.Ssz

@[expose] public section

/-!
# Independent hand `Desc` of `BeaconBlocksByRangeRequest`

This description is written by hand from the Prysm proto definitions in the Prysm source tree that the Go differential uses.
It does not use the checker descriptions `Prysm/<Type>/SpecChecker.lean`.
It is not independent of the source of the Desc producer (as `Prysm/ValidatorBalance/SpecDescription.lean`).
Where the proto cites a spec definition, the comment is quoted.
Overlay types (`cast_type` Slot, Epoch, ValidatorIndex, Gwei) are `uint64` in SSZ.
The proto file is `proto/prysm/v1alpha1/p2p_messages.proto`.

    message BeaconBlocksByRangeRequest { uint64 start_slot [Slot]; uint64 count; uint64 step; }
-/

namespace Prysm.BeaconBlocksByRangeRequest
open EthLib.Serialization.Ssz

/-- Prysm `v1alpha1.BeaconBlocksByRangeRequest`. -/
def desc : Desc := .container ["start_slot", "count", "step"]
  [.uint 8, .uint 8, .uint 8]

end Prysm.BeaconBlocksByRangeRequest
