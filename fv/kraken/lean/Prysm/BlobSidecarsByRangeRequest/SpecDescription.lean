module

public import EthLib.Serialization.Ssz

@[expose] public section

/-!
# Independent hand `Desc` of `BlobSidecarsByRangeRequest`

This description is written by hand from the Prysm proto definitions in the Prysm source tree that the Go differential uses.
It does not use the checker descriptions `Prysm/<Type>/SpecChecker.lean`.
It is not independent of the source of the Desc producer (as `Prysm/ValidatorBalance/SpecDescription.lean`).
Where the proto cites a spec definition, the comment is quoted.
Overlay types (`cast_type` Slot, Epoch, ValidatorIndex, Gwei) are `uint64` in SSZ.
The proto file is `proto/prysm/v1alpha1/p2p_messages.proto`.

    message BlobSidecarsByRangeRequest { uint64 start_slot [Slot]; uint64 count; }      // "Spec Definition: (start_slot: Slot, count: uint64)"
-/

namespace Prysm.BlobSidecarsByRangeRequest
open EthLib.Serialization.Ssz

/-- Prysm `v1alpha1.BlobSidecarsByRangeRequest`. -/
def desc : Desc := .container ["start_slot", "count"]
  [.uint 8, .uint 8]

end Prysm.BlobSidecarsByRangeRequest
