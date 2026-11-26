module

public import EthLib.Serialization.Ssz

@[expose] public section

/-!
# Independent hand `Desc` of `PartialDataColumnGroupID`

This description is written by hand from the Prysm proto definitions in the Prysm source tree that the Go differential uses.
It does not use the checker descriptions `Prysm/<Type>/SpecChecker.lean`.
It is not independent of the source of the Desc producer (as `Prysm/ValidatorBalance/SpecDescription.lean`).
Where the proto cites a spec definition, the comment is quoted.
Overlay types (`cast_type` Slot, Epoch, ValidatorIndex, Gwei) are `uint64` in SSZ.
The proto file is `proto/prysm/v1alpha1/partial_data_columns.proto`.

    message PartialDataColumnGroupID { bytes beacon_block_root [32]; uint64 slot [Slot]; }  // "Field order follows the spec"
-/

namespace Prysm.PartialDataColumnGroupID
open EthLib.Serialization.Ssz

/-- Prysm `v1alpha1.PartialDataColumnGroupID`. -/
def desc : Desc := .container ["beacon_block_root", "slot"]
  [.byteVector 32, .uint 8]

end Prysm.PartialDataColumnGroupID
