import Prysm.Checkpoint.Spec

/-!
# Independent hand `Desc` of `BuilderPreferences`

This description is written by hand from the Prysm proto definitions in the Prysm source tree that the Go differential uses.
It does not use the checker descriptions `Prysm/<Type>/SpecChecker.lean`.
It is not independent of the source of the Desc producer (as `Prysm/ValidatorBalance/SpecDescription.lean`).
Where the proto cites a spec definition, the comment is quoted.
Overlay types (`cast_type` Slot, Epoch, ValidatorIndex, Gwei) are `uint64` in SSZ.
The proto file is `proto/prysm/v1alpha1/gloas_builder_api.proto`.

    message BuilderPreferences { uint64 max_execution_payment [Gwei]; }
-/

namespace Prysm.BuilderPreferences
open EthLib.Serialization.Ssz

/-- Prysm `v1alpha1.BuilderPreferences`. -/
def desc : Desc := .container ["max_execution_payment"]
  [.uint 8]

end Prysm.BuilderPreferences
