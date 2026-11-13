import Prysm.Checkpoint.Spec

/-!
# Independent hand `Desc` of the eight types with a generated theorem: the `BuilderPreferences` part

The declarations of the other types of this group are in `Prysm/DepositRequest/SpecDescription.lean`.
-/

namespace Prysm.BuilderPreferences
open EthLib.Serialization.Ssz

/-- Prysm `v1alpha1.BuilderPreferences`. -/
def desc : Desc := .container ["max_execution_payment"]
  [.uint 8]

end Prysm.BuilderPreferences
