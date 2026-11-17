import EthLib.Serialization.Ssz

/-!
# Independent hand `Desc` of `v1alpha1.ValidatorBalance`

This description is written by hand from the Prysm proto definition `message ValidatorBalance` (`proto/prysm/v1alpha1/validator.proto`).
That file is in the Prysm source tree that the Go differential uses.
consensus-specs has no container of this name: it is a Prysm API type.
So this description is not independent of the source of the Desc producer.
It does not use the checker description `Prysm/ValidatorBalance/SpecChecker.lean`.

    message ValidatorBalance {
      uint64 index = 1 [cast_type = primitives.ValidatorIndex];   // uint64
      uint64 balance = 2; }
-/

namespace Prysm.ValidatorBalance
open EthLib.Serialization.Ssz

/-- Prysm proto `ValidatorBalance` (no consensus-specs container). -/
def desc : Desc := .container ["index", "balance"]
  [.uint 8, .uint 8]

end Prysm.ValidatorBalance
