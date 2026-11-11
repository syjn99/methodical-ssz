import E2e.Spec

/-!
# Independent hand `Desc` of `v1alpha1.ValidatorBalance` (unit G5-C)

Hand-written by the G5-C session from the Prysm proto definition (`proto/prysm/v1alpha1/validator.proto`, `message ValidatorBalance`; the Prysm source tree that the Go differential uses, read only). consensus-specs has NO container of this name: it is a Prysm API type. So this Desc is not independent of the producer's source in the way the other four are; it is independent of the Desc checker's output only,
BEFORE the Desc checker's Desc of `(v1alpha1, ValidatorBalance)` was printed or copied into this tree (FINDINGS NF-10).
This file is committed before `VbSpecChecker.lean` exists.

    message ValidatorBalance {
      uint64 index = 1 [cast_type = primitives.ValidatorIndex];   // uint64
      uint64 balance = 2; }
-/

namespace E2e
open EthLib.Serialization.Ssz

/-- Prysm proto `ValidatorBalance` (no consensus-specs container). -/
def prysmVbDesc : Desc := .container ["index", "balance"]
  [.uint 8, .uint 8]

end E2e
