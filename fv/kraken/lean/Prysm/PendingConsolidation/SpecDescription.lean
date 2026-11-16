import Prysm.Checkpoint.Spec

/-!
# Independent hand `Desc` of `v1alpha1.PendingConsolidation`

This description is written by hand from consensus-specs electra (`specs/electra/beacon-chain.md`).
It does not use the checker description `Prysm/PendingConsolidation/SpecChecker.lean`.

    class PendingConsolidation(Container):
        source_index: ValidatorIndex        # uint64
        target_index: ValidatorIndex        # uint64
-/

namespace Prysm.PendingConsolidation
open EthLib.Serialization.Ssz

/-- consensus-specs electra `PendingConsolidation`. -/
def desc : Desc := .container ["source_index", "target_index"]
  [.uint 8, .uint 8]

end Prysm.PendingConsolidation
