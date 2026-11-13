import Prysm.Checkpoint.Spec

/-!
# Independent hand `Desc` of `v1alpha1.PendingConsolidation` (hold-out, class D)

Hand-written from consensus-specs electra (`specs/electra/beacon-chain.md`),
BEFORE the Desc checker's Desc of `(v1alpha1, PendingConsolidation)` was generated or printed (so that the hand Desc is independent of the checker output in time, not only in content).
This file is committed before `Prysm/PendingConsolidation/SpecChecker.lean` exists.

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
