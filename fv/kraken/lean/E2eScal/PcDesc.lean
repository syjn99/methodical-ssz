import E2e.Spec

/-!
# Independent hand `Desc` of `v1alpha1.PendingConsolidation` (H5 hold-out, class D)

Hand-written by the H5 evaluation session from consensus-specs electra (`specs/electra/beacon-chain.md`),
BEFORE the Desc checker's Desc of `(v1alpha1, PendingConsolidation)` was generated or printed (FINDINGS NF-10).
This file is committed before `PcSpecChecker.lean` exists.

    class PendingConsolidation(Container):
        source_index: ValidatorIndex        # uint64
        target_index: ValidatorIndex        # uint64
-/

namespace E2e
open EthLib.Serialization.Ssz

/-- consensus-specs electra `PendingConsolidation`. -/
def prysmPcDesc : Desc := .container ["source_index", "target_index"]
  [.uint 8, .uint 8]

end E2e
