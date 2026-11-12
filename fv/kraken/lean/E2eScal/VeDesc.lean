import E2e.Spec

/-!
# Independent hand `Desc` of `v1alpha1.VoluntaryExit`

Hand-written from consensus-specs phase0 (`specs/phase0/beacon-chain.md`, local clone at commit `aa16bb4`),
BEFORE the Desc checker's Desc of `(v1alpha1, VoluntaryExit)` was printed or copied into this tree (so that the hand Desc is independent of the checker output in time, not only in content).
This file is committed before `VeSpecChecker.lean` exists.

    class VoluntaryExit(Container):
        epoch: Epoch                        # uint64
        validator_index: ValidatorIndex     # uint64
-/

namespace E2e
open EthLib.Serialization.Ssz

/-- consensus-specs phase0 `VoluntaryExit`. -/
def prysmVeDesc : Desc := .container ["epoch", "validator_index"]
  [.uint 8, .uint 8]

end E2e
