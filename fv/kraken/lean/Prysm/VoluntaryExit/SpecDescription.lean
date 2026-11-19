module

public import EthLib.Serialization.Ssz

@[expose] public section

/-!
# Independent hand `Desc` of `v1alpha1.VoluntaryExit`

This description is written by hand from consensus-specs phase0 (`ethereum/consensus-specs` release `v1.7.0-beta.4`, `specs/phase0/beacon-chain.md`).
It does not use the checker description `Prysm/VoluntaryExit/SpecChecker.lean`.

    class VoluntaryExit(Container):
        epoch: Epoch                        # uint64
        validator_index: ValidatorIndex     # uint64
-/

namespace Prysm.VoluntaryExit
open EthLib.Serialization.Ssz

/-- consensus-specs phase0 `VoluntaryExit`. -/
def desc : Desc := .container ["epoch", "validator_index"]
  [.uint 8, .uint 8]

end Prysm.VoluntaryExit
