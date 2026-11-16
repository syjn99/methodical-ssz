import Prysm.Checkpoint.Spec

/-!
# Independent hand `Desc` of `v1alpha1.SigningData`

This description is written by hand from consensus-specs phase0 (`ethereum/consensus-specs` release `v1.7.0-beta.4`, `specs/phase0/beacon-chain.md`).
It does not use the checker description `Prysm/SigningData/SpecChecker.lean`.

    class SigningData(Container):
        object_root: Root                   # Bytes32
        domain: Domain                      # Bytes32
-/

namespace Prysm.SigningData
open EthLib.Serialization.Ssz

/-- consensus-specs phase0 `SigningData`. -/
def desc : Desc := .container ["object_root", "domain"]
  [.byteVector 32, .byteVector 32]

end Prysm.SigningData
