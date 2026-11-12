import Prysm.Checkpoint.Spec

/-!
# Independent hand `Desc` of `v1alpha1.SigningData`

Hand-written from consensus-specs phase0 (`specs/phase0/beacon-chain.md`, local clone at commit `aa16bb4`),
BEFORE the Desc checker's Desc of `(v1alpha1, SigningData)` was printed or copied into this tree (so that the hand Desc is independent of the checker output in time, not only in content).
This file is committed before `SdSpecChecker.lean` exists.

    class SigningData(Container):
        object_root: Root                   # Bytes32
        domain: Domain                      # Bytes32
-/

namespace E2e
open EthLib.Serialization.Ssz

/-- consensus-specs phase0 `SigningData`. -/
def prysmSdDesc : Desc := .container ["object_root", "domain"]
  [.byteVector 32, .byteVector 32]

end E2e
