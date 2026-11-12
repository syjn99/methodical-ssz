import E2e.Spec

/-!
# Independent hand `Desc` of `v1alpha1.SigningData` (unit G5-C)

Hand-written by the G5-C session from consensus-specs phase0 (`specs/phase0/beacon-chain.md`, local clone at commit `aa16bb4`),
BEFORE the Desc checker's Desc of `(v1alpha1, SigningData)` was printed or copied into this tree (FINDINGS NF-10).
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
