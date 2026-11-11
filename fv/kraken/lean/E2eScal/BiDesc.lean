import E2e.Spec

/-!
# Independent hand `Desc` of `v1alpha1.BlobIdentifier` (H3 hold-out)

Hand-written by the H3 evaluation session from consensus-specs deneb (`specs/deneb/p2p-interface.md`),
BEFORE the Desc checker's Desc of `(v1alpha1, BlobIdentifier)` was generated or printed (FINDINGS NF-10).
This file is committed before `BiSpecChecker.lean` exists.

    class BlobIdentifier(Container):
        block_root: Root        # Bytes32
        index: BlobIndex        # uint64
-/

namespace E2e
open EthLib.Serialization.Ssz

/-- consensus-specs deneb `BlobIdentifier`. -/
def prysmBiDesc : Desc := .container ["block_root", "index"]
  [.byteVector 32, .uint 8]

end E2e
