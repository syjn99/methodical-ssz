import Prysm.Checkpoint.Spec

/-!
# Independent hand `Desc` of `v1alpha1.BlobIdentifier` (hold-out)

Hand-written from consensus-specs deneb (`specs/deneb/p2p-interface.md`),
BEFORE the Desc checker's Desc of `(v1alpha1, BlobIdentifier)` was generated or printed (so that the hand Desc is independent of the checker output in time, not only in content).
This file is committed before `BiSpecChecker.lean` exists.

    class BlobIdentifier(Container):
        block_root: Root        # Bytes32
        index: BlobIndex        # uint64
-/

namespace Prysm.BlobIdentifier
open EthLib.Serialization.Ssz

/-- consensus-specs deneb `BlobIdentifier`. -/
def desc : Desc := .container ["block_root", "index"]
  [.byteVector 32, .uint 8]

end Prysm.BlobIdentifier
