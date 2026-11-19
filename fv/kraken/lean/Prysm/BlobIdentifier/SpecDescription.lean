module

public import EthLib.Serialization.Ssz

@[expose] public section

/-!
# Independent hand `Desc` of `v1alpha1.BlobIdentifier`

This description is written by hand from consensus-specs deneb (`specs/deneb/p2p-interface.md`).
It does not use the checker description `Prysm/BlobIdentifier/SpecChecker.lean`.

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
