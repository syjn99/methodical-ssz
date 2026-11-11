import E2e.Spec

/-!
# Independent hand `Desc` of `v1alpha1.PowBlock` (H6 hold-out, full-proof type)

Hand-written by the H6 evaluation session from consensus-specs bellatrix (`specs/bellatrix/fork-choice.md`),
BEFORE the Desc checker's Desc of `(v1alpha1, PowBlock)` was generated or printed (FINDINGS NF-10).
This file is committed before `PbSpecChecker.lean` exists.

    class PowBlock(Container):
        block_hash: Hash32                  # Bytes32
        parent_hash: Hash32                 # Bytes32
        total_difficulty: uint256

The spec types `total_difficulty` as `uint256` (32 bytes, little-endian). The H6 selection inventory lists
Prysm's field as a 32-byte vector (b32); the wire size is the same (32 bytes). The Desc below keeps the
spec type. How it relates to the producer's Desc is a theorem of `PbSpec.lean`, not an assumption here.
-/

namespace E2e
open EthLib.Serialization.Ssz

/-- consensus-specs bellatrix `PowBlock`. -/
def prysmPbDesc : Desc := .container ["block_hash", "parent_hash", "total_difficulty"]
  [.byteVector 32, .byteVector 32, .uint 32]

end E2e
