import Prysm.Checkpoint.Spec

/-!
# Independent hand `Desc` of `v1alpha1.PowBlock` (hold-out, full-proof type)

Hand-written from consensus-specs bellatrix (`specs/bellatrix/fork-choice.md`),
BEFORE the Desc checker's Desc of `(v1alpha1, PowBlock)` was generated or printed (so that the hand Desc is independent of the checker output in time, not only in content).
This file is committed before `Prysm/PowBlock/SpecChecker.lean` exists.

    class PowBlock(Container):
        block_hash: Hash32                  # Bytes32
        parent_hash: Hash32                 # Bytes32
        total_difficulty: uint256

The spec types `total_difficulty` as `uint256` (32 bytes, little-endian). The hold-out selection inventory lists
Prysm's field as a 32-byte vector (b32); the wire size is the same (32 bytes). The Desc below keeps the
spec type. How it relates to the producer's Desc is a theorem of `Prysm/PowBlock/Spec.lean`, not an assumption here.
-/

namespace Prysm.PowBlock
open EthLib.Serialization.Ssz

/-- consensus-specs bellatrix `PowBlock`. -/
def desc : Desc := .container ["block_hash", "parent_hash", "total_difficulty"]
  [.byteVector 32, .byteVector 32, .uint 32]

end Prysm.PowBlock
