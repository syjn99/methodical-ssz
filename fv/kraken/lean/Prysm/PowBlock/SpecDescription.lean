import EthLib.Serialization.Ssz

/-!
# Independent hand `Desc` of `v1alpha1.PowBlock`

This description is written by hand from consensus-specs bellatrix (`specs/bellatrix/fork-choice.md`).
It does not use the checker description `Prysm/PowBlock/SpecChecker.lean`.

    class PowBlock(Container):
        block_hash: Hash32                  # Bytes32
        parent_hash: Hash32                 # Bytes32
        total_difficulty: uint256

The spec types `total_difficulty` as `uint256` (32 bytes, little-endian). The type inventory lists
Prysm's field as a 32-byte vector (b32); the wire size is the same (32 bytes). The Desc below keeps the
spec type. How it relates to the producer's Desc is a theorem of `Prysm/PowBlock/Spec.lean`, not an assumption here.
-/

namespace Prysm.PowBlock
open EthLib.Serialization.Ssz

/-- consensus-specs bellatrix `PowBlock`. -/
def desc : Desc := .container ["block_hash", "parent_hash", "total_difficulty"]
  [.byteVector 32, .byteVector 32, .uint 32]

end Prysm.PowBlock
