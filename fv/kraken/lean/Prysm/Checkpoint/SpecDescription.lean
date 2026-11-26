module

public import EthLib.Serialization.Ssz

@[expose] public section

/-!
# Independent hand `Desc` of `v1alpha1.Checkpoint`

This description is written by hand from consensus-specs phase0 (`specs/phase0/beacon-chain.md`).
It does not use the checker description `Prysm/Checkpoint/SpecChecker.lean`.

    class Checkpoint(Container):
        epoch: Epoch      # Epoch = uint64
        root: Root        # Root = Bytes32

The field order is epoch, root.
The SSZ kinds are `uint64` (8-byte little endian) and `Bytes32` (EthLib `byteVector 32`).
-/

namespace Prysm.Checkpoint
open EthLib.Serialization.Ssz

/-- consensus-specs phase0 `Checkpoint`. -/
def desc : Desc := .container ["epoch", "root"] [.uint 8, .byteVector 32]

end Prysm.Checkpoint
