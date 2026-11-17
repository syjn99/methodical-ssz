import EthLib.Serialization.Ssz

/-!
# Independent hand `Desc` of `primitives.Slot`

This description is written by hand from consensus-specs phase0 (`specs/phase0/beacon-chain.md`, "Custom types").
The type has no checker description, because the generator IR has no record of a hand-written primitive type.

    Slot = uint64

EthLib `Desc.uint` takes a byte width, so the type is `.uint 8`.
-/

namespace Prysm.Slot
open EthLib.Serialization.Ssz

/-- consensus-specs phase0 `Slot`. -/
def desc : Desc := .uint 8

end Prysm.Slot
