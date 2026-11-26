module

public import EthLib.Serialization.Ssz

@[expose] public section

/-!
# Independent hand `Desc` of `primitives.ValidatorIndex`

This description is written by hand from consensus-specs phase0 (`specs/phase0/beacon-chain.md`, "Custom types"):
`ValidatorIndex = uint64`.
EthLib `Desc.uint` takes a byte width, so the type is `.uint 8`.
No Desc checker record exists for the type, so the type has no `checkerDesc`.
-/

namespace Prysm.ValidatorIndex
open EthLib.Serialization.Ssz

/-- consensus-specs phase0 `ValidatorIndex`. -/
def desc : Desc := .uint 8

end Prysm.ValidatorIndex
