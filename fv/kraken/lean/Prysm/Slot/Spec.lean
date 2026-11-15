import Prysm.Epoch.Spec

/-!
# Spec of the hand-written Prysm `primitives.Slot`

Independent hand `Desc`, written from consensus-specs phase0 (`specs/phase0/beacon-chain.md`, "Custom types"):
`Slot = uint64`.
EthLib `Desc.uint` takes a byte width, so the type is `.uint 8`.
No Desc checker record exists for the type, so this module has no `checkerDesc`.
The lemmas about `.uint 8` are the lemmas `Prysm.Epoch.uint64_*` of `Prysm/Epoch/Spec.lean`.
-/

namespace Prysm.Slot
open EthLib.Serialization.Ssz

/-- consensus-specs phase0 `Slot`. -/
def desc : Desc := .uint 8

end Prysm.Slot
