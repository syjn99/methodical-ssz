module

public import EthLib.Serialization.Ssz

@[expose] public section

/-!
# Independent hand `Desc` of `v1alpha1.BeaconBlockHeader`

This description is written by hand from consensus-specs phase0 (`specs/phase0/beacon-chain.md`).
It does not use the checker description `Prysm/BeaconBlockHeader/SpecChecker.lean`.

    class BeaconBlockHeader(Container):
        slot: Slot                     # uint64
        proposer_index: ValidatorIndex # uint64
        parent_root: Root              # Bytes32
        state_root: Root
        body_root: Root
-/

namespace Prysm.BeaconBlockHeader
open EthLib.Serialization.Ssz

/-- consensus-specs phase0 `BeaconBlockHeader`. -/
def desc : Desc := .container ["slot", "proposer_index", "parent_root", "state_root", "body_root"]
  [.uint 8, .uint 8, .byteVector 32, .byteVector 32, .byteVector 32]

end Prysm.BeaconBlockHeader
