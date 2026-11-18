import Prysm.Checkpoint.SpecDescription

/-!
# Independent hand `Desc` of `v1alpha1.AttestationData`

This description is written by hand from consensus-specs phase0 (`specs/phase0/beacon-chain.md`).
It does not use the checker description `Prysm/AttestationData/SpecChecker.lean`.

    class AttestationData(Container):
        slot: Slot                # uint64
        index: CommitteeIndex     # uint64
        beacon_block_root: Root   # Bytes32
        source: Checkpoint
        target: Checkpoint

`Checkpoint` is the hand `Desc` `Prysm.Checkpoint.desc` (consensus-specs `Checkpoint(epoch: Epoch, root: Root)`).
-/

namespace Prysm.AttestationData
open EthLib.Serialization.Ssz

/-- consensus-specs phase0 `AttestationData`. -/
def desc : Desc := .container ["slot", "index", "beacon_block_root", "source", "target"]
  [.uint 8, .uint 8, .byteVector 32, Prysm.Checkpoint.desc, Prysm.Checkpoint.desc]

end Prysm.AttestationData
