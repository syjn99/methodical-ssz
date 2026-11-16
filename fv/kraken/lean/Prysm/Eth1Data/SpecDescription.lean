import Prysm.Checkpoint.Spec

/-!
# Independent hand `Desc` of `v1alpha1.Eth1Data`

This description is written by hand from consensus-specs phase0 (`specs/phase0/beacon-chain.md`).
It does not use the checker description `Prysm/Eth1Data/SpecChecker.lean`.

    class Eth1Data(Container):
        deposit_root: Root      # Bytes32
        deposit_count: uint64
        block_hash: Hash32      # Bytes32
-/

namespace Prysm.Eth1Data
open EthLib.Serialization.Ssz

/-- consensus-specs phase0 `Eth1Data`. -/
def desc : Desc := .container ["deposit_root", "deposit_count", "block_hash"]
  [.byteVector 32, .uint 8, .byteVector 32]

end Prysm.Eth1Data
