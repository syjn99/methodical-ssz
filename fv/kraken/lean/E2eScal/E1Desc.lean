import Prysm.Checkpoint.Spec

/-!
# Independent hand `Desc` of `v1alpha1.Eth1Data` (hold-out)

Hand-written from consensus-specs phase0 (`specs/phase0/beacon-chain.md`),
BEFORE the Desc checker's Desc of `(v1alpha1, Eth1Data)` was generated or printed (rule:
independence in time). This file is committed before `E1SpecChecker.lean` exists.

    class Eth1Data(Container):
        deposit_root: Root      # Bytes32
        deposit_count: uint64
        block_hash: Hash32      # Bytes32
-/

namespace E2e
open EthLib.Serialization.Ssz

/-- consensus-specs phase0 `Eth1Data`. -/
def prysmE1Desc : Desc := .container ["deposit_root", "deposit_count", "block_hash"]
  [.byteVector 32, .uint 8, .byteVector 32]

end E2e
