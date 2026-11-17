import EthLib.Serialization.Ssz

/-!
# Hand `Desc` of `v1alpha1.HistoricalBatch`

This description is written by hand from consensus-specs phase0 (`specs/phase0/beacon-chain.md`).
It is not independent of the Desc file of the producer.

    SLOTS_PER_HISTORICAL_ROOT = 8192                # mainnet preset
    class HistoricalBatch(Container):
        block_roots: Vector[Root, SLOTS_PER_HISTORICAL_ROOT]   # Root = Bytes32
        state_roots: Vector[Root, SLOTS_PER_HISTORICAL_ROOT]
-/

open EthLib.Serialization.Ssz

namespace Prysm.HistoricalBatch

/-- consensus-specs phase0 `HistoricalBatch` (mainnet). -/
def desc : Desc := .container ["block_roots", "state_roots"]
  [.vector (.byteVector 32) 8192, .vector (.byteVector 32) 8192]

end Prysm.HistoricalBatch
