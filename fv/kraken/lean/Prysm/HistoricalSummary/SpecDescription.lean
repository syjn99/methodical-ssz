import Prysm.Checkpoint.Spec

/-!
# Independent hand `Desc` of `v1alpha1.HistoricalSummary`

This description is written by hand from consensus-specs capella (`specs/capella/beacon-chain.md`, local clone at commit `aa16bb4`).
It does not use the checker description `Prysm/HistoricalSummary/SpecChecker.lean`.

    class HistoricalSummary(Container):
        block_summary_root: Root            # Bytes32
        state_summary_root: Root            # Bytes32
-/

namespace Prysm.HistoricalSummary
open EthLib.Serialization.Ssz

/-- consensus-specs capella `HistoricalSummary`. -/
def desc : Desc := .container ["block_summary_root", "state_summary_root"]
  [.byteVector 32, .byteVector 32]

end Prysm.HistoricalSummary
