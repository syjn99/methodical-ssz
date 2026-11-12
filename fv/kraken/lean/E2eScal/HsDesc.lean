import E2e.Spec

/-!
# Independent hand `Desc` of `v1alpha1.HistoricalSummary`

Hand-written from consensus-specs capella (`specs/capella/beacon-chain.md`, local clone at commit `aa16bb4`),
BEFORE the Desc checker's Desc of `(v1alpha1, HistoricalSummary)` was printed or copied into this tree (so that the hand Desc is independent of the checker output in time, not only in content).
This file is committed before `HsSpecChecker.lean` exists.

    class HistoricalSummary(Container):
        block_summary_root: Root            # Bytes32
        state_summary_root: Root            # Bytes32
-/

namespace E2e
open EthLib.Serialization.Ssz

/-- consensus-specs capella `HistoricalSummary`. -/
def prysmHsDesc : Desc := .container ["block_summary_root", "state_summary_root"]
  [.byteVector 32, .byteVector 32]

end E2e
