import E2e.Spec

/-!
# Independent hand `Desc` of `v1alpha1.HistoricalSummary` (unit G5-C)

Hand-written by the G5-C session from consensus-specs capella (`specs/capella/beacon-chain.md`, local clone at commit `aa16bb4`),
BEFORE the Desc checker's Desc of `(v1alpha1, HistoricalSummary)` was printed or copied into this tree (FINDINGS NF-10).
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
