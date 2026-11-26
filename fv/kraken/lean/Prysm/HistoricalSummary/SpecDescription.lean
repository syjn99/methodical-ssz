module

public import EthLib.Serialization.Ssz

@[expose] public section

/-!
# Independent hand `Desc` of `v1alpha1.HistoricalSummary`

This description is written by hand from consensus-specs capella (`ethereum/consensus-specs` release `v1.7.0-beta.4`, `specs/capella/beacon-chain.md`).
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
