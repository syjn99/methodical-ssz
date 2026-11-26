module

public import EthLib.Serialization.Ssz

@[expose] public section

/-!
# Independent hand `Desc` of `v1alpha1.SyncAggregatorSelectionData`

This description is written by hand from consensus-specs altair (`ethereum/consensus-specs` release `v1.7.0-beta.4`, `specs/altair/validator.md`).
It does not use the checker description `Prysm/SyncAggregatorSelectionData/SpecChecker.lean`.

    class SyncAggregatorSelectionData(Container):
        slot: Slot                          # uint64
        subcommittee_index: uint64
-/

namespace Prysm.SyncAggregatorSelectionData
open EthLib.Serialization.Ssz

/-- consensus-specs altair `SyncAggregatorSelectionData`. -/
def desc : Desc := .container ["slot", "subcommittee_index"]
  [.uint 8, .uint 8]

end Prysm.SyncAggregatorSelectionData
