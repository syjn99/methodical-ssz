import Prysm.Checkpoint.Spec

/-!
# Independent hand `Desc` of `v1alpha1.SyncAggregatorSelectionData`

This description is written by hand from consensus-specs altair (`specs/altair/validator.md`, local clone at commit `aa16bb4`).
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
