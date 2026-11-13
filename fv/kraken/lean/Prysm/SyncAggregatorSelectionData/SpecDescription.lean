import Prysm.Checkpoint.Spec

/-!
# Independent hand `Desc` of `v1alpha1.SyncAggregatorSelectionData`

Hand-written from consensus-specs altair (`specs/altair/validator.md`, local clone at commit `aa16bb4`),
BEFORE the Desc checker's Desc of `(v1alpha1, SyncAggregatorSelectionData)` was printed or copied into this tree (so that the hand Desc is independent of the checker output in time, not only in content).
This file is committed before `SaSpecChecker.lean` exists.

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
