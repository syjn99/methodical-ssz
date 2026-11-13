import Prysm.SyncCommittee.SpecDefinitions

/-!
# Definitions that the HistoricalBatch statements use

Part of the frozen statements (`Prysm/HistoricalBatch/Statements.lean`). A later change needs a new name and a reason.
The slice objects `Prysm.SyncCommittee.sliceHeaders` and `Prysm.SyncCommittee.elementBlocks` are imported from the SyncCommittee definitions, not copied.

- `desc`: hand `Desc` of consensus-specs phase0 `HistoricalBatch` (mainnet), from the spec text:

      SLOTS_PER_HISTORICAL_ROOT = 8192                # mainnet preset
      class HistoricalBatch(Container):
          block_roots: Vector[Root, SLOTS_PER_HISTORICAL_ROOT]   # Root = Bytes32
          state_roots: Vector[Root, SLOTS_PER_HISTORICAL_ROOT]

  The producer's Desc file was printed before this term was written (less independent than SyncCommittee).
- `SszValue`: the SSZ content of a Go `v1alpha1.HistoricalBatch` whose byte fields have the spec lengths
  (8192 × 32 each). `toValue` is the EthLib `Value`, `SszValue.encode` the 524288 bytes of the SSZ encoding.
-/

open EthLib.Serialization.Ssz

namespace Prysm.HistoricalBatch

/-- consensus-specs phase0 `HistoricalBatch` (mainnet). -/
def desc : Desc := .container ["block_roots", "state_roots"]
  [.vector (.byteVector 32) 8192, .vector (.byteVector 32) 8192]

/-- SSZ content of a Go `v1alpha1.HistoricalBatch` (8192 BlockRoots and 8192 StateRoots of 32 bytes). -/
structure SszValue where
  blockRoots : Vector (Vector UInt8 32) 8192
  stateRoots : Vector (Vector UInt8 32) 8192

/-- The 8192 block roots as byte lists, in order. -/
def SszValue.brs (g : SszValue) : List (List UInt8) := g.blockRoots.toList.map (·.toList)
/-- The 8192 state roots as byte lists, in order. -/
def SszValue.srs (g : SszValue) : List (List UInt8) := g.stateRoots.toList.map (·.toList)

def SszValue.toValue (g : SszValue) : Value :=
  .seq [.seq (g.blockRoots.toList.map fun p => .bytes p.toArray),
        .seq (g.stateRoots.toList.map fun p => .bytes p.toArray)]

/-- `blockRoots[0] ‖ … ‖ blockRoots[8191] ‖ stateRoots[0] ‖ … ‖ stateRoots[8191]`. -/
def SszValue.encode (g : SszValue) : Array UInt8 := g.brs.flatten.toArray ++ g.srs.flatten.toArray

end Prysm.HistoricalBatch
