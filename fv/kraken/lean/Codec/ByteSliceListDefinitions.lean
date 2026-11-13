import Runtime.Contracts
import Prysm.Checkpoint.Spec
import Prysm.SyncAggregate.SpecDescription
import Prysm.SyncAggregate.SpecDefinitions

/-!
# Memory objects of a `[][]byte` decoder loop

`elementBlocks`: the element blocks at their pointers. `sliceHeaders`: the backing array of slice headers
`(p, w, w)`. The SyncCommittee, HistoricalBatch and Deposit statements and `Codec/Segment/` use them.
-/

open Machine Runtime EthLib.Serialization.Ssz

namespace Codec

/-- The element blocks: `es[i]` at `ps[i]`, separated. -/
def elementBlocks : List (BitVec 64) → List (List UInt8) → DataMem → Prop
  | p :: ps, e :: es => Eq (e.At p) ⋆ Codec.elementBlocks ps es
  | _, _ => Std.ExtHashMap.emp

/-- The backing array of a `[][]byte` with element headers `(p, w, w)`. -/
def sliceHeaders (w : Int) (ps : List (BitVec 64)) : List UInt8 :=
  ps.flatMap fun p => Int.toBytes 8 p.toInt ++ Int.toBytes 8 w ++ Int.toBytes 8 w

end Codec
