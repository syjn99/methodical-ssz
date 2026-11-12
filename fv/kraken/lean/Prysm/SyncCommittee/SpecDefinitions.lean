import Runtime.Contracts
import Prysm.Checkpoint.Spec
import Prysm.SyncAggregate.SpecDescription

/-!
# Definitions that the SyncAggregate and SyncCommittee statements use

These definitions are part of the frozen statements (`Prysm/SyncAggregate/Statements.lean`, `Prysm/SyncCommittee/Statements.lean`). A later change needs a
new name and a reason; the original stays.

- `elementBlocks ps es`: the element blocks of a slice of byte slices. Block i (`es[i]`) is at `ps[i]`.
  The two lists have the same length in every statement that uses it (`ps.length = 512 = es.length`).
- `sliceHeaders w ps`: the backing array of a Go `[][]byte` whose element i is the slice header
  `(ps[i], w, w)` (ptr, len, cap; 24 bytes, little endian).
- `Prysm.SyncAggregate.SszValue`, `SszValue`: the SSZ content of a Go `v1alpha1.SyncAggregate` / `v1alpha1.SyncCommittee` whose byte
  fields have the lengths of the spec (64 / 96; 512 × 48 / 48). `toValue` is the EthLib `Value`,
  `Prysm.SyncAggregate.SszValue.encode` / `SszValue.encode` the 160 / 24624 bytes of the SSZ encoding (fixed-size container: the fields in order).
-/

open Machine Runtime TestTarget EthLib.Serialization.Ssz

namespace Prysm.SyncCommittee

/-- The element blocks: `es[i]` at `ps[i]`, separated. -/
def elementBlocks : List (BitVec 64) → List (List UInt8) → DataMem → Prop
  | p :: ps, e :: es => Eq (e.At p) ⋆ elementBlocks ps es
  | _, _ => Std.ExtHashMap.emp

/-- The backing array of a `[][]byte` with element headers `(p, w, w)`. -/
def sliceHeaders (w : Int) (ps : List (BitVec 64)) : List UInt8 :=
  ps.flatMap fun p => Int.toBytes 8 p.toInt ++ Int.toBytes 8 w ++ Int.toBytes 8 w

/-- SSZ content of a Go `v1alpha1.SyncAggregate` (SyncCommitteeBits 64 bytes, SyncCommitteeSignature 96). -/
structure _root_.Prysm.SyncAggregate.SszValue where
  bits : Vector UInt8 64
  signature : Vector UInt8 96

/-- Bitvector[512] is the 512 bits of the 64 bytes, lowest bit of byte 0 first (EthLib `unpackBits`). -/
def _root_.Prysm.SyncAggregate.SszValue.toValue (g : Prysm.SyncAggregate.SszValue) : Value :=
  .seq [.bits (unpackBits g.bits.toArray 512), .bytes g.signature.toArray]

/-- `bits ‖ signature`. -/
def _root_.Prysm.SyncAggregate.SszValue.encode (g : Prysm.SyncAggregate.SszValue) : Array UInt8 := g.bits.toArray ++ g.signature.toArray

/-- SSZ content of a Go `v1alpha1.SyncCommittee` (512 Pubkeys of 48 bytes, AggregatePubkey 48). -/
structure SszValue where
  pubkeys : Vector (Vector UInt8 48) 512
  aggregatePubkey : Vector UInt8 48

/-- The 512 pubkeys as byte lists, in order. -/
def SszValue.pks (g : SszValue) : List (List UInt8) := g.pubkeys.toList.map (·.toList)

def SszValue.toValue (g : SszValue) : Value :=
  .seq [.seq (g.pubkeys.toList.map fun p => .bytes p.toArray), .bytes g.aggregatePubkey.toArray]

/-- `pubkeys[0] ‖ … ‖ pubkeys[511] ‖ aggregatePubkey`. -/
def SszValue.encode (g : SszValue) : Array UInt8 := g.pks.flatten.toArray ++ g.aggregatePubkey.toArray

end Prysm.SyncCommittee
