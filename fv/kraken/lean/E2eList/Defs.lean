import Fk.Contracts
import E2e.Spec
import E2eList.Desc

/-!
# Definitions that the SyncAggregate and SyncCommittee statements use

These definitions are part of the frozen statements (`StmtSa.lean`, `StmtSc.lean`). A later change needs a
new name and a reason; the original stays.

- `lvElems ps es`: the element blocks of a slice of byte slices. Block i (`es[i]`) is at `ps[i]`.
  The two lists have the same length in every statement that uses it (`ps.length = 512 = es.length`).
- `lvHdrs w ps`: the backing array of a Go `[][]byte` whose element i is the slice header
  `(ps[i], w, w)` (ptr, len, cap; 24 bytes, little endian).
- `PSa`, `PSc`: the SSZ content of a Go `v1alpha1.SyncAggregate` / `v1alpha1.SyncCommittee` whose byte
  fields have the lengths of the spec (64 / 96; 512 × 48 / 48). `toValue` is the EthLib `Value`,
  `psaEnc` / `pscEnc` the 160 / 24624 bytes of the SSZ encoding (fixed-size container: the fields in order).
-/

open Fk EthLib.Serialization.Ssz

namespace E2eList

/-- The element blocks: `es[i]` at `ps[i]`, separated. -/
def lvElems : List (BitVec 64) → List (List UInt8) → DataMem → Prop
  | p :: ps, e :: es => Eq (e.At p) ⋆ lvElems ps es
  | _, _ => Std.ExtHashMap.emp

/-- The backing array of a `[][]byte` with element headers `(p, w, w)`. -/
def lvHdrs (w : Int) (ps : List (BitVec 64)) : List UInt8 :=
  ps.flatMap fun p => Int.toBytes 8 p.toInt ++ Int.toBytes 8 w ++ Int.toBytes 8 w

/-- SSZ content of a Go `v1alpha1.SyncAggregate` (SyncCommitteeBits 64 bytes, SyncCommitteeSignature 96). -/
structure PSa where
  bits : Vector UInt8 64
  signature : Vector UInt8 96

/-- Bitvector[512] is the 512 bits of the 64 bytes, lowest bit of byte 0 first (EthLib `unpackBits`). -/
def PSa.toValue (g : PSa) : Value :=
  .seq [.bits (unpackBits g.bits.toArray 512), .bytes g.signature.toArray]

/-- `bits ‖ signature`. -/
def psaEnc (g : PSa) : Array UInt8 := g.bits.toArray ++ g.signature.toArray

/-- SSZ content of a Go `v1alpha1.SyncCommittee` (512 Pubkeys of 48 bytes, AggregatePubkey 48). -/
structure PSc where
  pubkeys : Vector (Vector UInt8 48) 512
  aggregatePubkey : Vector UInt8 48

/-- The 512 pubkeys as byte lists, in order. -/
def PSc.pks (g : PSc) : List (List UInt8) := g.pubkeys.toList.map (·.toList)

def PSc.toValue (g : PSc) : Value :=
  .seq [.seq (g.pubkeys.toList.map fun p => .bytes p.toArray), .bytes g.aggregatePubkey.toArray]

/-- `pubkeys[0] ‖ … ‖ pubkeys[511] ‖ aggregatePubkey`. -/
def pscEnc (g : PSc) : Array UInt8 := g.pks.flatten.toArray ++ g.aggregatePubkey.toArray

end E2eList
