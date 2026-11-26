module

public import Machine.Bytes

@[expose] public section

/-!
# Fields of a flat container and the list functions of the statement kinds

`ContainerField` is a field of a flat fixed-size container: a fixed byte vector (`ContainerField.bytes n`) or an
8-byte `uint64` (`ContainerField.uint64`).
The functions here compute, from the field list, the parts of a kind statement that depend only on the fields:
the binders and their length hypotheses (`ForallChunks`, `ExistsWords`, `Implications`), the input chunks, the
receiver words before and after, the heap chunks, the sizes and the memory as a left fold of `⋆` (`sepAll`).
The decoder kinds (`Codec/Kind/DecodeAcceptAnyFrame.lean`) and the encoder kinds
(`Codec/Kind/EncodeFastPathAnyFrame.lean`) use them.
-/

open Machine

namespace Codec

/-- A field of a flat container: a fixed byte vector of `n` bytes, or an 8-byte `uint64`. -/
inductive ContainerField where
  | bytes (n : Nat)
  | uint64

namespace ContainerField

/-- SSZ size. -/
def size : ContainerField → Nat
  | bytes n => n
  | uint64 => 8

/-- Heap bytes used by the decoder for the field. -/
def heap : ContainerField → Nat
  | bytes n => n
  | uint64 => 0

/-- Number of 8-byte receiver words. -/
def words : ContainerField → Nat
  | bytes _ => 3
  | uint64 => 1

end ContainerField

/-- `∀ x₁ … xₘ : List UInt8, P [x₁, …, xₘ]`. -/
def ForallChunks : Nat → (List (List UInt8) → Prop) → Prop
  | 0, P => P []
  | m + 1, P => ∀ x : List UInt8, ForallChunks m (fun xs => P (x :: xs))

/-- `∃ p₁ … pₘ : BitVec 64, P [p₁, …, pₘ]`. -/
def ExistsWords : Nat → (List (BitVec 64) → Prop) → Prop
  | 0, P => P []
  | m + 1, P => ∃ p : BitVec 64, ExistsWords m (fun ps => P (p :: ps))

/-- `A₁ → … → Aₘ → Q`. -/
def Implications : List Prop → Prop → Prop
  | [], Q => Q
  | A :: As, Q => A → Implications As Q

/-- `b` for offset 0, else `b + o`. -/
def addOffset (b : BitVec 64) : Nat → BitVec 64
  | 0 => b
  | o + 1 => b + BitVec.ofNat 64 (o + 1)

/-- `init ⋆ p₁ ⋆ … ⋆ pₘ` (left-nested, as the notation). -/
def sepAll (init : DataMem → Prop) (ps : List (DataMem → Prop)) : DataMem → Prop :=
  ps.foldl (fun a b => a ⋆ b) init

def sszSize (fs : List ContainerField) : Nat := fs.foldl (fun a f => a + f.size) 0
def heapSize (fs : List ContainerField) : Nat := fs.foldl (fun a f => a + f.heap) 0
def receiverWords (fs : List ContainerField) : Nat := fs.foldl (fun a f => a + f.words) 0
def countBytesFields : List ContainerField → Nat
  | [] => 0
  | .bytes _ :: fs => countBytesFields fs + 1
  | .uint64 :: fs => countBytesFields fs

/-- Length hypotheses of the field values. -/
def valueLengthFacts : List ContainerField → List (List UInt8) → List Prop
  | [], _ => []
  | f :: fs, vs => ((vs.headD []).length = f.size) :: valueLengthFacts fs vs.tail

/-- `c` hypotheses "length = 8". -/
def wordLengthFacts : Nat → List (List UInt8) → List Prop
  | 0, _ => []
  | c + 1, cs => ((cs.headD []).length = 8) :: wordLengthFacts c cs.tail

/-- The input chunks: field value `i` at its SSZ offset from `b`. -/
def inputChunks (b : BitVec 64) : List ContainerField → Nat → List (List UInt8) → List (DataMem → Prop)
  | [], _, _ => []
  | f :: fs, o, vs => Eq ((vs.headD []).At (addOffset b o)) :: inputChunks b fs (o + f.size) vs.tail

/-- The receiver words before the call: one arbitrary 8-byte chunk per word, from Go offset `g`. -/
def receiverPre (b : BitVec 64) : Nat → Nat → List (List UInt8) → List (DataMem → Prop)
  | 0, _, _ => []
  | c + 1, g, cs => Eq ((cs.headD []).At (addOffset b g)) :: receiverPre b c (g + 8) cs.tail

/-- The receiver words after the call: slice header (pointer, len, cap) or the 8 value bytes. -/
def receiverPost (b : BitVec 64) : List ContainerField → Nat → List (List UInt8) → List (BitVec 64) → List (DataMem → Prop)
  | [], _, _, _ => []
  | .bytes n :: fs, g, vs, ps =>
    Eq ((Int.toBytes 8 (ps.headD 0).toInt).At (addOffset b g))
      :: Eq ((Int.toBytes 8 (Int.ofNat n)).At (addOffset b (g + 8)))
      :: Eq ((Int.toBytes 8 (Int.ofNat n)).At (addOffset b (g + 16)))
      :: receiverPost b fs (g + 24) vs.tail ps.tail
  | .uint64 :: fs, g, vs, ps => Eq ((vs.headD []).At (addOffset b g)) :: receiverPost b fs (g + 8) vs.tail ps

/-- The new heap chunks: the bytes of each byte-vector field at its pointer. -/
def heapPost : List ContainerField → List (List UInt8) → List (BitVec 64) → List (DataMem → Prop)
  | [], _, _ => []
  | .bytes _ :: fs, vs, ps => Eq ((vs.headD []).At (ps.headD 0)) :: heapPost fs vs.tail ps.tail
  | .uint64 :: fs, vs, ps => heapPost fs vs.tail ps

/-- 1 if the receiver has a `state` word before the first field. -/
def stateWords : Bool → Nat
  | true => 1
  | false => 0

/-- The `state` chunk (if any). -/
def stateChunk (b : BitVec 64) : Bool → List (List UInt8) → List (DataMem → Prop)
  | true, cs => [Eq ((cs.headD []).At b)]
  | false, _ => []

end Codec
