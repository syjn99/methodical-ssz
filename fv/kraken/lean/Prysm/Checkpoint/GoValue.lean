import Prysm.Checkpoint.Layout
import Prysm.Checkpoint.WitnessDecodeAccept
import Prysm.Checkpoint.WitnessEncodeFastPath
import Prysm.Checkpoint.WitnessEncodeRejectLength

/-!
# Go-value element

`layout`: the offsets that the machine theorems use for the receiver (state 0,
Epoch 8, Root 16/24/32, unknownFields 40, sizeCache 64, size 72) are the
generated layout `Prysm.Checkpoint.goFields` (from `prysm/ir/ir-mainnet.json`, go/types gc
amd64; TRUST: not read from the ELF's abi.Type, which has no named symbol).

`goValue b`: the 72 bytes `b` are a Go value of `v1alpha1.Checkpoint`: length
72; the two slice headers (`Root`, `unknownFields`) have `len ≤ cap < 2^63` and
a nil pointer only with `cap = 0`. (`state` is a pointer field: any word;
`sizeCache` is an int32: any 4 bytes; the 4 padding bytes are not constrained.)
The theorems below check, by evaluation, that the receiver bytes inside every
witness memory block are such Go values: before the decoder (a zero
`&Checkpoint{}`), after it (`Root` = (heap block, 32, 32)), and in the encoder
witnesses.
-/

namespace Prysm.Checkpoint

def fieldOffset (f : String) : Nat := ((goFields.find? (·.1 = f)).map (·.2.1)).getD 0

theorem layout : fieldOffset "state" = 0 ∧ fieldOffset "Epoch" = 8 ∧ fieldOffset "Root" = 16 ∧ fieldOffset "unknownFields" = 40
    ∧ fieldOffset "sizeCache" = 64 ∧ goSize = 72 := by decide

/-- Little-endian unsigned value of a byte list. -/
def u64le (l : List UInt8) : Nat := l.foldr (fun x acc => x.toNat + 256 * acc) 0

def word (b : List UInt8) (o : Nat) : Nat := u64le ((b.drop o).take 8)

/-- A Go slice header at offset `o`: `len ≤ cap < 2^63`, nil pointer only with `cap = 0`. -/
def goSliceOk (b : List UInt8) (o : Nat) : Bool :=
  decide (word b (o + 8) ≤ word b (o + 16)) && decide (word b (o + 16) < 2 ^ 63)
    && (word b o != 0 || word b (o + 16) == 0)

def goValue (b : List UInt8) : Bool :=
  decide (b.length = goSize) && goSliceOk b (fieldOffset "Root") && goSliceOk b (fieldOffset "unknownFields")

/-- The receiver bytes at offset `o` of a witness block. -/
def receiverAt (blk : List UInt8) (o : Nat) : List UInt8 := (blk.drop o).take goSize

open Witness.DecodeAccept in
/-- Decoder witness, before the call: the receiver (offset 0x5c of the block) is a zero `Checkpoint`. -/
theorem witness_decode_accept_receiver_pre : goValue (receiverAt (block (Int.toBytes 8 0x0123456789abcdef) (List.replicate 32 0xff)) 0x5c)
    = true := by decide

/-! After the decoder. The receiver bytes are not written by hand: `afterDecode b e8 p`
is the list of the receiver fragments that the conclusion of `Decode.accept` names at
`rax .. rax + 72` (`cst` = the before bytes 0..8, `e8` at +8, `p` at +16, 32 at +24 and +32, `ctl` = the
before bytes 40..72). `after_decode_goValue` holds for every before receiver that is a Go value, every
8 input bytes and every `p ≠ 0`. `MakesliceContract` does not state `p ≠ 0` (Go's makeslice with cap 32 never
returns nil, but that is not in the contract form); so the after-state Go value is conditional on
`p ≠ 0` (the witness bump allocator returns 0x1000c). -/

theorem u64le_eq_zero : ∀ (l : List UInt8), u64le l = 0 → l = List.replicate l.length 0
  | [], _ => rfl
  | x :: l, h => by
    simp only [u64le, List.foldr_cons] at h
    have h1 : x.toNat = 0 := by omega
    have h2 : u64le l = 0 := by unfold u64le; omega
    have hx : x = 0 := UInt8.toNat_inj.mp h1
    have e := u64le_eq_zero l h2
    show x :: l = List.replicate (l.length + 1) 0
    rw [List.replicate_succ, hx]; exact congrArg _ e

theorem toBytes8_ne_zero (p : BitVec 64) (hp : p ≠ 0) : u64le (Int.toBytes 8 p.toInt) ≠ 0 := by
  intro h
  have e := u64le_eq_zero _ h
  rw [Int.toBytes_length] at e
  apply hp
  rw [← Machine.ofInt_ofBytes_toBytes64 p, e]
  decide

/-- The receiver after the decoder, as the fragments of `Decode.accept`'s conclusion name it:
`state` (the before bytes 0..8), `Epoch` = the 8 input bytes, `Root` = (p, 32, 32), and the before
bytes 40..72 (`unknownFields`, `sizeCache`, padding). -/
def afterDecode (b e8 : List UInt8) (p : BitVec 64) : List UInt8 :=
  b.take 8 ++ (e8 ++ (Int.toBytes 8 p.toInt ++ (Int.toBytes 8 (32 : BitVec 64).toInt
    ++ (Int.toBytes 8 (32 : BitVec 64).toInt ++ b.drop 40))))

theorem after_decode_goValue (b e8 : List UInt8) (hb : goValue b = true) (he8 : e8.length = 8)
    (p : BitVec 64) (hp : p ≠ 0) : goValue (afterDecode b e8 p) = true := by
  have hbl : b.length = 72 := by
    simp only [goValue, Bool.and_eq_true, decide_eq_true_eq] at hb; exact hb.1.1
  have h8 : (b.take 8).length = 8 := by simp [hbl]
  have hT : ∀ x : BitVec 64, (Int.toBytes 8 x.toInt).length = 8 := fun x => Int.toBytes_length 8 _
  have hd : ∀ (l1 l2 : List UInt8) (n : Nat), l1.length = n → (l1 ++ l2).drop n = l2 :=
    fun l1 l2 n h => by subst h; simp
  have ht : ∀ (l1 l2 : List UInt8), l1.length = 8 → (l1 ++ l2).take 8 = l1 :=
    fun l1 l2 h => by rw [List.take_append_of_le_length (by omega)]; simp [← h]
  have w32 : u64le (Int.toBytes 8 (32 : BitVec 64).toInt) = 32 := by decide
  have off16 : fieldOffset "Root" = 16 := by decide
  have off40 : fieldOffset "unknownFields" = 40 := by decide
  have hsz : goSize = 72 := by decide
  have hL : (afterDecode b e8 p).length = 72 := by
    simp only [afterDecode, List.length_append, hT, he8, h8, List.length_drop, hbl]
  -- unknownFields: the same bytes as before
  have hU : ∀ o, (afterDecode b e8 p).drop (40 + o) = b.drop (40 + o) := by
    intro o
    have : (afterDecode b e8 p).drop 40 = b.drop 40 := by
      unfold afterDecode
      rw [show 40 = 8 + (8 + (8 + (8 + 8))) from rfl, ← List.drop_drop, hd _ _ _ h8, ← List.drop_drop, hd _ _ _ he8,
        ← List.drop_drop, hd _ _ _ (hT _), ← List.drop_drop, hd _ _ _ (hT _), hd _ _ _ (hT _)]
    rw [← List.drop_drop, this, List.drop_drop]
  have hR : (afterDecode b e8 p).drop 16 = Int.toBytes 8 p.toInt ++ (Int.toBytes 8 (32 : BitVec 64).toInt
      ++ (Int.toBytes 8 (32 : BitVec 64).toInt ++ b.drop 40)) := by
    unfold afterDecode
    rw [show 16 = 8 + 8 from rfl, ← List.drop_drop, hd _ _ _ h8, hd _ _ _ he8]
  have hd2 : ∀ (l1 l2 : List UInt8) (n m : Nat), l1.length = n → (l1 ++ l2).drop (n + m) = l2.drop m :=
    fun l1 l2 n m h => by rw [← List.drop_drop, hd _ _ _ h]
  have hR8 : (afterDecode b e8 p).drop (16 + 8) = Int.toBytes 8 (32 : BitVec 64).toInt
      ++ (Int.toBytes 8 (32 : BitVec 64).toInt ++ b.drop 40) := by
    rw [← List.drop_drop, hR, hd _ _ _ (hT _)]
  have hR16 : (afterDecode b e8 p).drop (16 + 16) = Int.toBytes 8 (32 : BitVec 64).toInt ++ b.drop 40 := by
    rw [show 16 + 16 = 16 + 8 + 8 from rfl, ← List.drop_drop, hR8, hd _ _ _ (hT _)]
  have e0 := hU 0; have e8' := hU 8; have e16 := hU 16
  simp only [Nat.add_zero] at e0
  have hb' := hb
  simp only [goValue, Bool.and_eq_true, decide_eq_true_eq, off16, off40, hsz] at hb' ⊢
  refine ⟨⟨hL, ?_⟩, ?_⟩
  · simp only [goSliceOk, word, hR, hR8, hR16, ht _ _ (hT _), w32]
    have := toBytes8_ne_zero p hp
    simp [this]
  · simp only [goSliceOk, word, e0, e8', e16] at hb' ⊢
    exact hb'.2
open Witness.DecodeAccept in
/-- Decoder witness, after the call: the receiver from the conclusion fragments over the witness block. -/
theorem witness_decode_accept_receiver_post (p : BitVec 64) (hp : p ≠ 0) :
    goValue (afterDecode (receiverAt (block (Int.toBytes 8 0x0123456789abcdef) (List.replicate 32 0xff)) 0x5c)
      (Int.toBytes 8 0x0123456789abcdef) p) = true :=
  after_decode_goValue _ _ witness_decode_accept_receiver_pre (by decide) p hp

open Witness.EncodeFastPath in
/-- Encoder witnesses: the receiver at offset 8 (Root = (0x10050, 32, 32)). -/
theorem witness_encode_fast_path_receiver : goValue (receiverAt (block (Int.toBytes 8 0x0123456789abcdef) (List.replicate 32 0xff)
    [] []) 8) = true := by decide

open Witness.EncodeRejectLength in
/-- Encoder reject witness: the receiver at offset 24 with `len(Root)` 31, 33, 0 and cap 48. -/
theorem witness_encode_reject_length_receiver : goValue (receiverAt (block (Int.toBytes 8 7) 31) 24) = true
    ∧ goValue (receiverAt (block (Int.toBytes 8 7) 33) 24) = true
    ∧ goValue (receiverAt (block (Int.toBytes 8 7) 0) 24) = true := by decide

/-- Control: a header with `len > cap` is not a Go value. -/
theorem goValue_rejects_bad : goValue (List.replicate 24 0 ++ Int.toBytes 8 33 ++ Int.toBytes 8 32
    ++ List.replicate 32 0) = false := by decide

end Prysm.Checkpoint
