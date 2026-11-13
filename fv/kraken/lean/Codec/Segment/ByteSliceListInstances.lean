import Codec.Segment.ByteSliceList
import Prysm.HistoricalBatch.DecodeLoopLemmas

/-!
# The fixed list lemmas of SyncCommittee and HistoricalBatch as instances of `Codec.Segment.ByteSliceList`

Each hand lemma's statement is proved from the general lemma by one `exact` (new names; `Prysm/SyncCommittee/DecodeLoopLemmas.lean` and
`Prysm/HistoricalBatch/DecodeLoopLemmas.lean` are unchanged). This is the check that the general statements cover the copied ones.
-/

open Machine Runtime

namespace Codec.Segment

theorem flatten_length_sync_committee (qs : List (List UInt8)) (h : ∀ e ∈ qs, e.length = 48) :
    qs.flatten.length = 48 * qs.length := flat_len 48 qs h
theorem flatten_length_historical_batch (qs : List (List UInt8)) (h : ∀ e ∈ qs, e.length = 32) :
    qs.flatten.length = 32 * qs.length := flat_len 32 qs h

theorem input_split_sync_committee (bf : BitVec 64) (pks : List (List UInt8)) (hpks : pks.length = 512)
    (hpk : ∀ e ∈ pks, e.length = 48) (i : Nat) (hi : i < 512) :
    Eq (pks.flatten.At bf) = Eq ((pks.take i).flatten.At bf) ⋆ Eq (pks[i].At (bf + BitVec.ofNat 64 (48 * i)))
      ⋆ Eq ((pks.drop (i + 1)).flatten.At (bf + BitVec.ofNat 64 (48 * i) + 48)) :=
  in_split 48 512 (by decide) bf pks hpks hpk i hi
theorem input_split_historical_batch (bf : BitVec 64) (pks : List (List UInt8)) (hpks : pks.length = 8192)
    (hpk : ∀ e ∈ pks, e.length = 32) (i : Nat) (hi : i < 8192) :
    Eq (pks.flatten.At bf) = Eq ((pks.take i).flatten.At bf) ⋆ Eq (pks[i].At (bf + BitVec.ofNat 64 (32 * i)))
      ⋆ Eq ((pks.drop (i + 1)).flatten.At (bf + BitVec.ofNat 64 (32 * i) + 32)) :=
  in_split 32 8192 (by decide) bf pks hpks hpk i hi

theorem array_split_sync_committee (A : BitVec 64) (ps : List (BitVec 64)) (i : Nat) (hi : i < 512) (hps : ps.length = i) :
    Eq ((Codec.sliceHeaders 48 ps ++ Codec.zeroBytes (24 * (512 - i))).At A) = Eq ((Codec.sliceHeaders 48 ps).At A)
      ⋆ Eq ((Codec.zeroBytes 8).At (A + BitVec.ofNat 64 (24 * i))) ⋆ Eq ((Codec.zeroBytes 8).At (A + BitVec.ofNat 64 (24 * i) + 8))
      ⋆ Eq ((Codec.zeroBytes 8).At (A + BitVec.ofNat 64 (24 * i) + 16))
      ⋆ Eq ((Codec.zeroBytes (24 * (512 - (i + 1)))).At (A + BitVec.ofNat 64 (24 * i) + 24)) :=
  backing_array_split 512 (by decide) 48 A ps i hi hps
theorem array_split_historical_batch (A : BitVec 64) (ps : List (BitVec 64)) (i : Nat) (hi : i < 8192) (hps : ps.length = i) :
    Eq ((Codec.sliceHeaders 32 ps ++ Codec.zeroBytes (24 * (8192 - i))).At A) = Eq ((Codec.sliceHeaders 32 ps).At A)
      ⋆ Eq ((Codec.zeroBytes 8).At (A + BitVec.ofNat 64 (24 * i))) ⋆ Eq ((Codec.zeroBytes 8).At (A + BitVec.ofNat 64 (24 * i) + 8))
      ⋆ Eq ((Codec.zeroBytes 8).At (A + BitVec.ofNat 64 (24 * i) + 16))
      ⋆ Eq ((Codec.zeroBytes (24 * (8192 - (i + 1)))).At (A + BitVec.ofNat 64 (24 * i) + 24)) :=
  backing_array_split 8192 (by decide) 32 A ps i hi hps

theorem array_join_sync_committee (A p : BitVec 64) (ps : List (BitVec 64)) (i : Nat) (hi : i < 512) (hps : ps.length = i) :
    Eq ((Codec.sliceHeaders 48 (ps ++ [p]) ++ Codec.zeroBytes (24 * (512 - (i + 1)))).At A) = Eq ((Codec.sliceHeaders 48 ps).At A)
      ⋆ Eq ((Int.toBytes 8 p.toInt).At (A + BitVec.ofNat 64 (24 * i)))
      ⋆ Eq ((Int.toBytes 8 48).At (A + BitVec.ofNat 64 (24 * i) + 8))
      ⋆ Eq ((Int.toBytes 8 48).At (A + BitVec.ofNat 64 (24 * i) + 16))
      ⋆ Eq ((Codec.zeroBytes (24 * (512 - (i + 1)))).At (A + BitVec.ofNat 64 (24 * i) + 24)) :=
  backing_array_join 512 (by decide) 48 A p ps i hi hps
theorem array_join_historical_batch (A p : BitVec 64) (ps : List (BitVec 64)) (i : Nat) (hi : i < 8192) (hps : ps.length = i) :
    Eq ((Codec.sliceHeaders 32 (ps ++ [p]) ++ Codec.zeroBytes (24 * (8192 - (i + 1)))).At A) = Eq ((Codec.sliceHeaders 32 ps).At A)
      ⋆ Eq ((Int.toBytes 8 p.toInt).At (A + BitVec.ofNat 64 (24 * i)))
      ⋆ Eq ((Int.toBytes 8 32).At (A + BitVec.ofNat 64 (24 * i) + 8))
      ⋆ Eq ((Int.toBytes 8 32).At (A + BitVec.ofNat 64 (24 * i) + 16))
      ⋆ Eq ((Codec.zeroBytes (24 * (8192 - (i + 1)))).At (A + BitVec.ofNat 64 (24 * i) + 24)) :=
  backing_array_join 8192 (by decide) 32 A p ps i hi hps

/-- The statements are the hand ones: each hand lemma follows from its instance by `exact`. -/
example : @Prysm.SyncCommittee.Decode.input_split = @input_split_sync_committee := rfl
example : @Prysm.HistoricalBatch.Decode.input_split = @input_split_historical_batch := rfl
example : @Prysm.SyncCommittee.Decode.array_split = @array_split_sync_committee := rfl
example : @Prysm.SyncCommittee.Decode.array_join = @array_join_sync_committee := rfl
example : @Prysm.HistoricalBatch.Decode.array_split = @array_split_historical_batch := rfl
example : @Prysm.HistoricalBatch.Decode.array_join = @array_join_historical_batch := rfl

end Codec.Segment
