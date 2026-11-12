import Machine.Frame
import Machine.Block
import E2eList.ScLemmas

/-!
# List and memory-chunk lemmas of the `[][]byte` element loops, for any element width `w` and count `n`

Generalized once from `E2eList.ScLemmas` (w = 48, n = 512) and `E2eHb.HbLemmas` (w = 32, n = 8192).
Side conditions: the input bytes and the backing array fit in the address space (`w * n ≤ 2^64`,
`24 * n ≤ 2^64`); the SyncCommittee / HistoricalBatch instances discharge them by `decide`/`omega`. The fixed instances are re-derived in
`Codec/Segment/ByteSliceListInstances.lean`. The size-free SyncCommittee lemmas (`lvElems_snoc`, `lvHdrs_length`, `lvHdrs_snoc`,
`lv_flatten_split`) are imported, not restated.
-/

open Machine Runtime TestTarget E2eList

namespace Codec.Segment

theorem flat_len (w : Nat) (qs : List (List UInt8)) (h : ∀ e ∈ qs, e.length = w) :
    qs.flatten.length = w * qs.length := by
  induction qs with
  | nil => simp
  | cons q qs ih =>
    simp only [List.flatten_cons, List.length_append, List.length_cons]
    rw [h q (List.mem_cons_self), ih (fun e he => h e (List.mem_cons_of_mem _ he))]
    rw [Nat.mul_succ]; omega

/-- The input chunk as (blocks < i) ⋆ block i ⋆ (blocks > i). -/
theorem in_split (w n : Nat) (hsz : w * n ≤ 2 ^ 64) (bf : BitVec 64) (pks : List (List UInt8))
    (hpks : pks.length = n) (hpk : ∀ e ∈ pks, e.length = w) (i : Nat) (hi : i < n) :
    Eq (pks.flatten.At bf) = Eq ((pks.take i).flatten.At bf) ⋆ Eq (pks[i].At (bf + BitVec.ofNat 64 (w * i)))
      ⋆ Eq ((pks.drop (i + 1)).flatten.At (bf + BitVec.ofNat 64 (w * i) + BitVec.ofNat 64 w)) := by
  have hlt : i < pks.length := by omega
  have ht : (pks.take i).flatten.length = w * i := by
    rw [flat_len w _ (fun e he => hpk e (List.mem_of_mem_take he)), List.length_take, Nat.min_eq_left (by omega)]
  have hp : pks[i].length = w := hpk _ (List.getElem_mem hlt)
  have hd : (pks.drop (i + 1)).flatten.length = w * (n - (i + 1)) := by
    rw [flat_len w _ (fun e he => hpk e (List.mem_of_mem_drop he)), List.length_drop, hpks]
  have hmul : w * i + (w + w * (n - (i + 1))) = w * n := by
    obtain ⟨m, hm⟩ : ∃ m, n = i + 1 + m := ⟨n - (i + 1), by omega⟩
    subst hm
    rw [show i + 1 + m - (i + 1) = m by omega, Nat.mul_add, Nat.mul_add, Nat.mul_one]; omega
  rw [lv_flatten_split pks i hlt,
    at_app _ _ (b := bf + BitVec.ofNat 64 (w * i)) (by rw [ht]) (by simp only [List.length_append, ht, hp, hd]; omega),
    at_app _ _ (b := bf + BitVec.ofNat 64 (w * i) + BitVec.ofNat 64 w) (by rw [hp])
      (by rw [hp, hd]; omega)]
  simp only [Std.ExtHashMap.sep_assoc]

/-- The backing array (headers of the first i elements, then zeros) around element i, before the three stores. -/
theorem arr_split (n : Nat) (hsz : 24 * n ≤ 2 ^ 64) (w : Int) (A : BitVec 64) (ps : List (BitVec 64)) (i : Nat)
    (hi : i < n) (hps : ps.length = i) :
    Eq ((lvHdrs w ps ++ zz (24 * (n - i))).At A) = Eq ((lvHdrs w ps).At A)
      ⋆ Eq ((zz 8).At (A + BitVec.ofNat 64 (24 * i))) ⋆ Eq ((zz 8).At (A + BitVec.ofNat 64 (24 * i) + 8))
      ⋆ Eq ((zz 8).At (A + BitVec.ofNat 64 (24 * i) + 16))
      ⋆ Eq ((zz (24 * (n - (i + 1)))).At (A + BitVec.ofNat 64 (24 * i) + 24)) := by
  have hl := lvHdrs_length w ps
  rw [show zz (24 * (n - i)) = zz 8 ++ (zz 8 ++ (zz 8 ++ zz (24 * (n - (i + 1))))) by
      simp only [zz, List.replicate_append_replicate]; congr 1; omega,
    at_app _ _ (b := A + BitVec.ofNat 64 (24 * i)) (by rw [hl, hps]) (by simp [hl, hps]; omega),
    at_app _ _ (b := A + BitVec.ofNat 64 (24 * i) + 8) (by simp) (by simp; omega),
    at_app _ _ (b := A + BitVec.ofNat 64 (24 * i) + 16) (by simp; bv_omega) (by simp; omega),
    at_app _ _ (b := A + BitVec.ofNat 64 (24 * i) + 24) (by simp; bv_omega) (by simp; omega)]
  simp only [Std.ExtHashMap.sep_assoc]

/-- The backing array after the three stores of iteration i (header `(p, w, w)`). -/
theorem arr_join (n : Nat) (hsz : 24 * n ≤ 2 ^ 64) (w : Int) (A p : BitVec 64) (ps : List (BitVec 64)) (i : Nat)
    (hi : i < n) (hps : ps.length = i) :
    Eq ((lvHdrs w (ps ++ [p]) ++ zz (24 * (n - (i + 1)))).At A) = Eq ((lvHdrs w ps).At A)
      ⋆ Eq ((Int.toBytes 8 p.toInt).At (A + BitVec.ofNat 64 (24 * i)))
      ⋆ Eq ((Int.toBytes 8 w).At (A + BitVec.ofNat 64 (24 * i) + 8))
      ⋆ Eq ((Int.toBytes 8 w).At (A + BitVec.ofNat 64 (24 * i) + 16))
      ⋆ Eq ((zz (24 * (n - (i + 1)))).At (A + BitVec.ofNat 64 (24 * i) + 24)) := by
  have hl := lvHdrs_length w ps
  rw [lvHdrs_snoc, List.append_assoc, List.append_assoc, List.append_assoc,
    at_app _ _ (b := A + BitVec.ofNat 64 (24 * i)) (by rw [hl, hps])
      (by simp [hl, hps, Int.toBytes_length]; omega),
    at_app _ _ (b := A + BitVec.ofNat 64 (24 * i) + 8) (by simp [Int.toBytes_length])
      (by simp [Int.toBytes_length]; omega),
    at_app _ _ (b := A + BitVec.ofNat 64 (24 * i) + 16) (by simp [Int.toBytes_length]; bv_omega)
      (by simp [Int.toBytes_length]; omega),
    at_app _ _ (b := A + BitVec.ofNat 64 (24 * i) + 24) (by simp [Int.toBytes_length]; bv_omega)
      (by simp [Int.toBytes_length]; omega)]
  simp only [Std.ExtHashMap.sep_assoc]

end Codec.Segment
