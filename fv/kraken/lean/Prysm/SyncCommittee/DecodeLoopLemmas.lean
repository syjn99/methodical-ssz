import Machine.Frame
import Machine.Block
import Prysm.SyncCommittee.SpecDefinitions

/-!
# List and memory-chunk lemmas for the SyncCommittee element loop

- `elementBlocks_snoc`, `sliceHeaders_length`, `sliceHeaders_snoc`: the two loop objects of `Prysm/SyncCommittee/SpecDefinitions.lean` grow by one element.
- `flatten_length`, `flatten_split`: the input `pks.flatten` (512 blocks of 48 bytes) around block i.
- `Decode.input_split`: the input chunk as (blocks < i) ⋆ block i ⋆ (blocks > i).
- `Decode.array_split`, `Decode.array_join`: the backing array (headers of the first i elements, then zeros) around element i,
  before (three zero words) and after (the header `(p, 48, 48)`) the three stores of iteration i.
- `jge_false512`: `cmp $0x200, a; jge` is not taken when a < 512 (the text of `Machine.jge_false` with a wider bound).
-/

open Machine Runtime TestTarget

namespace Prysm.SyncCommittee

abbrev zz (n : Nat) : List UInt8 := List.replicate n 0

theorem elementBlocks_snoc (ps : List (BitVec 64)) (es : List (List UInt8)) (p : BitVec 64) (e : List UInt8)
    (h : ps.length = es.length) :
    elementBlocks (ps ++ [p]) (es ++ [e]) = elementBlocks ps es ⋆ Eq (e.At p) := by
  induction ps generalizing es with
  | nil =>
    cases es with
    | nil => simp only [List.nil_append, elementBlocks, Std.ExtHashMap.emp_sep, Std.ExtHashMap.sep_emp]
    | cons _ _ => simp at h
  | cons q qs ih =>
    cases es with
    | nil => simp at h
    | cons f fs =>
      simp only [List.cons_append, elementBlocks]
      rw [ih fs (by simpa using h), Std.ExtHashMap.sep_assoc]

theorem sliceHeaders_length (w : Int) (ps : List (BitVec 64)) : (sliceHeaders w ps).length = 24 * ps.length := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp [sliceHeaders, Int.toBytes_length] at ih ⊢; omega

theorem sliceHeaders_snoc (w : Int) (ps : List (BitVec 64)) (p : BitVec 64) :
    sliceHeaders w (ps ++ [p]) = sliceHeaders w ps ++ (Int.toBytes 8 p.toInt ++ (Int.toBytes 8 w ++ Int.toBytes 8 w)) := by
  simp [sliceHeaders, List.append_assoc]

theorem flatten_length (qs : List (List UInt8)) (h : ∀ e ∈ qs, e.length = 48) :
    qs.flatten.length = 48 * qs.length := by
  induction qs with
  | nil => rfl
  | cons q qs ih =>
    simp only [List.flatten_cons, List.length_append, List.length_cons]
    rw [h q (List.mem_cons_self), ih (fun e he => h e (List.mem_cons_of_mem _ he))]; omega

theorem flatten_split (pks : List (List UInt8)) (i : Nat) (hi : i < pks.length) :
    pks.flatten = (pks.take i).flatten ++ (pks[i] ++ (pks.drop (i + 1)).flatten) := by
  have e : pks = pks.take i ++ (pks[i] :: pks.drop (i + 1)) := by
    rw [← List.drop_eq_getElem_cons hi, List.take_append_drop]
  calc pks.flatten = (pks.take i ++ (pks[i] :: pks.drop (i + 1))).flatten := congrArg List.flatten e
    _ = _ := by rw [List.flatten_append, List.flatten_cons]

theorem Decode.input_split (bf : BitVec 64) (pks : List (List UInt8)) (hpks : pks.length = 512)
    (hpk : ∀ e ∈ pks, e.length = 48) (i : Nat) (hi : i < 512) :
    Eq (pks.flatten.At bf) = Eq ((pks.take i).flatten.At bf) ⋆ Eq (pks[i].At (bf + BitVec.ofNat 64 (48 * i)))
      ⋆ Eq ((pks.drop (i + 1)).flatten.At (bf + BitVec.ofNat 64 (48 * i) + 48)) := by
  have hlt : i < pks.length := by omega
  have ht : (pks.take i).flatten.length = 48 * i := by
    rw [flatten_length _ (fun e he => hpk e (List.mem_of_mem_take he))]; simp; omega
  have hp : pks[i].length = 48 := hpk _ (List.getElem_mem hlt)
  have hd : (pks.drop (i + 1)).flatten.length = 48 * (511 - i) := by
    rw [flatten_length _ (fun e he => hpk e (List.mem_of_mem_drop he))]; simp; omega
  rw [flatten_split pks i hlt,
    at_app _ _ (b := bf + BitVec.ofNat 64 (48 * i)) (by rw [ht]) (by simp only [List.length_append, ht, hp, hd]; omega),
    at_app _ _ (b := bf + BitVec.ofNat 64 (48 * i) + 48) (by rw [hp]; rfl) (by rw [hp, hd]; omega)]
  simp only [Std.ExtHashMap.sep_assoc]

theorem Decode.array_split (A : BitVec 64) (ps : List (BitVec 64)) (i : Nat) (hi : i < 512) (hps : ps.length = i) :
    Eq ((sliceHeaders 48 ps ++ zz (24 * (512 - i))).At A) = Eq ((sliceHeaders 48 ps).At A)
      ⋆ Eq ((zz 8).At (A + BitVec.ofNat 64 (24 * i))) ⋆ Eq ((zz 8).At (A + BitVec.ofNat 64 (24 * i) + 8))
      ⋆ Eq ((zz 8).At (A + BitVec.ofNat 64 (24 * i) + 16))
      ⋆ Eq ((zz (24 * (512 - (i + 1)))).At (A + BitVec.ofNat 64 (24 * i) + 24)) := by
  have hl := sliceHeaders_length 48 ps
  rw [show zz (24 * (512 - i)) = zz 8 ++ (zz 8 ++ (zz 8 ++ zz (24 * (512 - (i + 1))))) by
      simp only [zz, List.replicate_append_replicate]; congr 1; omega,
    at_app _ _ (b := A + BitVec.ofNat 64 (24 * i)) (by rw [hl, hps]) (by simp [hl, hps]; omega),
    at_app _ _ (b := A + BitVec.ofNat 64 (24 * i) + 8) (by simp) (by simp; omega),
    at_app _ _ (b := A + BitVec.ofNat 64 (24 * i) + 16) (by simp; bv_omega) (by simp; omega),
    at_app _ _ (b := A + BitVec.ofNat 64 (24 * i) + 24) (by simp; bv_omega) (by simp; omega)]
  simp only [Std.ExtHashMap.sep_assoc]

theorem Decode.array_join (A p : BitVec 64) (ps : List (BitVec 64)) (i : Nat) (hi : i < 512) (hps : ps.length = i) :
    Eq ((sliceHeaders 48 (ps ++ [p]) ++ zz (24 * (512 - (i + 1)))).At A) = Eq ((sliceHeaders 48 ps).At A)
      ⋆ Eq ((Int.toBytes 8 p.toInt).At (A + BitVec.ofNat 64 (24 * i)))
      ⋆ Eq ((Int.toBytes 8 48).At (A + BitVec.ofNat 64 (24 * i) + 8))
      ⋆ Eq ((Int.toBytes 8 48).At (A + BitVec.ofNat 64 (24 * i) + 16))
      ⋆ Eq ((zz (24 * (512 - (i + 1)))).At (A + BitVec.ofNat 64 (24 * i) + 24)) := by
  have hl := sliceHeaders_length 48 ps
  rw [sliceHeaders_snoc, List.append_assoc, List.append_assoc, List.append_assoc,
    at_app _ _ (b := A + BitVec.ofNat 64 (24 * i)) (by rw [hl, hps])
      (by simp [hl, hps, Int.toBytes_length]; omega),
    at_app _ _ (b := A + BitVec.ofNat 64 (24 * i) + 8) (by simp [Int.toBytes_length])
      (by simp [Int.toBytes_length]; omega),
    at_app _ _ (b := A + BitVec.ofNat 64 (24 * i) + 16) (by simp [Int.toBytes_length]; bv_omega)
      (by simp [Int.toBytes_length]; omega),
    at_app _ _ (b := A + BitVec.ofNat 64 (24 * i) + 24) (by simp [Int.toBytes_length]; bv_omega)
      (by simp [Int.toBytes_length]; omega)]
  simp only [Std.ExtHashMap.sep_assoc]

/-- `cmp b, a; jge` is not taken when `a < b < 2^62` (the text of `Machine.jge_false`, bound 2^62 instead of 16). -/
theorem jge_false512 (a b : BitVec 64) (hb : b.toNat < 2 ^ 62) (hab : a.toNat < b.toNat)
    (h : (a - b).msb = ((a.toInt - b.toInt).bmod 18446744073709551616 != a.toInt - b.toInt)) : False := by
  have ta : a.toInt = a.toNat := BitVec.toInt_eq_toNat_of_lt (by omega)
  have tb : b.toInt = b.toNat := BitVec.toInt_eq_toNat_of_lt (by omega)
  rw [ta, tb] at h
  have hm : (((a.toNat : Int) - b.toNat).bmod 18446744073709551616) = (a.toNat : Int) - b.toNat := by
    apply Int.bmod_eq_of_le <;> omega
  rw [hm] at h
  simp only [bne_self_eq_false] at h
  have hs : (a - b).msb = true := by
    rw [BitVec.msb_eq_decide]; simp [BitVec.toNat_sub]; omega
  rw [hs] at h; exact Bool.noConfusion h

end Prysm.SyncCommittee
