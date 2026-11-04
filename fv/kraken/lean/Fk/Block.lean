import Fk.Bytes

/-! Splitting a byte block around an 8-byte element (for loops over arrays). -/

namespace Fk
open Std

theorem block_split (bs : List UInt8) (a : BitVec 64) (o : Nat) (h : o + 8 ≤ bs.length)
    (hl : bs.length < 2 ^ 64) :
    Eq (bs.At a) = Eq ((bs.take o).At a) ⋆ Eq (((bs.drop o).take 8).At (a + BitVec.ofNat 64 o))
      ⋆ Eq ((bs.drop (o + 8)).At (a + BitVec.ofNat 64 o + 8)) := by
  have e1 : bs = bs.take o ++ ((bs.drop o).take 8 ++ bs.drop (o + 8)) := by
    rw [← List.drop_drop, List.take_append_drop, List.take_append_drop]
  conv => lhs; rw [e1]
  rw [Mem.At_append_sep _ _ _ (by simp; omega), Mem.At_append_sep _ _ _ (by simp; omega),
    ← Std.ExtHashMap.sep_assoc]
  have l1 : (bs.take o).length = o := by simp; omega
  have l2 : ((bs.drop o).take 8).length = 8 := by simp; omega
  rw [l1, l2]; rfl

theorem out_next (bs : List UInt8) (n i : Nat) (hbs : bs.length = 8 * n) (hi : i < n) :
    bs.take (8 * i) ++ List.replicate (8 * (n - i)) 0 =
      bs.take (8 * i) ++ (List.replicate 8 0 ++ List.replicate (8 * (n - (i + 1))) 0) := by
  rw [List.replicate_append_replicate]; congr 2; omega

theorem out_step (bs : List UInt8) (n i : Nat) (hbs : bs.length = 8 * n) (hi : i < n) :
    bs.take (8 * i) ++ ((bs.drop (8 * i)).take 8 ++ List.replicate (8 * (n - (i + 1))) 0) =
      bs.take (8 * (i + 1)) ++ List.replicate (8 * (n - (i + 1))) 0 := by
  rw [← List.append_assoc, ← List.take_add, show 8 * i + 8 = 8 * (i + 1) by omega]

/-- `cmp b, a; jge` is not taken when `a < b ≤ 16`. -/
theorem jge_false (a b : BitVec 64) (hb : b.toNat ≤ 16) (hab : a.toNat < b.toNat)
    (h : (a - b).msb = ((a.toInt - b.toInt).bmod 18446744073709551616 != a.toInt - b.toInt)) : False := by
  have ta : a.toInt = a.toNat := BitVec.toInt_eq_toNat_of_lt (by omega)
  have tb : b.toInt = b.toNat := BitVec.toInt_eq_toNat_of_lt (by omega)
  rw [ta, tb] at h
  have hm : (((a.toNat : Int) - b.toNat).bmod 18446744073709551616) = (a.toNat : Int) - b.toNat := by
    apply Int.bmod_eq_of_le <;> omega
  rw [hm] at h
  simp only [bne_self_eq_false] at h
  rw [BitVec.msb_eq_decide, BitVec.toNat_sub] at h
  simp at h; omega

end Fk
