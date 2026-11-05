import Fk.Step

/-! Byte facts for the stored values. -/

namespace Fk
open Std

/-- A chunk loaded at width `w = 8n` and stored back at the same width is unchanged. -/
theorem toBytes_ofInt_ofBytes (w n : Nat) (hw : w = 8 * n) (bs : List UInt8) (h : bs.length = n) :
    Int.toBytes n (BitVec.ofInt w (Int.ofBytes bs)).toInt = bs := by
  subst hw
  rw [BitVec.toInt_ofInt, show (2 : Nat) ^ (8 * n) = 256 ^ n by rw [Nat.pow_mul]]
  exact_mod_cast Int.toBytes_bmod_ofBytes n bs h

theorem zx8 (x : BitVec 8) : BitVec.extractLsb' 0 8 (BitVec.zeroExtend 64 (BitVec.zeroExtend 32 x)) = x := by
  bv_decide
theorem zx16 (x : BitVec 16) : BitVec.extractLsb' 0 16 (BitVec.zeroExtend 64 (BitVec.zeroExtend 32 x)) = x := by
  bv_decide
theorem zx32 (x : BitVec 32) : BitVec.extractLsb' 0 32 (BitVec.zeroExtend 64 x) = x := by
  bv_decide

theorem sep_true {P F : DataMem → Prop} {m : DataMem} (h : (P ⋆ F) m) : (P ⋆ fun _ => True) m := by
  obtain ⟨m1, m2, h1, h2, hp, -⟩ := h
  exact ⟨m1, m2, h1, h2, hp, trivial⟩

/-- Drop the last atom of a left-nested chain into the `True` frame. -/
theorem sep_drop {Q X : DataMem → Prop} {m : DataMem} (h : ((Q ⋆ X) ⋆ fun _ => True) m) :
    (Q ⋆ fun _ => True) m := by
  rw [Std.ExtHashMap.sep_assoc] at h
  obtain ⟨a, b, hu, hi, hq, -⟩ := h
  exact ⟨a, b, hu, hi, hq, trivial⟩

end Fk
