import Fk.Step

/-! Branch-condition lemmas stated once, so the kernel does not re-check
arithmetic on 64-bit literals at every use (`simp` + `omega` proof terms with
literals near 2^64 make the kernel report deep recursion). -/

namespace Fk

theorem toNat_add_neg8 (x : BitVec 64) (h : 8 ≤ x.toNat) : (x + -8).toNat = x.toNat - 8 := by
  rw [← BitVec.sub_eq_add_neg, BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; simpa using h)]; rfl

/-- `cmp b, a; jbe` is not taken when `b < a` (unsigned). -/
theorem cmp_be_false (a b : BitVec 64) (af of' : Bool) (h : b.toNat < a.toNat) :
    CondCode.be.interp (StatusFlags.from_result (a - b)
      { cf := BitVec.unsigned (a - b) != a.unsigned - b.unsigned, af := af, of := of' }) = false := by
  have hle : b ≤ a := by rw [BitVec.le_def]; omega
  have hs : (a - b).toNat = a.toNat - b.toNat := BitVec.toNat_sub_of_le hle
  have hz : a - b ≠ 0#64 := by
    intro h0; have := congrArg BitVec.toNat h0; rw [hs] at this; simp at this; omega
  simp only [CondCode.interp, StatusFlags.from_result, BitVec.unsigned, hs]
  simp [hz]; omega

theorem sub4_toNat (x : BitVec 64) (n : Nat) (_hn : n ≤ 16) (h : x.toNat = 4 + 8 * n) :
    (-4 + x).toNat = 8 * n := by
  rw [BitVec.add_comm, ← BitVec.sub_eq_add_neg, BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; simp; omega)]
  simp; omega

/-- `(len - 4) & 7 == 0` for `len = 4 + 8n`. -/
theorem and7_zero (x : BitVec 64) (n : Nat) (hn : n ≤ 16) (h : x.toNat = 4 + 8 * n) :
    (-4 + x) &&& 7 = 0#64 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, sub4_toNat x n hn h, show (7 : BitVec 64).toNat = 2 ^ 3 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod]
  simp

theorem shr3_toNat (x : BitVec 64) (n : Nat) (hn : n ≤ 16) (h : x.toNat = 4 + 8 * n) :
    (BitVec.ushiftRight (-4 + x) 3).toNat = n := by
  rw [show (-4 + x).ushiftRight 3 = (-4 + x) >>> 3 from rfl, BitVec.toNat_ushiftRight, sub4_toNat x n hn h, Nat.shiftRight_eq_div_pow]
  all_goals omega

/-- `cmp $16, a; jg` is not taken when `a ≤ 16`. -/
theorem jg16_false (a : BitVec 64) (af : Bool) (h : a.toNat ≤ 16) :
    CondCode.g.interp (StatusFlags.from_result (a - 16)
      { cf := BitVec.unsigned (a - 16) != a.unsigned - BitVec.unsigned (16 : BitVec 64), af := af,
        of := BitVec.toInt (a - 16) != a.toInt - BitVec.toInt (16 : BitVec 64) }) = false := by
  have ta : a.toInt = a.toNat := BitVec.toInt_eq_toNat_of_lt (by omega)
  have t16 : BitVec.toInt (16 : BitVec 64) = 16 := by decide
  have hs : (a - 16).toInt = (a.toNat : Int) - 16 := by
    rw [BitVec.toInt_sub, ta, t16]; apply Int.bmod_eq_of_le <;> omega
  by_cases h16 : a.toNat = 16
  · have : a - 16 = 0#64 := by apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_sub]; omega
    simp [CondCode.interp, StatusFlags.from_result]
    intro h1; exact absurd this h1
  · have hm : (a - 16).msb = true := by
      rw [BitVec.msb_eq_decide]; simp [BitVec.toNat_sub]; omega
    simp [CondCode.interp, StatusFlags.from_result, ta]
    intro _
    rw [show (a - 16#64).msb = true from hm, Int.bmod_eq_of_le (by omega) (by omega)]; simp

/-- Return-address slot of the `call` in ListU64.UnmarshalSSZ (frame of 0x80 + saved rbp). -/
theorem call_slot (x : BitVec 64) : -128 + (x - 8#64) - 8#64 = x - 144 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_neg, BitVec.toNat_ofNat, BitVec.ofNat_eq_ofNat]
  omega

/-- Data pointer of ListU64.UnmarshalSSZ: `buf + (cap-4 == 0 ? 0 : 4)` via neg/sar/and. -/
theorem dptr4 (y : BitVec 64) (h0 : 0 < y.toNat) (h1 : y.toNat < 2 ^ 63) :
    BitVec.zeroExtend 64 (BitVec.extractLsb' 0 32 (BitVec.sshiftRight (-y) 63) &&& BitVec.truncate 32 (4 : BitVec 64)) = 4 := by
  have hz : (-y).toInt = -(y.toNat : Int) := by
    rw [BitVec.toInt_neg, BitVec.toInt_eq_toNat_of_lt (by omega)]
    apply Int.bmod_eq_of_le <;> omega
  have hs : BitVec.sshiftRight (-y) 63 = BitVec.allOnes 64 := by
    apply BitVec.eq_of_toInt_eq
    rw [BitVec.toInt_sshiftRight, hz, BitVec.toInt_allOnes]
    simp [Int.shiftRight_eq_div_pow]
    omega
  rw [hs]; decide

theorem toNat_add_neg4 (x : BitVec 64) (h : 4 ≤ x.toNat) : (x + -4).toNat = x.toNat - 4 := by
  rw [← BitVec.sub_eq_add_neg, BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; simpa using h)]; rfl

theorem frame_ret (x : BitVec 64) : (BitVec.ofNat 64 128 + ((x - 144) + 8)) = x - 8 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.ofNat_eq_ofNat]
  omega

theorem cap_sub4 (rdi : UInt64) (n : Nat) (hc : 4 + 8 * n ≤ rdi.toNat) :
    8 * n ≤ (rdi.toBitVec + -4).toNat := by
  rw [toNat_add_neg4 _ (by simp; omega)]; simp; omega

theorem dptr_buf (rbx rdi : UInt64) (n : Nat) (hn : 0 < n) (hc : 4 + 8 * n ≤ rdi.toNat)
    (h63 : rdi.toNat < 2 ^ 63) :
    rbx.toBitVec + BitVec.zeroExtend 64
      (BitVec.extractLsb' 0 32 (BitVec.sshiftRight (-(rdi.toBitVec + -4)) 63) &&& BitVec.truncate 32 (4 : BitVec 64))
      = rbx.toBitVec + 4 := by
  have := cap_sub4 rdi n hc
  rw [dptr4 _ (by omega) (by rw [toNat_add_neg4 _ (by simp; omega)]; simp; omega)]

/-- Saved-rbp slot after the callee returned (`rsp+8`) and the frame was released. -/
theorem pop_slot (x : BitVec 64) : ({ toBitVec := x - 144 } + 8 : UInt64).toBitVec - -128 = x - 8 := by
  apply BitVec.eq_of_toNat_eq
  simp only [UInt64.toBitVec_add, UInt64.toBitVec_ofNat, BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_neg,
    BitVec.toNat_ofNat, BitVec.ofNat_eq_ofNat]
  omega

theorem ret_slot (x : BitVec 64) : x - 8 + 8#64 = x := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.ofNat_eq_ofNat]
  omega

end Fk
