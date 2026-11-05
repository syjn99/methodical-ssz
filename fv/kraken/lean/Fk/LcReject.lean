import Fk.NeReject
import Fk.LuRejectCall

/-!
# ListC.UnmarshalSSZ (List[ListU64, 4]) reject paths without calls, on Kraken main

- `lc_reject_short_main`: `len(buf) < 4` → returns `ssz.ErrSize`.
- `lc_reject_offset_main`: `len(buf) ≥ 4` and the container offset (bytes
  0..3) ≠ 4 → returns `ssz.ErrInvalidVariableOffset`.
- `lc_reject_tail_main`: `5 ≤ len ≤ 7` (list bytes too short for an offset),
- `lc_reject_zero_main`: first element offset 0,
- `lc_reject_past_main`: first element offset `o` (≠ 0, `o mod 4 = 0`,
  `o ≤ 16`) past the end of `buf[4:]`:
  these three return the error from `fmt.errorf` (contract `FmtErrorfC`,
  rax ≠ 0).
Not proved here: the misaligned (`o mod 4 ≠ 0`) and too-many (`o / 4 > 4`)
paths (they box the value with `runtime.convT64` as in ListU64), the
per-element offset checks inside the loop, and the accept paths.
All return with rsp + 8 and rbp restored; the receiver is in `R` (not written).
Premises the Go caller provides: return address at rsp, saved-rbp slot, the
spill slot at rsp+16, the stack guard below rsp − 96 (the frame is 0xd8
bytes plus 0x60 below for callees: `lea -0x60(%rsp),%r12`), the error global.
-/

open Fk Fk.Code
variable [Host]

theorem toNat_add_neg96 (x : BitVec 64) (h : 96 ≤ x.toNat) : (x + -96).toNat = x.toNat - 96 := by
  rw [← BitVec.sub_eq_add_neg, BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; simpa using h)]; rfl

theorem lc_s16 (x : BitVec 64) : x - 8#64 - 216 + 240 = x + 16 := by bv_omega
theorem lc_pop (x : BitVec 64) : (216 : BitVec 64) + (x - 8#64 - 216) = x - 8 := by bv_omega

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem lc_reject_short_main (k : Nat) (hk : ListCUnmarshalSSZ.IsInfixAt Host.prog k)
    (hf : LabelsFresh ListCUnmarshalSSZ k)
    (s : MachineData) (ra guard e0 e1 : UInt64) (fp slot : List UInt8) (hfp : fp.length = 8) (hsl : slot.length = 8)
    (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (slot.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At (label "ssz.ErrSize").toBitVec)
      ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrSize" + 8).toBitVec) ⋆ R)
    (hguard : guard.toNat + 96 < s.regs.rsp.toNat) (hlen : s.regs.rcx.toNat < 4) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = e0 ∧ st.data.regs.rbx = e1
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp
        ∧ (R ⋆ fun _ => True) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hguard hlen ⊢
  have := rsp.toNat_lt_size; have := guard.toNat_lt_size; have := rcx.toNat_lt_size; simp only [UInt64.size] at *
  kat hk ListCUnmarshalSSZ 0
  kat hk ListCUnmarshalSSZ 1
  kat hk ListCUnmarshalSSZ 2
  kat hk ListCUnmarshalSSZ 3
  apply load_step _ _ _ _ (Int.toBytes 8 guard.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk ListCUnmarshalSSZ 4
  split
  case isTrue h =>
    exfalso
    rw [cmp_be_false _ _ _ _ (by rw [toNat_add_neg96 _ (by simp; omega)]; simp; omega)] at h
    exact absurd h (by simp)
  simp only [Effects.All]
  kat hk ListCUnmarshalSSZ 5
  apply store_step_at _ _ (rsp.toBitVec - 8) _ _ _ fp _ _ (by bv_omega) (by ecancel) (by exact hfp)
  intro m1 H1
  simp only [Width.bytes, Width.bits] at H1
  kunfold
  kat hk ListCUnmarshalSSZ 6
  kat hk ListCUnmarshalSSZ 7
  kat hk ListCUnmarshalSSZ 8
  apply store_step_at _ _ (rsp.toBitVec + 16) _ _ _ slot _ _ (lc_s16 _) (by ecancel) (by exact hsl)
  intro m2 H2
  simp only [Width.bytes, Width.bits] at H2
  kunfold
  kat hk ListCUnmarshalSSZ 9
  kat hk ListCUnmarshalSSZ 10
  split
  case isFalse h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned] at h; omega
  simp only [Effects.All]
  klabel hk hf ListCUnmarshalSSZ 220
  kat hk ListCUnmarshalSSZ 220
  kat hk ListCUnmarshalSSZ 221
  apply load_step _ _ _ _ (Int.toBytes 8 e0.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk ListCUnmarshalSSZ 222
  apply load_step _ _ _ _ (Int.toBytes 8 e1.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk ListCUnmarshalSSZ 223
  kat hk ListCUnmarshalSSZ 224
  rw [lc_pop]
  apply load_step _ _ _ _ (Int.toBytes 8 rbp.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk ListCUnmarshalSSZ 225
  rw [show rsp.toBitVec - 8 + 8#64 = rsp.toBitVec by bv_omega]
  apply load_step _ _ _ _ (Int.toBytes 8 ra.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  apply Eventually.done
  simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  refine ⟨trivial, ?_, ?_, ?_, ?_, ?_⟩
  · first | trivial | rfl | (apply UInt64.toBitVec_inj.mp; simp)
  · first | trivial | rfl | (apply UInt64.toBitVec_inj.mp; simp)
  · apply UInt64.toBitVec_inj.mp; simp
  · first | trivial | rfl
  · exact sep_true (by ecancel)

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem lc_reject_offset_main (k : Nat) (hk : ListCUnmarshalSSZ.IsInfixAt Host.prog k)
    (hf : LabelsFresh ListCUnmarshalSSZ k)
    (s : MachineData) (ra guard e0 e1 : UInt64) (fp slot : List UInt8) (hfp : fp.length = 8) (hsl : slot.length = 8)
    (o4 : List UInt8) (ho4 : o4.length = 4) (hoff : Int.ofBytes o4 ≠ 4)
    (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (slot.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq (o4.At s.regs.rbx.toBitVec)
      ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At (label "ssz.ErrInvalidVariableOffset").toBitVec)
      ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrInvalidVariableOffset" + 8).toBitVec) ⋆ R)
    (hguard : guard.toNat + 96 < s.regs.rsp.toNat) (hlen : 4 ≤ s.regs.rcx.toNat) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = e0 ∧ st.data.regs.rbx = e1
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp
        ∧ (R ⋆ fun _ => True) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hguard hlen ⊢
  have := rsp.toNat_lt_size; have := guard.toNat_lt_size; have := rcx.toNat_lt_size; simp only [UInt64.size] at *
  kat hk ListCUnmarshalSSZ 0
  kat hk ListCUnmarshalSSZ 1
  kat hk ListCUnmarshalSSZ 2
  kat hk ListCUnmarshalSSZ 3
  apply load_step _ _ _ _ (Int.toBytes 8 guard.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk ListCUnmarshalSSZ 4
  split
  case isTrue h =>
    exfalso
    rw [cmp_be_false _ _ _ _ (by rw [toNat_add_neg96 _ (by simp; omega)]; simp; omega)] at h
    exact absurd h (by simp)
  simp only [Effects.All]
  kat hk ListCUnmarshalSSZ 5
  apply store_step_at _ _ (rsp.toBitVec - 8) _ _ _ fp _ _ (by bv_omega) (by ecancel) (by exact hfp)
  intro m1 H1
  simp only [Width.bytes, Width.bits] at H1
  kunfold
  kat hk ListCUnmarshalSSZ 6
  kat hk ListCUnmarshalSSZ 7
  kat hk ListCUnmarshalSSZ 8
  apply store_step_at _ _ (rsp.toBitVec + 16) _ _ _ slot _ _ (lc_s16 _) (by ecancel) (by exact hsl)
  intro m2 H2
  simp only [Width.bytes, Width.bits] at H2
  kunfold
  kat hk ListCUnmarshalSSZ 9
  kat hk ListCUnmarshalSSZ 10
  split
  case isTrue h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned] at h; omega
  simp only [Effects.All]
  kat hk ListCUnmarshalSSZ 11
  apply load_step_at _ _ rbx.toBitVec _ _ o4 _ _ (by bv_omega) (by ecancel) (by exact ho4)
  kunfold
  kat hk ListCUnmarshalSSZ 12
  kat hk ListCUnmarshalSSZ 13
  kat hk ListCUnmarshalSSZ 14
  kat hk ListCUnmarshalSSZ 15
  split
  case isFalse h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
    exact hoff (lu_off4 o4 ho4 h)
  simp only [Effects.All]
  klabel hk hf ListCUnmarshalSSZ 214
  kat hk ListCUnmarshalSSZ 214
  kat hk ListCUnmarshalSSZ 215
  apply load_step _ _ _ _ (Int.toBytes 8 e0.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk ListCUnmarshalSSZ 216
  apply load_step _ _ _ _ (Int.toBytes 8 e1.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk ListCUnmarshalSSZ 217
  kat hk ListCUnmarshalSSZ 218
  rw [lc_pop]
  apply load_step _ _ _ _ (Int.toBytes 8 rbp.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk ListCUnmarshalSSZ 219
  rw [show rsp.toBitVec - 8 + 8#64 = rsp.toBitVec by bv_omega]
  apply load_step _ _ _ _ (Int.toBytes 8 ra.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  apply Eventually.done
  simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  refine ⟨trivial, ?_, ?_, ?_, ?_, ?_⟩
  · first | trivial | rfl | (apply UInt64.toBitVec_inj.mp; simp)
  · first | trivial | rfl | (apply UInt64.toBitVec_inj.mp; simp)
  · apply UInt64.toBitVec_inj.mp; simp
  · first | trivial | rfl
  · exact sep_true (by ecancel)

/-- `lea -4(%rdi),%rdx; neg; sar $63; and $4,%edx`: 4 when `4 < cap < 2^63`. -/
theorem lc_rdx4 (x : BitVec 64) (h : 4 < x.toNat) (h2 : x.toNat < 2 ^ 63) :
    BitVec.zeroExtend 64 (BitVec.extractLsb' 0 32 (BitVec.sshiftRight (-(x + -4)) 63) &&& BitVec.truncate 32 (4 : BitVec 64)) = 4 := by
  have hm : (-(x + -4)).msb = true := by
    rw [BitVec.msb_eq_decide, ← BitVec.sub_eq_add_neg, BitVec.toNat_neg,
      BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; simp; omega)]
    simp; omega
  generalize -(x + -4) = y at hm ⊢
  have hs : BitVec.sshiftRight y 63 = BitVec.allOnes 64 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sshiftRight, ite_cond_eq_true _ _ (by simpa using hm)]
    rw [BitVec.msb_eq_decide] at hm; simp at hm
    simp [BitVec.toNat_not, Nat.shiftRight_eq_div_pow]; omega
  rw [hs]; decide

/-- `cmp $3, a; jle` is not taken when `3 < a < 2^63`. -/
theorem jle3_false (a : BitVec 64) (af : Bool) (h : 3 < a.toNat) (h2 : a.toNat < 2 ^ 63) :
    CondCode.le.interp (StatusFlags.from_result (a - 3)
      { cf := BitVec.unsigned (a - 3) != a.unsigned - BitVec.unsigned (3 : BitVec 64), af := af,
        of := BitVec.toInt (a - 3) != a.toInt - BitVec.toInt (3 : BitVec 64) }) = false := by
  have ta : a.toInt = a.toNat := BitVec.toInt_eq_toNat_of_lt (by omega)
  have t3 : BitVec.toInt (3 : BitVec 64) = 3 := by decide
  have hs : (a - 3).toInt = (a.toNat : Int) - 3 := by
    rw [BitVec.toInt_sub, ta, t3]; apply Int.bmod_eq_of_le <;> omega
  have hz : a - 3 ≠ 0#64 := by
    intro h0; have := congrArg BitVec.toNat h0; simp [BitVec.toNat_sub] at this; omega
  have hm : (a - 3).msb = false := by
    rw [BitVec.msb_eq_decide]; simp [BitVec.toNat_sub]; omega
  simp [CondCode.interp, StatusFlags.from_result, ta, t3, hs]
  refine ⟨?_, by simpa using hz⟩
  rw [show (a - 3#64) = a - 3 from rfl, hm, Int.bmod_eq_of_le (by omega) (by omega)]; simp

theorem zx_o (o : Nat) (h : o < 2 ^ 32) : BitVec.zeroExtend 64 (BitVec.ofInt 32 (o : Int)) = BitVec.ofNat 64 o := by
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_ofInt]; omega

theorem and3_o (o : Nat) (h : o < 2 ^ 32) : (BitVec.ofNat 64 o &&& 3).toNat = o % 4 := by
  rw [BitVec.toNat_and, show (3 : BitVec 64).toNat = 2 ^ 2 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  simp

theorem and3_zero (o : Nat) (h : o < 2 ^ 32) (h4 : o % 4 = 0) : BitVec.ofNat 64 o &&& 3 = 0 := by
  apply BitVec.eq_of_toNat_eq; rw [and3_o o h, h4]; rfl

theorem shr2_o (o : Nat) (h : o < 2 ^ 32) : (BitVec.ofNat 64 o).ushiftRight 2 = BitVec.ofNat 64 (o / 4) := by
  apply BitVec.eq_of_toNat_eq
  rw [show (BitVec.ofNat 64 o).ushiftRight 2 = BitVec.ofNat 64 o >>> 2 from rfl, BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow]
  simp; omega

theorem ja4_false (x : Nat) (h : x ≤ 4) (af of' : Bool) :
    CondCode.a.interp (StatusFlags.from_result (BitVec.ofNat 64 x - 4)
      { cf := BitVec.unsigned (BitVec.ofNat 64 x - 4) != (BitVec.ofNat 64 x).unsigned - BitVec.unsigned (4 : BitVec 64),
        af := af, of := of' }) = false := by
  rcases (by omega : x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4) with rfl | rfl | rfl | rfl | rfl <;>
    simp (config := {decide := true}) [CondCode.interp, StatusFlags.from_result, BitVec.unsigned]

theorem jae_false (a b : BitVec 64) (af of' : Bool) (h : a.toNat < b.toNat) :
    CondCode.ae.interp (StatusFlags.from_result (a - b)
      { cf := BitVec.unsigned (a - b) != a.unsigned - b.unsigned, af := af, of := of' }) = false := by
  have hb : (a - b).toNat = 2 ^ 64 - b.toNat + a.toNat := by
    rw [BitVec.toNat_sub]; have := b.isLt; omega
  simp only [CondCode.interp, StatusFlags.from_result, BitVec.unsigned, hb]
  simp; omega

theorem jle3_true (a : BitVec 64) (h : a.toNat ≤ 3) (af : Bool) :
    CondCode.le.interp (StatusFlags.from_result (a - 3)
      { cf := BitVec.unsigned (a - 3) != a.unsigned - BitVec.unsigned (3 : BitVec 64), af := af,
        of := BitVec.toInt (a - 3) != a.toInt - BitVec.toInt (3 : BitVec 64) }) = true := by
  have : a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 := by
    rcases (by omega : a.toNat = 0 ∨ a.toNat = 1 ∨ a.toNat = 2 ∨ a.toNat = 3) with h | h | h | h
    · exact .inl (BitVec.eq_of_toNat_eq h)
    · exact .inr (.inl (BitVec.eq_of_toNat_eq h))
    · exact .inr (.inr (.inl (BitVec.eq_of_toNat_eq h)))
    · exact .inr (.inr (.inr (BitVec.eq_of_toNat_eq h)))
  rcases this with rfl | rfl | rfl | rfl <;>
    simp (config := {decide := true}) [CondCode.interp, StatusFlags.from_result, BitVec.unsigned]

theorem lc_call (x : BitVec 64) : x - 8#64 - 216 - 8#64 = x - 232 := by bv_omega
theorem lc_pop2 (x : BitVec 64) : (216 : BitVec 64) + ({ toBitVec := x - 232 } + 8 : UInt64).toBitVec = x - 8 := by
  simp only [UInt64.toBitVec_add, UInt64.toBitVec_ofNat]; bv_omega

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- First element offset 0 (bytes 4..7 of `buf` read as 0), `len ≥ 8`: returns
the error from `fmt.errorf` (rax ≠ 0). -/
theorem lc_reject_zero_main (k : Nat) (hk : ListCUnmarshalSSZ.IsInfixAt Host.prog k)
    (hf : LabelsFresh ListCUnmarshalSSZ k)
    (s : MachineData) (ra guard : UInt64) (fp slot rslot : List UInt8) (hfp : fp.length = 8) (hsl : slot.length = 8)
    (hrs : rslot.length = 8) (o4 : List UInt8) (ho4 : o4.length = 4) (hoff : Int.ofBytes o4 = 0)
    (R : DataMem → Prop) (S : Nat) (scratch : List UInt8) (hsc : scratch.length = S)
    (Heap : Nat → DataMem → Prop) (avail : Nat)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (slot.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 232)) ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - 232 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16)) ⋆ Heap avail
      ⋆ Eq ([4, 0, 0, 0].At s.regs.rbx.toBitVec) ⋆ Eq (o4.At (s.regs.rbx.toBitVec + 4)) ⋆ R)
    (hguard : guard.toNat + 96 < s.regs.rsp.toNat) (hsp : 232 ≤ s.regs.rsp.toNat)
    (hlen : 8 ≤ s.regs.rcx.toNat) (hcap : s.regs.rcx.toNat ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63)
    (hfe : FmtErrorfC Heap S) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax ≠ 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp
        ∧ (R ⋆ fun _ => True) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hguard hsp hlen hcap hcap63 ⊢
  have := rsp.toNat_lt_size; have := guard.toNat_lt_size; have := rcx.toNat_lt_size; have := rdi.toNat_lt_size
  simp only [UInt64.size] at *
  kat hk ListCUnmarshalSSZ 0
  kat hk ListCUnmarshalSSZ 1
  kat hk ListCUnmarshalSSZ 2
  kat hk ListCUnmarshalSSZ 3
  apply load_step _ _ _ _ (Int.toBytes 8 guard.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk ListCUnmarshalSSZ 4
  split
  case isTrue h =>
    exfalso
    rw [cmp_be_false _ _ _ _ (by rw [toNat_add_neg96 _ (by simp; omega)]; simp; omega)] at h
    exact absurd h (by simp)
  simp only [Effects.All]
  kat hk ListCUnmarshalSSZ 5
  apply store_step_at _ _ (rsp.toBitVec - 8) _ _ _ fp _ _ (by bv_omega) (by ecancel) (by exact hfp)
  intro m1 H1
  simp only [Width.bytes, Width.bits] at H1
  kunfold
  kat hk ListCUnmarshalSSZ 6
  kat hk ListCUnmarshalSSZ 7
  kat hk ListCUnmarshalSSZ 8
  apply store_step_at _ _ (rsp.toBitVec + 16) _ _ _ slot _ _ (lc_s16 _) (by ecancel) (by exact hsl)
  intro m2 H2
  simp only [Width.bytes, Width.bits] at H2
  kunfold
  kat hk ListCUnmarshalSSZ 9
  kat hk ListCUnmarshalSSZ 10
  split
  case isTrue h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned] at h; omega
  simp only [Effects.All]
  kat hk ListCUnmarshalSSZ 11
  apply load_step_at _ _ rbx.toBitVec _ _ [4, 0, 0, 0] _ _ (by bv_omega) (by ecancel) (by simp)
  simp only [show Int.ofBytes [4, 0, 0, 0] = 4 by simp [Int.ofBytes]]
  kunfold
  kat hk ListCUnmarshalSSZ 12
  kat hk ListCUnmarshalSSZ 13
  kat hk ListCUnmarshalSSZ 14
  kat hk ListCUnmarshalSSZ 15
  split
  case isTrue h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
  simp only [Effects.All]
  kat hk ListCUnmarshalSSZ 16
  kat hk ListCUnmarshalSSZ 17
  kat hk ListCUnmarshalSSZ 18
  kat hk ListCUnmarshalSSZ 19
  kshl64 63
  kat hk ListCUnmarshalSSZ 20
  intro _
  rw [lc_rdx4 _ (by simp; omega) (by simp; omega)]
  kat hk ListCUnmarshalSSZ 21
  kat hk ListCUnmarshalSSZ 22
  kat hk ListCUnmarshalSSZ 23
  kat hk ListCUnmarshalSSZ 24
  kat hk ListCUnmarshalSSZ 25
  kat hk ListCUnmarshalSSZ 26
  kat hk ListCUnmarshalSSZ 27
  rw [jle3_false _ _ (by rw [BitVec.add_comm, ← BitVec.sub_eq_add_neg, BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; simp; omega)]; simp; omega)
    (by rw [BitVec.add_comm, ← BitVec.sub_eq_add_neg, BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; simp; omega)]; simp; omega)]
  simp only [Bool.false_eq_true, ↓reduceIte, Effects.All]
  kat hk ListCUnmarshalSSZ 28
  apply load_step_at _ _ (rbx.toBitVec + 4) _ _ o4 _ _ (by bv_omega) (by ecancel) (by exact ho4)
  rw [hoff]
  kunfold
  kat hk ListCUnmarshalSSZ 29
  kat hk ListCUnmarshalSSZ 30
  kat hk ListCUnmarshalSSZ 31
  intro _
  kat hk ListCUnmarshalSSZ 32
  split
  case isFalse h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
  simp only [Effects.All]
  klabel hk hf ListCUnmarshalSSZ 157
  kat hk ListCUnmarshalSSZ 157
  kat hk ListCUnmarshalSSZ 158
  kat hk ListCUnmarshalSSZ 159
  kat hk ListCUnmarshalSSZ 160
  intro _
  kat hk ListCUnmarshalSSZ 161
  intro _
  kat hk ListCUnmarshalSSZ 162
  kat hk ListCUnmarshalSSZ 163
  apply store_step_at _ _ (rsp.toBitVec - 232) _ _ _ rslot _ _ (lc_call _) (by ecancel) (by exact hrs)
  intro m5 H5
  simp only [Width.bytes, Width.bits] at H5
  kunfold
  rw [lc_call] at *
  refine eventually_trans _ _ _ _ (hfe _ (Host.addrOf (k + 163 + 1)) avail scratch _ hsc (by ecancel)) ?_
  rintro ⟨d2, pc2⟩ ⟨hpc2, hrsp2, hrax2, stk2, av2, hstk2, Hm2⟩
  dsimp only at hpc2 hrsp2 hrax2 Hm2
  subst hpc2
  obtain ⟨⟨rax2, rbx2, rcx2, rdx2, rsi2, rdi2, rsp2, rbp2, r82, r92, r102, r112, r122, r132, r142, r152⟩,
    zmms2, flags2, mem2⟩ := d2
  simp only at hrsp2 hrax2 Hm2
  subst hrsp2
  kat hk ListCUnmarshalSSZ 164
  intro _
  kat hk ListCUnmarshalSSZ 165
  split
  case isFalse h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
    exact hrax2 (UInt64.toBitVec_inj.mp (by simpa using h))
  simp only [Effects.All]
  klabel hk hf ListCUnmarshalSSZ 174
  kat hk ListCUnmarshalSSZ 174
  kat hk ListCUnmarshalSSZ 175
  kat hk ListCUnmarshalSSZ 176
  rw [lc_pop2]
  apply load_step _ _ _ _ (Int.toBytes 8 rbp.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk ListCUnmarshalSSZ 177
  rw [show rsp.toBitVec - 8 + 8#64 = rsp.toBitVec by bv_omega]
  apply load_step _ _ _ _ (Int.toBytes 8 ra.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  apply Eventually.done
  simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  refine ⟨trivial, hrax2, ?_, ?_, ?_⟩
  · apply UInt64.toBitVec_inj.mp; simp
  · first | trivial | rfl
  · exact sep_true (by ecancel)

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- First element offset `o` (bytes 4..7) non-zero, a multiple of 4, at most
16 (4 elements), but past the end of `buf[4:]` (`len − 4 < o`): returns the
error from `fmt.errorf` (rax ≠ 0). -/
theorem lc_reject_past_main (k : Nat) (hk : ListCUnmarshalSSZ.IsInfixAt Host.prog k)
    (hf : LabelsFresh ListCUnmarshalSSZ k)
    (s : MachineData) (ra guard : UInt64) (fp slot rslot : List UInt8) (hfp : fp.length = 8) (hsl : slot.length = 8)
    (hrs : rslot.length = 8) (o4 : List UInt8) (ho4 : o4.length = 4) (o : Nat) (hoff : Int.ofBytes o4 = o) (ho0 : o ≠ 0) (ho4' : o % 4 = 0) (ho16 : o ≤ 16)
    (R : DataMem → Prop) (S : Nat) (scratch : List UInt8) (hsc : scratch.length = S)
    (Heap : Nat → DataMem → Prop) (avail : Nat)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (slot.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 232)) ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - 232 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16)) ⋆ Heap avail
      ⋆ Eq ([4, 0, 0, 0].At s.regs.rbx.toBitVec) ⋆ Eq (o4.At (s.regs.rbx.toBitVec + 4)) ⋆ R)
    (hguard : guard.toNat + 96 < s.regs.rsp.toNat) (hsp : 232 ≤ s.regs.rsp.toNat)
    (hlen : 8 ≤ s.regs.rcx.toNat) (hpast : s.regs.rcx.toNat - 4 < o) (hcap : s.regs.rcx.toNat ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63)
    (hfe : FmtErrorfC Heap S) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax ≠ 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp
        ∧ (R ⋆ fun _ => True) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hguard hsp hlen hcap hcap63 ⊢
  have := rsp.toNat_lt_size; have := guard.toNat_lt_size; have := rcx.toNat_lt_size; have := rdi.toNat_lt_size
  simp only [UInt64.size] at *
  kat hk ListCUnmarshalSSZ 0
  kat hk ListCUnmarshalSSZ 1
  kat hk ListCUnmarshalSSZ 2
  kat hk ListCUnmarshalSSZ 3
  apply load_step _ _ _ _ (Int.toBytes 8 guard.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk ListCUnmarshalSSZ 4
  split
  case isTrue h =>
    exfalso
    rw [cmp_be_false _ _ _ _ (by rw [toNat_add_neg96 _ (by simp; omega)]; simp; omega)] at h
    exact absurd h (by simp)
  simp only [Effects.All]
  kat hk ListCUnmarshalSSZ 5
  apply store_step_at _ _ (rsp.toBitVec - 8) _ _ _ fp _ _ (by bv_omega) (by ecancel) (by exact hfp)
  intro m1 H1
  simp only [Width.bytes, Width.bits] at H1
  kunfold
  kat hk ListCUnmarshalSSZ 6
  kat hk ListCUnmarshalSSZ 7
  kat hk ListCUnmarshalSSZ 8
  apply store_step_at _ _ (rsp.toBitVec + 16) _ _ _ slot _ _ (lc_s16 _) (by ecancel) (by exact hsl)
  intro m2 H2
  simp only [Width.bytes, Width.bits] at H2
  kunfold
  kat hk ListCUnmarshalSSZ 9
  kat hk ListCUnmarshalSSZ 10
  split
  case isTrue h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned] at h; omega
  simp only [Effects.All]
  kat hk ListCUnmarshalSSZ 11
  apply load_step_at _ _ rbx.toBitVec _ _ [4, 0, 0, 0] _ _ (by bv_omega) (by ecancel) (by simp)
  simp only [show Int.ofBytes [4, 0, 0, 0] = 4 by simp [Int.ofBytes]]
  kunfold
  kat hk ListCUnmarshalSSZ 12
  kat hk ListCUnmarshalSSZ 13
  kat hk ListCUnmarshalSSZ 14
  kat hk ListCUnmarshalSSZ 15
  split
  case isTrue h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
  simp only [Effects.All]
  kat hk ListCUnmarshalSSZ 16
  kat hk ListCUnmarshalSSZ 17
  kat hk ListCUnmarshalSSZ 18
  kat hk ListCUnmarshalSSZ 19
  kshl64 63
  kat hk ListCUnmarshalSSZ 20
  intro _
  rw [lc_rdx4 _ (by simp; omega) (by simp; omega)]
  kat hk ListCUnmarshalSSZ 21
  kat hk ListCUnmarshalSSZ 22
  kat hk ListCUnmarshalSSZ 23
  kat hk ListCUnmarshalSSZ 24
  kat hk ListCUnmarshalSSZ 25
  kat hk ListCUnmarshalSSZ 26
  kat hk ListCUnmarshalSSZ 27
  rw [jle3_false _ _ (by rw [BitVec.add_comm, ← BitVec.sub_eq_add_neg, BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; simp; omega)]; simp; omega)
    (by rw [BitVec.add_comm, ← BitVec.sub_eq_add_neg, BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; simp; omega)]; simp; omega)]
  simp only [Bool.false_eq_true, ↓reduceIte, Effects.All]
  kat hk ListCUnmarshalSSZ 28
  apply load_step_at _ _ (rbx.toBitVec + 4) _ _ o4 _ _ (by bv_omega) (by ecancel) (by exact ho4)
  rw [hoff]
  kunfold
  kat hk ListCUnmarshalSSZ 29
  kat hk ListCUnmarshalSSZ 30
  kat hk ListCUnmarshalSSZ 31
  intro _
  have ho32 : o < 2 ^ 32 := by
    have := Int.ofBytes_lt o4; rw [ho4] at this; omega
  rw [zx_o o ho32]
  kat hk ListCUnmarshalSSZ 32
  split
  case isTrue h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
    have := congrArg BitVec.toNat h; simp at this; omega
  simp only [Effects.All]
  kat hk ListCUnmarshalSSZ 33
  kat hk ListCUnmarshalSSZ 34
  intro _
  rw [and3_zero o ho32 ho4']
  kat hk ListCUnmarshalSSZ 35
  split
  case isTrue h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
  simp only [Effects.All]
  kat hk ListCUnmarshalSSZ 36
  kat hk ListCUnmarshalSSZ 37
  kshl64 2
  rw [shr2_o o ho32]
  kat hk ListCUnmarshalSSZ 38
  kat hk ListCUnmarshalSSZ 39
  rw [ja4_false _ (by omega)]
  simp only [Bool.false_eq_true, ↓reduceIte, Effects.All]
  kat hk ListCUnmarshalSSZ 40
  kat hk ListCUnmarshalSSZ 41
  kat hk ListCUnmarshalSSZ 42
  rw [jae_false _ _ _ _ (by
    rw [BitVec.add_comm, ← BitVec.sub_eq_add_neg, BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; simp; omega)]
    simp; omega)]
  simp only [Bool.false_eq_true, ↓reduceIte, Effects.All]
  kat hk ListCUnmarshalSSZ 43
  kat hk ListCUnmarshalSSZ 44
  kat hk ListCUnmarshalSSZ 45
  intro _
  kat hk ListCUnmarshalSSZ 46
  intro _
  kat hk ListCUnmarshalSSZ 47
  kat hk ListCUnmarshalSSZ 48
  apply store_step_at _ _ (rsp.toBitVec - 232) _ _ _ rslot _ _ (lc_call _) (by ecancel) (by exact hrs)
  intro m5 H5
  simp only [Width.bytes, Width.bits] at H5
  kunfold
  rw [lc_call] at *
  refine eventually_trans _ _ _ _ (hfe _ (Host.addrOf (k + 48 + 1)) avail scratch _ hsc (by ecancel)) ?_
  rintro ⟨d2, pc2⟩ ⟨hpc2, hrsp2, hrax2, stk2, av2, hstk2, Hm2⟩
  dsimp only at hpc2 hrsp2 hrax2 Hm2
  subst hpc2
  obtain ⟨⟨rax2, rbx2, rcx2, rdx2, rsi2, rdi2, rsp2, rbp2, r82, r92, r102, r112, r122, r132, r142, r152⟩,
    zmms2, flags2, mem2⟩ := d2
  simp only at hrsp2 hrax2 Hm2
  subst hrsp2
  kat hk ListCUnmarshalSSZ 49
  kat hk ListCUnmarshalSSZ 50
  intro _
  kat hk ListCUnmarshalSSZ 51
  split
  case isFalse h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
    exact hrax2 (UInt64.toBitVec_inj.mp (by simpa using h))
  simp only [Effects.All]
  klabel hk hf ListCUnmarshalSSZ 60
  kat hk ListCUnmarshalSSZ 60
  kat hk ListCUnmarshalSSZ 61
  kat hk ListCUnmarshalSSZ 62
  rw [lc_pop2]
  apply load_step _ _ _ _ (Int.toBytes 8 rbp.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk ListCUnmarshalSSZ 63
  rw [show rsp.toBitVec - 8 + 8#64 = rsp.toBitVec by bv_omega]
  apply load_step _ _ _ _ (Int.toBytes 8 ra.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  apply Eventually.done
  simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  refine ⟨trivial, hrax2, ?_, ?_, ?_⟩
  · apply UInt64.toBitVec_inj.mp; simp
  · first | trivial | rfl
  · exact sep_true (by ecancel)

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- `5 ≤ len(buf) ≤ 7`: the list bytes `buf[4:]` are too short for an offset;
returns the error from `fmt.errorf` (rax ≠ 0). -/
theorem lc_reject_tail_main (k : Nat) (hk : ListCUnmarshalSSZ.IsInfixAt Host.prog k)
    (hf : LabelsFresh ListCUnmarshalSSZ k)
    (s : MachineData) (ra guard : UInt64) (fp slot rslot : List UInt8) (hfp : fp.length = 8) (hsl : slot.length = 8)
    (hrs : rslot.length = 8)
    (R : DataMem → Prop) (S : Nat) (scratch : List UInt8) (hsc : scratch.length = S)
    (Heap : Nat → DataMem → Prop) (avail : Nat)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (slot.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 232)) ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - 232 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16)) ⋆ Heap avail
      ⋆ Eq ([4, 0, 0, 0].At s.regs.rbx.toBitVec) ⋆ R)
    (hguard : guard.toNat + 96 < s.regs.rsp.toNat) (hsp : 232 ≤ s.regs.rsp.toNat)
    (hlen5 : 5 ≤ s.regs.rcx.toNat) (hlen : s.regs.rcx.toNat ≤ 7) (hcap : s.regs.rcx.toNat ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63)
    (hfe : FmtErrorfC Heap S) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax ≠ 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp
        ∧ (R ⋆ fun _ => True) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hguard hsp hlen hcap hcap63 ⊢
  have := rsp.toNat_lt_size; have := guard.toNat_lt_size; have := rcx.toNat_lt_size; have := rdi.toNat_lt_size
  simp only [UInt64.size] at *
  kat hk ListCUnmarshalSSZ 0
  kat hk ListCUnmarshalSSZ 1
  kat hk ListCUnmarshalSSZ 2
  kat hk ListCUnmarshalSSZ 3
  apply load_step _ _ _ _ (Int.toBytes 8 guard.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk ListCUnmarshalSSZ 4
  split
  case isTrue h =>
    exfalso
    rw [cmp_be_false _ _ _ _ (by rw [toNat_add_neg96 _ (by simp; omega)]; simp; omega)] at h
    exact absurd h (by simp)
  simp only [Effects.All]
  kat hk ListCUnmarshalSSZ 5
  apply store_step_at _ _ (rsp.toBitVec - 8) _ _ _ fp _ _ (by bv_omega) (by ecancel) (by exact hfp)
  intro m1 H1
  simp only [Width.bytes, Width.bits] at H1
  kunfold
  kat hk ListCUnmarshalSSZ 6
  kat hk ListCUnmarshalSSZ 7
  kat hk ListCUnmarshalSSZ 8
  apply store_step_at _ _ (rsp.toBitVec + 16) _ _ _ slot _ _ (lc_s16 _) (by ecancel) (by exact hsl)
  intro m2 H2
  simp only [Width.bytes, Width.bits] at H2
  kunfold
  kat hk ListCUnmarshalSSZ 9
  kat hk ListCUnmarshalSSZ 10
  split
  case isTrue h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned] at h; omega
  simp only [Effects.All]
  kat hk ListCUnmarshalSSZ 11
  apply load_step_at _ _ rbx.toBitVec _ _ [4, 0, 0, 0] _ _ (by bv_omega) (by ecancel) (by simp)
  simp only [show Int.ofBytes [4, 0, 0, 0] = 4 by simp [Int.ofBytes]]
  kunfold
  kat hk ListCUnmarshalSSZ 12
  kat hk ListCUnmarshalSSZ 13
  kat hk ListCUnmarshalSSZ 14
  kat hk ListCUnmarshalSSZ 15
  split
  case isTrue h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
  simp only [Effects.All]
  kat hk ListCUnmarshalSSZ 16
  kat hk ListCUnmarshalSSZ 17
  kat hk ListCUnmarshalSSZ 18
  kat hk ListCUnmarshalSSZ 19
  kshl64 63
  kat hk ListCUnmarshalSSZ 20
  intro _
  kat hk ListCUnmarshalSSZ 21
  kat hk ListCUnmarshalSSZ 22
  kat hk ListCUnmarshalSSZ 23
  kat hk ListCUnmarshalSSZ 24
  kat hk ListCUnmarshalSSZ 25
  kat hk ListCUnmarshalSSZ 26
  kat hk ListCUnmarshalSSZ 27
  rw [jle3_true _ (by rw [BitVec.add_comm, ← BitVec.sub_eq_add_neg, BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; simp; omega)]; simp; omega)]
  simp only [↓reduceIte, Effects.All]
  klabel hk hf ListCUnmarshalSSZ 178
  kat hk ListCUnmarshalSSZ 178
  kat hk ListCUnmarshalSSZ 179
  kat hk ListCUnmarshalSSZ 180
  split
  case isFalse h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
    have := congrArg BitVec.toNat h
    simp [BitVec.toNat_add] at this; omega
  simp only [Effects.All]
  klabel hk hf ListCUnmarshalSSZ 193
  kat hk ListCUnmarshalSSZ 193
  kat hk ListCUnmarshalSSZ 194
  kat hk ListCUnmarshalSSZ 195
  kat hk ListCUnmarshalSSZ 196
  intro _
  kat hk ListCUnmarshalSSZ 197
  intro _
  kat hk ListCUnmarshalSSZ 198
  kat hk ListCUnmarshalSSZ 199
  apply store_step_at _ _ (rsp.toBitVec - 232) _ _ _ rslot _ _ (lc_call _) (by ecancel) (by exact hrs)
  intro m5 H5
  simp only [Width.bytes, Width.bits] at H5
  kunfold
  rw [lc_call] at *
  refine eventually_trans _ _ _ _ (hfe _ (Host.addrOf (k + 199 + 1)) avail scratch _ hsc (by ecancel)) ?_
  rintro ⟨d2, pc2⟩ ⟨hpc2, hrsp2, hrax2, stk2, av2, hstk2, Hm2⟩
  dsimp only at hpc2 hrsp2 hrax2 Hm2
  subst hpc2
  obtain ⟨⟨rax2, rbx2, rcx2, rdx2, rsi2, rdi2, rsp2, rbp2, r82, r92, r102, r112, r122, r132, r142, r152⟩,
    zmms2, flags2, mem2⟩ := d2
  simp only at hrsp2 hrax2 Hm2
  subst hrsp2
  kat hk ListCUnmarshalSSZ 200
  intro _
  kat hk ListCUnmarshalSSZ 201
  split
  case isFalse h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
    exact hrax2 (UInt64.toBitVec_inj.mp (by simpa using h))
  simp only [Effects.All]
  klabel hk hf ListCUnmarshalSSZ 210
  kat hk ListCUnmarshalSSZ 210
  kat hk ListCUnmarshalSSZ 211
  kat hk ListCUnmarshalSSZ 212
  rw [lc_pop2]
  apply load_step _ _ _ _ (Int.toBytes 8 rbp.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk ListCUnmarshalSSZ 213
  rw [show rsp.toBitVec - 8 + 8#64 = rsp.toBitVec by bv_omega]
  apply load_step _ _ _ _ (Int.toBytes 8 ra.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  apply Eventually.done
  simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  refine ⟨trivial, hrax2, ?_, ?_, ?_⟩
  · apply UInt64.toBitVec_inj.mp; simp
  · first | trivial | rfl
  · exact sep_true (by ecancel)
