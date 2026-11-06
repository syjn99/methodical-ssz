import Fk.LuReject
import Fk.NeAccept

/-!
# Nested.UnmarshalSSZ reject paths without calls, on Kraken main

- `ne_reject_short_main`: `len(buf) < 28` → returns `ssz.ErrSize`.
- `ne_reject_offset_main`: `len(buf) ≥ 28` and the offset at bytes 24..27
  ≠ 28 → returns `ssz.ErrInvalidVariableOffset`.
-/

open Fk Fk.Code
variable [Host]

theorem ne_off28 (o4 : List UInt8) (ho4 : o4.length = 4)
    (h : BitVec.zeroExtend 64 (BitVec.ofInt 32 (Int.ofBytes o4)) - 28 = 0#64) : Int.ofBytes o4 = 28 := by
  have h0 := Int.ofBytes_ge_zero o4
  have h1 := Int.ofBytes_lt o4
  rw [ho4] at h1
  have hx : BitVec.zeroExtend 64 (BitVec.ofInt 32 (Int.ofBytes o4)) = 28 := by
    rw [← BitVec.sub_add_cancel (BitVec.zeroExtend 64 (BitVec.ofInt 32 (Int.ofBytes o4))) 28, h]; rfl
  have := congrArg BitVec.toNat hx
  simp [BitVec.toNat_ofInt] at this
  omega

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem ne_reject_short_main (k : Nat) (hk : NestedUnmarshalSSZ.IsInfixAt Host.prog k)
    (hf : LabelsFresh NestedUnmarshalSSZ k)
    (s : MachineData) (ra guard e0 e1 : UInt64) (fp slot : List UInt8) (hfp : fp.length = 8) (hsl : slot.length = 8)
    (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (slot.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At (label "ssz.ErrSize").toBitVec)
      ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrSize" + 8).toBitVec) ⋆ R)
    (hguard : guard.toNat + 112 < s.regs.rsp.toNat) (hlen : s.regs.rcx.toNat < 28) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = e0 ∧ st.data.regs.rbx = e1
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp
        ∧ (R ⋆ fun _ => True) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hguard hlen ⊢
  have := rsp.toNat_lt_size; have := guard.toNat_lt_size; have := rcx.toNat_lt_size; simp only [UInt64.size] at *
  kat hk NestedUnmarshalSSZ 0
  kat hk NestedUnmarshalSSZ 1
  kat hk NestedUnmarshalSSZ 2
  apply load_step _ _ _ _ (Int.toBytes 8 guard.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk NestedUnmarshalSSZ 3
  split
  · rename_i h; exfalso
    simp [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, CondCode.interp, StatusFlags.from_result, BitVec.unsigned] at h
    rcases h with h | h
    · apply h; omega
    · have := congrArg BitVec.toNat h; simp [BitVec.toNat_sub] at this; omega
  simp only [Effects.All]
  kat hk NestedUnmarshalSSZ 4
  apply store_step_at _ _ (rsp.toBitVec - 8) _ _ _ fp _ _ (by bv_omega) (by ecancel) (by exact hfp)
  intro m1 H1
  simp only [Width.bytes, Width.bits] at H1
  kunfold
  kat hk NestedUnmarshalSSZ 5
  kat hk NestedUnmarshalSSZ 6
  kat hk NestedUnmarshalSSZ 7
  apply store_step_at _ _ (rsp.toBitVec + 16) _ _ _ slot _ _ (ne_s120 _) (by ecancel) (by exact hsl)
  intro m2 H2
  simp only [Width.bytes, Width.bits] at H2
  kunfold
  kat hk NestedUnmarshalSSZ 8
  kat hk NestedUnmarshalSSZ 9
  kat hk NestedUnmarshalSSZ 10
  split
  case isFalse h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned] at h; omega
  simp only [Effects.All]
  klabel hk hf NestedUnmarshalSSZ 139
  kat hk NestedUnmarshalSSZ 139
  kat hk NestedUnmarshalSSZ 140
  apply load_step _ _ _ _ (Int.toBytes 8 e0.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk NestedUnmarshalSSZ 141
  apply load_step _ _ _ _ (Int.toBytes 8 e1.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk NestedUnmarshalSSZ 142
  kat hk NestedUnmarshalSSZ 143
  rw [show (88 : BitVec 64) + (rsp.toBitVec - 8#64 - 88) = rsp.toBitVec - 8 by bv_omega]
  apply load_step _ _ _ _ (Int.toBytes 8 rbp.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk NestedUnmarshalSSZ 144
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
theorem ne_reject_offset_main (k : Nat) (hk : NestedUnmarshalSSZ.IsInfixAt Host.prog k)
    (hf : LabelsFresh NestedUnmarshalSSZ k)
    (s : MachineData) (ra guard e0 e1 : UInt64) (fp slot : List UInt8) (hfp : fp.length = 8) (hsl : slot.length = 8)
    (o4 : List UInt8) (ho4 : o4.length = 4) (hoff : Int.ofBytes o4 ≠ 28)
    (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (slot.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq (o4.At (s.regs.rbx.toBitVec + 24))
      ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At (label "ssz.ErrInvalidVariableOffset").toBitVec)
      ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrInvalidVariableOffset" + 8).toBitVec) ⋆ R)
    (hguard : guard.toNat + 112 < s.regs.rsp.toNat) (hlen : 28 ≤ s.regs.rcx.toNat) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = e0 ∧ st.data.regs.rbx = e1
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp
        ∧ (R ⋆ fun _ => True) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hguard hlen ⊢
  have := rsp.toNat_lt_size; have := guard.toNat_lt_size; have := rcx.toNat_lt_size; simp only [UInt64.size] at *
  kat hk NestedUnmarshalSSZ 0
  kat hk NestedUnmarshalSSZ 1
  kat hk NestedUnmarshalSSZ 2
  apply load_step _ _ _ _ (Int.toBytes 8 guard.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk NestedUnmarshalSSZ 3
  split
  · rename_i h; exfalso
    simp [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, CondCode.interp, StatusFlags.from_result, BitVec.unsigned] at h
    rcases h with h | h
    · apply h; omega
    · have := congrArg BitVec.toNat h; simp [BitVec.toNat_sub] at this; omega
  simp only [Effects.All]
  kat hk NestedUnmarshalSSZ 4
  apply store_step_at _ _ (rsp.toBitVec - 8) _ _ _ fp _ _ (by bv_omega) (by ecancel) (by exact hfp)
  intro m1 H1
  simp only [Width.bytes, Width.bits] at H1
  kunfold
  kat hk NestedUnmarshalSSZ 5
  kat hk NestedUnmarshalSSZ 6
  kat hk NestedUnmarshalSSZ 7
  apply store_step_at _ _ (rsp.toBitVec + 16) _ _ _ slot _ _ (ne_s120 _) (by ecancel) (by exact hsl)
  intro m2 H2
  simp only [Width.bytes, Width.bits] at H2
  kunfold
  kat hk NestedUnmarshalSSZ 8
  kat hk NestedUnmarshalSSZ 9
  kat hk NestedUnmarshalSSZ 10
  split
  case isTrue h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned] at h; omega
  simp only [Effects.All]
  kat hk NestedUnmarshalSSZ 11
  apply load_step_at _ _ (rbx.toBitVec + 24) _ _ o4 _ _ (by bv_omega) (by ecancel) (by exact ho4)
  kunfold
  kat hk NestedUnmarshalSSZ 12
  kat hk NestedUnmarshalSSZ 13
  kat hk NestedUnmarshalSSZ 14
  kat hk NestedUnmarshalSSZ 15
  split
  case isFalse h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
    exact hoff (ne_off28 o4 ho4 h)
  simp only [Effects.All]
  klabel hk hf NestedUnmarshalSSZ 133
  kat hk NestedUnmarshalSSZ 133
  kat hk NestedUnmarshalSSZ 134
  apply load_step _ _ _ _ (Int.toBytes 8 e0.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk NestedUnmarshalSSZ 135
  apply load_step _ _ _ _ (Int.toBytes 8 e1.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk NestedUnmarshalSSZ 136
  kat hk NestedUnmarshalSSZ 137
  rw [show (88 : BitVec 64) + (rsp.toBitVec - 8#64 - 88) = rsp.toBitVec - 8 by bv_omega]
  apply load_step _ _ _ _ (Int.toBytes 8 rbp.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk NestedUnmarshalSSZ 138
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
