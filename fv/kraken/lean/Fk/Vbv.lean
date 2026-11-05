import Fk.Code
import Fk.Step
import Fk.Labels
import Fk.Bytes
import Fk.Flags
import Fk.Contracts
import Fk.FunSpecs

open Fk Fk.Code

theorem vbv_and7 (x : BitVec 64) (c : BitVec 32) (hc : c = 7) :
    BitVec.zeroExtend 64 (BitVec.extractLsb' 0 32 x &&& c) = BitVec.ofNat 64 (x.toNat % 8) := by
  subst hc
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_and, BitVec.extractLsb'_toNat, BitVec.toNat_ofNat]
  have : (7 : Nat) = 2 ^ 3 - 1 := rfl
  simp only [Nat.shiftRight_zero]
  rw [show (7 : BitVec 32).toNat = 2 ^ 3 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem vbv_nz {w : Nat} (r : BitVec w) (f : StatusFlags.from_result.Remaining) :
    CondCode.nz.interp (StatusFlags.from_result (r &&& r) f) = (r != 0) := by
  simp [CondCode.interp, StatusFlags.from_result, BitVec.zero, bne]

theorem vbv_low8 (d : BitVec 64) (n : BitVec 8) : BitVec.extractLsb' 0 8 (d.replaceLow n) = n := by
  ext i hi
  simp only [BitVec.replaceLow, BitVec.getElem_extractLsb', BitVec.getLsbD_setWidth]
  erw [BitVec.getLsbD_append]
  simp [hi]; omega

theorem vbv_len (x : BitVec 64) (b : Bool) :
    x.ushiftRight 3 + BitVec.zeroExtend 64 (BitVec.zeroExtend 32 (BitVec.ofNat 8 b.toNat))
      = BitVec.ofNat 64 (x.toNat / 8 + b.toNat) := by
  apply BitVec.eq_of_toNat_eq
  have := x.isLt
  cases b <;> simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow] <;> omega

theorem vbv_bl (x y : BitVec 64) (h : y.toNat = x.toNat / 8 + (if x.toNat % 8 = 0 then 0 else 1)) :
    BitVec.ofNat 64 (x.toNat / 8 + (BitVec.ofNat 64 (x.toNat % 8) != 0).toNat) = y := by
  apply BitVec.eq_of_toNat_eq
  have := x.isLt; have := y.isLt
  by_cases hp : x.toNat % 8 = 0
  · simp only [hp, ↓reduceIte] at h
    simp [hp]; omega
  · simp only [hp, ↓reduceIte] at h
    have : (BitVec.ofNat 64 (x.toNat % 8) != 0) = true := by
      simp [bne, BitVec.ofNat_eq_ofNat]; intro h'; have := congrArg BitVec.toNat h'; simp at this; omega
    rw [this]; simp; omega

theorem vbv_zand {w : Nat} (r : BitVec w) (f : StatusFlags.from_result.Remaining) :
    CondCode.z.interp (StatusFlags.from_result (r &&& r) f) = (r == 0) := by
  simp [CondCode.interp, StatusFlags.from_result, BitVec.zero]

theorem vbv_mod8_ne (x : Nat) (h : x % 8 ≠ 0) : (BitVec.ofNat 64 (x % 8) == 0) = false := by
  simp only [beq_eq_false_iff_ne, ne_eq]; intro h'; have := congrArg BitVec.toNat h'; simp at this; omega

theorem vbv_dec_lt (y : BitVec 64) (h : 1 ≤ y.toNat) : (y + -1).toNat < y.toNat := by
  rw [← BitVec.sub_eq_add_neg, BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; simp; omega)]; simp; omega

theorem vbv_cnt (x : Nat) : (BitVec.extractLsb' 0 8 (BitVec.ofNat 64 (x % 8))).toNat &&& 31 = x % 8 := by
  have h8 : x % 8 < 8 := Nat.mod_lt _ (by decide)
  have : (BitVec.extractLsb' 0 8 (BitVec.ofNat 64 (x % 8))).toNat = x % 8 := by
    simp [BitVec.extractLsb'_toNat]; omega
  rw [this, show (31 : Nat) = 2 ^ 5 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]; omega

theorem vbv_byte (b : UInt8) :
    BitVec.extractLsb' 0 8 (BitVec.zeroExtend 64 (BitVec.zeroExtend 32 (BitVec.ofInt 8 (Int.ofBytes [b])))) = b.toBitVec := by
  rw [zx8]; apply BitVec.eq_of_toNat_eq; simp [Int.ofBytes, BitVec.toNat_ofInt]

theorem vbv_shr_zero (b : UInt8) (p : Nat) (h : b.toNat >>> p = 0) : (b.toBitVec.ushiftRight p == 0) = true := by
  simp only [beq_iff_eq]; apply BitVec.eq_of_toNat_eq; simpa [BitVec.toNat_ushiftRight] using h

theorem vbv_split (init : List UInt8) (last : UInt8) (y : BitVec 64) (h : init.length + 1 = y.toNat) :
    init.length + [last].length ≤ 2 ^ 64 := by
  have := y.isLt; simp; omega

theorem vbv_last_addr (x y : BitVec 64) (n : Nat) (h : n + 1 = y.toNat) :
    y + x * 1#64 + -1 = x + BitVec.ofNat 64 n := by
  rw [BitVec.mul_one]
  have : BitVec.ofNat 64 n = y - 1 := by apply BitVec.eq_of_toNat_eq; simp; omega
  rw [this]; bv_omega

theorem vbv_pop (x : BitVec 64) : (40 : BitVec 64) + (x - 8#64 - 40) = x - 8 := by bv_omega
theorem vbv_ret (x : BitVec 64) : x - 8 + 8#64 = x := by bv_omega
theorem vbv_ge1 (y : UInt64) (n : Nat) (h : n + 1 = y.toNat) : 1 ≤ y.toBitVec.toNat := by
  show 1 ≤ y.toNat; omega

-- "bitvector padding bits are not zero" (ssz/unmarshal.go, ValidateBitvector)
def vbvFmt : List UInt8 :=
  [98, 105, 116, 118, 101, 99, 116, 111, 114, 32, 112, 97, 100, 100, 105, 110, 103, 32, 98, 105, 116, 115, 32, 97, 114, 101, 32, 110, 111, 116, 32, 122, 101, 114, 111]
theorem vbvFmt_len : vbvFmt.length = 35 := by rfl
theorem vbvFmt_nopct : (0x25 : UInt8) ∉ vbvFmt := by simp [vbvFmt]

theorem vbv_call (x : BitVec 64) : x - 8#64 - 40 - 8#64 = x - 56 := by bv_omega
theorem vbv_slot' (x : BitVec 64) : ({ toBitVec := x - 56 } + 8 : UInt64).toBitVec - 8#64 = x - 56 := by
  simp only [UInt64.toBitVec_add, UInt64.toBitVec_ofNat]; bv_omega
theorem vbv_pop2 (x : BitVec 64) : (40 : BitVec 64) + ({ toBitVec := x - 56 } + 8 : UInt64).toBitVec = x - 8 := by
  simp only [UInt64.toBitVec_add, UInt64.toBitVec_ofNat]; bv_omega
theorem vbv_shr_ne (b : UInt8) (p : Nat) (h : b.toNat >>> p ≠ 0) : (b.toBitVec.ushiftRight p == 0) = false := by
  simp only [beq_eq_false_iff_ne, ne_eq]; intro h'; apply h; have := congrArg BitVec.toNat h'; simpa [BitVec.toNat_ushiftRight] using this

theorem vbv_a48 (x : BitVec 64) : x - 48 = x - 56 + 8 := by bv_omega
theorem vbv_a40 (x : BitVec 64) : x - 56 + 8 + BitVec.ofNat 64 8 = x - 56 + 16 := by bv_omega
theorem vbv_o8 (x : BitVec 64) : x + BitVec.ofNat 64 8 = x + 8#64 := rfl

variable [Host]

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 100000 in
theorem vbv_accept_main (k : Nat) (hk : ValidateBitvector.IsInfixAt Host.prog k)
    (hf : LabelsFresh ValidateBitvector k)
    (s : MachineData) (ra guard : UInt64) (fp sp : List UInt8) (hfp : fp.length = 8) (hsp : sp.length = 8)
    (init : List UInt8) (last : UInt8)
    (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (sp.At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq ((init ++ [last]).At s.regs.rax.toBitVec) ⋆ R)
    (hguard : guard.toNat < s.regs.rsp.toNat) (hsp8 : 8 ≤ s.regs.rsp.toNat)
    (hlen : s.regs.rbx.toNat = s.regs.rdi.toNat / 8 + (if s.regs.rdi.toNat % 8 = 0 then 0 else 1))
    (hbuf : init.length + 1 = s.regs.rbx.toNat)
    (hpad : s.regs.rdi.toNat % 8 ≠ 0) (hlast : last.toNat >>> (s.regs.rdi.toNat % 8) = 0) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ fp' sp' : List UInt8, fp'.length = 8 ∧ sp'.length = 8 ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq (fp'.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (sp'.At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq ((init ++ [last]).At s.regs.rax.toBitVec) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hguard hsp8 hlen hpad hlast hbuf ⊢
  have := rsp.toNat_lt_size; have := guard.toNat_lt_size; simp only [UInt64.size] at *
  kat hk ValidateBitvector 0
  kat hk ValidateBitvector 1
  kat hk ValidateBitvector 2
  apply load_step _ _ _ _ (Int.toBytes 8 guard.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk ValidateBitvector 3
  split
  · rename_i h; exfalso
    simp [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, CondCode.interp, StatusFlags.from_result, BitVec.unsigned] at h
    rcases h with h | h
    · apply h; omega
    · have := congrArg BitVec.toNat h; simp [BitVec.toNat_sub] at this; omega
  simp only [Effects.All]
  kat hk ValidateBitvector 4
  apply store_step_at _ _ (rsp.toBitVec - 8) _ _ _ fp _ _ (by bv_omega) (by ecancel) (by exact hfp)
  intro m1 H1
  simp only [Width.bytes, Width.bits] at H1
  kunfold
  kat hk ValidateBitvector 5
  kat hk ValidateBitvector 6
  kat hk ValidateBitvector 7
  apply store_step_at _ _ (rsp.toBitVec + 8) _ _ _ sp _ _ (by bv_omega) (by ecancel) (by exact hsp)
  intro m2 H2
  simp only [Width.bytes, Width.bits] at H2
  kunfold
  kat hk ValidateBitvector 8
  kat hk ValidateBitvector 9
  intro _
  rw [vbv_and7 rdi.toBitVec (BitVec.truncate 32 (7 : BitVec 64)) (by decide)]
  kat hk ValidateBitvector 10
  kshl64 3
  kat hk ValidateBitvector 11
  intro _
  kat hk ValidateBitvector 12
  rw [vbv_nz]
  kat hk ValidateBitvector 13
  rw [vbv_low8]
  kat hk ValidateBitvector 14
  rw [vbv_len, vbv_bl rdi.toBitVec rbx.toBitVec hlen]
  kat hk ValidateBitvector 15
  kat hk ValidateBitvector 16
  split
  case isTrue h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
  simp only [Effects.All]
  kat hk ValidateBitvector 17
  intro _
  kat hk ValidateBitvector 18
  rw [vbv_zand, vbv_mod8_ne rdi.toBitVec.toNat hpad]
  simp only [Bool.false_eq_true, ↓reduceIte, Effects.All]
  kat hk ValidateBitvector 19
  kat hk ValidateBitvector 20
  kat hk ValidateBitvector 21
  kat hk ValidateBitvector 22
  rw [cmp_be_false _ _ _ _ (vbv_dec_lt _ (vbv_ge1 _ _ hbuf))]
  simp only [Bool.false_eq_true, ↓reduceIte, Effects.All]
  kat hk ValidateBitvector 23
  rw [Mem.At_append_sep _ _ _ (vbv_split init last rbx.toBitVec hbuf)] at H2
  rw [vbv_last_addr _ _ _ hbuf]
  apply load_step _ _ _ _ [last] _ _ (by ecancel) (by rfl)
  kunfold
  kat hk ValidateBitvector 24
  rw [vbv_cnt]
  have hp0 : (rdi.toBitVec.toNat % 8 == 0) = false := by simpa using hpad
  simp only [hp0, Bool.false_eq_true, ↓reduceIte, Effects.All]
  intro _
  rw [if_pos (Nat.mod_lt _ (by decide))]
  rw [vbv_byte]
  split
  all_goals (try intro _)
  all_goals (
    kat hk ValidateBitvector 25
    intro _
    kat hk ValidateBitvector 26
    rw [vbv_zand, vbv_low8, vbv_shr_zero last (rdi.toBitVec.toNat % 8) hlast]
    simp only [↓reduceIte, Effects.All]
    klabel hk hf ValidateBitvector 47
    kat hk ValidateBitvector 47
    kat hk ValidateBitvector 48
    intro _
    kat hk ValidateBitvector 49
    intro _
    kat hk ValidateBitvector 50
    kat hk ValidateBitvector 51
    rw [vbv_pop]
    apply load_step _ _ _ _ (Int.toBytes 8 rbp.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
    kunfold
    kat hk ValidateBitvector 52
    rw [vbv_ret]
    apply load_step _ _ _ _ (Int.toBytes 8 ra.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
    kunfold
    apply Eventually.done
    simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, Fk.ofInt_ofBytes_toBytes64] at *
    refine ⟨trivial, ?_, ?_, ?_, ?_, ?_, _, _, Int.toBytes_length 8 rbp.toBitVec.toInt, Int.toBytes_length 8 rax.toBitVec.toInt, ?mem⟩
    case mem => rw [Mem.At_append_sep _ _ _ (vbv_split init last rbx.toBitVec hbuf)]; ecancel
    all_goals first
      | trivial | rfl
      | (apply UInt64.toBitVec_inj.mp; simp; done)
      | (apply UInt64.toBitVec_inj.mp; simp; bv_omega))

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 100000 in
theorem vbv_reject_pad_main (k : Nat) (hk : ValidateBitvector.IsInfixAt Host.prog k)
    (hf : LabelsFresh ValidateBitvector k)
    (s : MachineData) (ra guard : UInt64) (fp sp fr rslot : List UInt8) (hfp : fp.length = 8) (hsp : sp.length = 8)
    (hfr : fr.length = 40) (hrs : rslot.length = 8)
    (init : List UInt8) (last : UInt8)
    (R : DataMem → Prop) (S : Nat) (scratch : List UInt8) (hsc : scratch.length = S)
    (Heap : Nat → DataMem → Prop) (avail : Nat) (hav : 16 ≤ avail)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (sp.At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq (fr.At (s.regs.rsp.toBitVec - 48)) ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 56))
      ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - 56 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq ((init ++ [last]).At s.regs.rax.toBitVec)
      ⋆ Eq (vbvFmt.At (label "go_string._" + 27706).toBitVec) ⋆ Heap avail ⋆ R)
    (hguard : guard.toNat < s.regs.rsp.toNat) (hsp8 : 8 ≤ s.regs.rsp.toNat)
    (hlen : s.regs.rbx.toNat = s.regs.rdi.toNat / 8 + (if s.regs.rdi.toNat % 8 = 0 then 0 else 1))
    (hbuf : init.length + 1 = s.regs.rbx.toNat)
    (hpad : s.regs.rdi.toNat % 8 ≠ 0) (hlast : last.toNat >>> (s.regs.rdi.toNat % 8) ≠ 0)
    (hfe : FmtErrorfNilC S) (hno : NewobjectC Heap (label "type__" + 82848).toBitVec 16 S) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec
        ∧ st.data.regs.rax.toBitVec = (label "go_itab._errors.errorString_error").toBitVec
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ fp' sp' fr' rs' sc' obj : List UInt8, fp'.length = 8 ∧ sp'.length = 8 ∧ fr'.length = 40 ∧ rs'.length = 8
          ∧ sc'.length = S ∧ obj.length = 16 ∧ obj = Int.toBytes 8 (label "go_string._" + 27706).toBitVec.toInt ++ Int.toBytes 8 (35 : BitVec 64).toInt ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq (fp'.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (sp'.At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq (fr'.At (s.regs.rsp.toBitVec - 48)) ⋆ Eq (rs'.At (s.regs.rsp.toBitVec - 56))
          ⋆ Eq (sc'.At (s.regs.rsp.toBitVec - 56 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq ((init ++ [last]).At s.regs.rax.toBitVec)
          ⋆ Eq (vbvFmt.At (label "go_string._" + 27706).toBitVec) ⋆ Eq (obj.At st.data.regs.rbx.toBitVec)
          ⋆ Heap (avail - 16) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hguard hsp8 hlen hpad hlast hbuf ⊢
  have := rsp.toNat_lt_size; have := guard.toNat_lt_size; simp only [UInt64.size] at *
  kat hk ValidateBitvector 0
  kat hk ValidateBitvector 1
  kat hk ValidateBitvector 2
  apply load_step _ _ _ _ (Int.toBytes 8 guard.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk ValidateBitvector 3
  split
  · rename_i h; exfalso
    simp [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, CondCode.interp, StatusFlags.from_result, BitVec.unsigned] at h
    rcases h with h | h
    · apply h; omega
    · have := congrArg BitVec.toNat h; simp [BitVec.toNat_sub] at this; omega
  simp only [Effects.All]
  kat hk ValidateBitvector 4
  apply store_step_at _ _ (rsp.toBitVec - 8) _ _ _ fp _ _ (by bv_omega) (by ecancel) (by exact hfp)
  intro m1 H1
  simp only [Width.bytes, Width.bits] at H1
  kunfold
  kat hk ValidateBitvector 5
  kat hk ValidateBitvector 6
  kat hk ValidateBitvector 7
  apply store_step_at _ _ (rsp.toBitVec + 8) _ _ _ sp _ _ (by bv_omega) (by ecancel) (by exact hsp)
  intro m2 H2
  simp only [Width.bytes, Width.bits] at H2
  kunfold
  kat hk ValidateBitvector 8
  kat hk ValidateBitvector 9
  intro _
  rw [vbv_and7 rdi.toBitVec (BitVec.truncate 32 (7 : BitVec 64)) (by decide)]
  kat hk ValidateBitvector 10
  kshl64 3
  kat hk ValidateBitvector 11
  intro _
  kat hk ValidateBitvector 12
  rw [vbv_nz]
  kat hk ValidateBitvector 13
  rw [vbv_low8]
  kat hk ValidateBitvector 14
  rw [vbv_len, vbv_bl rdi.toBitVec rbx.toBitVec hlen]
  kat hk ValidateBitvector 15
  kat hk ValidateBitvector 16
  split
  case isTrue h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
  simp only [Effects.All]
  kat hk ValidateBitvector 17
  intro _
  kat hk ValidateBitvector 18
  rw [vbv_zand, vbv_mod8_ne rdi.toBitVec.toNat hpad]
  simp only [Bool.false_eq_true, ↓reduceIte, Effects.All]
  kat hk ValidateBitvector 19
  kat hk ValidateBitvector 20
  kat hk ValidateBitvector 21
  kat hk ValidateBitvector 22
  rw [cmp_be_false _ _ _ _ (vbv_dec_lt _ (vbv_ge1 _ _ hbuf))]
  simp only [Bool.false_eq_true, ↓reduceIte, Effects.All]
  kat hk ValidateBitvector 23
  rw [Mem.At_append_sep _ _ _ (vbv_split init last rbx.toBitVec hbuf)] at H2
  rw [vbv_last_addr _ _ _ hbuf]
  apply load_step _ _ _ _ [last] _ _ (by ecancel) (by rfl)
  kunfold
  kat hk ValidateBitvector 24
  rw [vbv_cnt]
  have hp0 : (rdi.toBitVec.toNat % 8 == 0) = false := by simpa using hpad
  simp only [hp0, Bool.false_eq_true, ↓reduceIte, Effects.All]
  intro _
  rw [if_pos (Nat.mod_lt _ (by decide))]
  rw [vbv_byte]
  split
  all_goals (try intro _)
  all_goals (
    kat hk ValidateBitvector 25
    intro _
    kat hk ValidateBitvector 26
    rw [vbv_zand, vbv_low8, vbv_shr_ne last (rdi.toBitVec.toNat % 8) hlast]
    simp only [Bool.false_eq_true, ↓reduceIte, Effects.All]
    kat hk ValidateBitvector 27
    kat hk ValidateBitvector 28
    kat hk ValidateBitvector 29
    intro _
    kat hk ValidateBitvector 30
    intro _
    kat hk ValidateBitvector 31
    kat hk ValidateBitvector 32
    apply store_step_at _ _ (rsp.toBitVec - 56) _ _ _ rslot _ _ (vbv_call _) (by ecancel) (by exact hrs)
    intro m5 H5
    simp only [Width.bytes, Width.bits] at H5
    kunfold
    rw [vbv_call] at *
    have hA : rsp.toBitVec - 56 + 8 = rsp.toBitVec - 48 := by bv_omega
    refine eventually_trans _ _ _ _ (hfe _ (Host.addrOf (k + 32 + 1)) vbvFmt scratch fr _
      (by rw [vbvFmt_len]; rfl) (by apply UInt64.toBitVec_inj.mp; simp) vbvFmt_nopct hsc hfr
      (by dsimp only; rw [hA]; ecancel)) ?_
    rintro ⟨d2, pc2⟩ ⟨hpc2, hrsp2, hr142, hrax2, stk2, sp2, hstk2, hsp2, Hm2⟩
    dsimp only at hpc2 hrsp2 hrax2 hr142 Hm2
    subst hpc2
    obtain ⟨⟨rax2, rbx2, rcx2, rdx2, rsi2, rdi2, rsp2, rbp2, r82, r92, r102, r112, r122, r132, r142, r152⟩,
      zmms2, flags2, mem2⟩ := d2
    simp only at hrsp2 hrax2 hr142 Hm2
    subst hrsp2 hrax2 hr142
    kat hk ValidateBitvector 33
    intro _
    kat hk ValidateBitvector 34
    split
    case isTrue h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
    simp only [Effects.All]
    kat hk ValidateBitvector 35
    kat hk ValidateBitvector 36
    kat hk ValidateBitvector 37
    apply store_step_at _ _ (rsp.toBitVec - 56) _ _ _ (Int.toBytes 8 (Host.addrOf (k + 32 + 1)).toBitVec.toInt) _ _
      (vbv_slot' _) (by ecancel) (by exact Int.toBytes_length 8 _)
    intro m6 H6
    simp only [Width.bytes, Width.bits] at H6
    kunfold
    rw [vbv_slot'] at *
    rw [← List.take_append_drop 8 sp2, at_app (sp2.take 8) (sp2.drop 8) (b := rsp.toBitVec - 56 + 16)
      (by simp [hsp2]; bv_omega) (by simp [hsp2])] at H6
    refine eventually_trans _ _ _ _ (hno _ (Host.addrOf (k + 37 + 1)) avail stk2 (sp2.take 8) _ rfl hav hstk2
      (by simp [hsp2]) (by dsimp only; ecancel)) ?_
    rintro ⟨d3, pc3⟩ ⟨hpc3, hrsp3, hr143, -, stk3, sn3, hstk3, hsn3, Hm3⟩
    dsimp only at hpc3 hrsp3 hr143 Hm3
    subst hpc3
    obtain ⟨⟨rax3, rbx3, rcx3, rdx3, rsi3, rdi3, rsp3, rbp3, r83, r93, r103, r113, r123, r133, r143, r153⟩,
      zmms3, flags3, mem3⟩ := d3
    simp only at hrsp3 hr143 Hm3
    subst hrsp3 hr143
    rw [show List.replicate 16 (0 : UInt8) = List.replicate 8 0 ++ List.replicate 8 0 from rfl,
      Mem.At_append_sep _ _ _ (by simp)] at Hm3
    simp only [List.length_replicate] at Hm3
    kat hk ValidateBitvector 38
    apply store_step_at _ _ (rax3.toBitVec + BitVec.ofNat 64 8) _ _ _ (List.replicate 8 0) _ _ (by bv_omega) (by ecancel) (by simp)
    intro m7 H7
    simp only [Width.bytes, Width.bits] at H7
    kunfold
    kat hk ValidateBitvector 39
    kat hk ValidateBitvector 40
    apply store_step _ _ _ _ _ (List.replicate 8 0) _ _ (by ecancel) (by simp)
    intro m8 H8
    simp only [Width.bytes, Width.bits] at H8
    kunfold
    kat hk ValidateBitvector 41
    kat hk ValidateBitvector 42
    kat hk ValidateBitvector 43
    kat hk ValidateBitvector 44
    kat hk ValidateBitvector 45
    rw [vbv_pop2]
    apply load_step _ _ _ _ (Int.toBytes 8 rbp.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
    kunfold
    kat hk ValidateBitvector 46
    rw [vbv_ret]
    apply load_step _ _ _ _ (Int.toBytes 8 ra.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
    kunfold
    apply Eventually.done
    simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
    refine ⟨trivial, ?_, ?_, ?_, ?_, _, _, sn3 ++ List.drop 8 sp2, _, stk3,
      Int.toBytes 8 (label "go_string._" + 27706).toBitVec.toInt ++ Int.toBytes 8 (BitVec.toInt (35 : BitVec 64)),
      Int.toBytes_length 8 rbp.toBitVec.toInt, Int.toBytes_length 8 rax.toBitVec.toInt,
      by simp [hsn3, hsp2], Int.toBytes_length 8 (Host.addrOf (k + 37 + 1)).toBitVec.toInt, hstk3, by simp [Int.toBytes_length], rfl, ?mem⟩
    case mem =>
      have hb := vbv_split init last rbx.toBitVec hbuf
      rw [vbv_a48, Mem.At_append_sep sn3 (List.drop 8 sp2) _ (by simp [hsn3, hsp2]),
        Mem.At_append_sep init [last] _ hb, Mem.At_append_sep (Int.toBytes 8 _) (Int.toBytes 8 _) _ (by simp [Int.toBytes_length])]
      simp only [hsn3, Int.toBytes_length]
      rw [vbv_a40, vbv_o8]
      simp only [Std.ExtHashMap.sep_emp] at H8
      refine Eq.mp ?_ H8
      exact congrFun (by ac_rfl) _
    all_goals first | trivial | rfl | (apply UInt64.toBitVec_inj.mp; simp))

namespace Fk

/-- Function specification of `ssz.ValidateBitvector`, accept path with padding
bits (`bits % 8 ≠ 0`): derived from `vbv_accept_main`, not assumed. -/
def VbvAccC : Prop :=
  ∀ (st : MachineData) (ret : Int64) (guard : UInt64) (fp sp init : List UInt8) (last : UInt8) (R : DataMem → Prop),
    fp.length = 8 → sp.length = 8 → guard.toNat < st.regs.rsp.toNat → 8 ≤ st.regs.rsp.toNat →
    st.regs.rbx.toNat = st.regs.rdi.toNat / 8 + (if st.regs.rdi.toNat % 8 = 0 then 0 else 1) →
    init.length + 1 = st.regs.rbx.toNat → st.regs.rdi.toNat % 8 ≠ 0 → last.toNat >>> (st.regs.rdi.toNat % 8) = 0 →
    (Eq ((Int.toBytes 8 ret.toBitVec.toInt).At st.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (st.regs.rsp.toBitVec - 8)) ⋆ Eq (sp.At (st.regs.rsp.toBitVec + 8))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (st.regs.r14.toBitVec + 16))
      ⋆ Eq ((init ++ [last]).At st.regs.rax.toBitVec) ⋆ R) st.dmem →
    Eventually (step1 Host.exe)
      (fun st' => st'.pc = ret ∧ st'.data.regs.rax = 0 ∧ st'.data.regs.rbx = 0
        ∧ st'.data.regs.rsp = st.regs.rsp + 8 ∧ st'.data.regs.rbp = st.regs.rbp ∧ st'.data.regs.r14 = st.regs.r14 ∧
        ∃ fp' sp' : List UInt8, fp'.length = 8 ∧ sp'.length = 8 ∧
        (Eq ((Int.toBytes 8 ret.toBitVec.toInt).At st.regs.rsp.toBitVec)
          ⋆ Eq (fp'.At (st.regs.rsp.toBitVec - 8)) ⋆ Eq (sp'.At (st.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (st.regs.r14.toBitVec + 16))
          ⋆ Eq ((init ++ [last]).At st.regs.rax.toBitVec) ⋆ R) st'.data.dmem)
      ⟨st, label "ssz.ValidateBitvector"⟩

theorem vbv_acc_holds (k : Nat) (hk : ValidateBitvector.IsInfixAt Host.prog k)
    (hf : LabelsFresh ValidateBitvector k) : VbvAccC := by
  intro st ret guard fp sp init last R hfp hsp hg h8 hlen hbuf hpad hlast hm
  rw [label_at hk hf (j := 0) (by rfl) (by intro i hi; omega)]
  have h := vbv_accept_main k hk hf st (UInt64.ofBitVec ret.toBitVec) guard fp sp hfp hsp init last R hm hg h8 hlen
    hbuf hpad hlast
  simp only [Nat.add_zero] at h
  exact h

/-- Function specification of `ssz.ValidateBitvector`, padding-reject path:
derived from `vbv_reject_pad_main` under the `fmt.errorf` (nil) and
`runtime.newobject` contracts. -/
def VbvPadC (Heap : Nat → DataMem → Prop) (S : Nat) : Prop :=
  ∀ (st : MachineData) (ret : Int64) (guard : UInt64) (fp sp fr rslot init scratch : List UInt8) (last : UInt8)
    (avail : Nat) (R : DataMem → Prop),
    fp.length = 8 → sp.length = 8 → fr.length = 40 → rslot.length = 8 → scratch.length = S → 16 ≤ avail →
    guard.toNat < st.regs.rsp.toNat → 8 ≤ st.regs.rsp.toNat →
    st.regs.rbx.toNat = st.regs.rdi.toNat / 8 + (if st.regs.rdi.toNat % 8 = 0 then 0 else 1) →
    init.length + 1 = st.regs.rbx.toNat → st.regs.rdi.toNat % 8 ≠ 0 → last.toNat >>> (st.regs.rdi.toNat % 8) ≠ 0 →
    (Eq ((Int.toBytes 8 ret.toBitVec.toInt).At st.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (st.regs.rsp.toBitVec - 8)) ⋆ Eq (sp.At (st.regs.rsp.toBitVec + 8))
      ⋆ Eq (fr.At (st.regs.rsp.toBitVec - 48)) ⋆ Eq (rslot.At (st.regs.rsp.toBitVec - 56))
      ⋆ Eq (scratch.At (st.regs.rsp.toBitVec - 56 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (st.regs.r14.toBitVec + 16))
      ⋆ Eq ((init ++ [last]).At st.regs.rax.toBitVec)
      ⋆ Eq (vbvFmt.At (label "go_string._" + 27706).toBitVec) ⋆ Heap avail ⋆ R) st.dmem →
    Eventually (step1 Host.exe)
      (fun st' => st'.pc = ret
        ∧ st'.data.regs.rax.toBitVec = (label "go_itab._errors.errorString_error").toBitVec
        ∧ st'.data.regs.rsp = st.regs.rsp + 8 ∧ st'.data.regs.rbp = st.regs.rbp ∧ st'.data.regs.r14 = st.regs.r14 ∧
        ∃ fp' sp' fr' rs' sc' obj : List UInt8, fp'.length = 8 ∧ sp'.length = 8 ∧ fr'.length = 40 ∧ rs'.length = 8
          ∧ sc'.length = S ∧ obj.length = 16 ∧ obj = Int.toBytes 8 (label "go_string._" + 27706).toBitVec.toInt ++ Int.toBytes 8 (35 : BitVec 64).toInt ∧
        (Eq ((Int.toBytes 8 ret.toBitVec.toInt).At st.regs.rsp.toBitVec)
          ⋆ Eq (fp'.At (st.regs.rsp.toBitVec - 8)) ⋆ Eq (sp'.At (st.regs.rsp.toBitVec + 8))
          ⋆ Eq (fr'.At (st.regs.rsp.toBitVec - 48)) ⋆ Eq (rs'.At (st.regs.rsp.toBitVec - 56))
          ⋆ Eq (sc'.At (st.regs.rsp.toBitVec - 56 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (st.regs.r14.toBitVec + 16))
          ⋆ Eq ((init ++ [last]).At st.regs.rax.toBitVec)
          ⋆ Eq (vbvFmt.At (label "go_string._" + 27706).toBitVec) ⋆ Eq (obj.At st'.data.regs.rbx.toBitVec)
          ⋆ Heap (avail - 16) ⋆ R) st'.data.dmem)
      ⟨st, label "ssz.ValidateBitvector"⟩

theorem vbv_pad_holds (k : Nat) (hk : ValidateBitvector.IsInfixAt Host.prog k)
    (hf : LabelsFresh ValidateBitvector k) (Heap : Nat → DataMem → Prop) (S : Nat)
    (hfe : FmtErrorfNilC S) (hno : NewobjectC Heap (label "type__" + 82848).toBitVec 16 S) : VbvPadC Heap S := by
  intro st ret guard fp sp fr rslot init scratch last avail R hfp hsp hfr hrs hsc hav hg h8 hlen hbuf hpad hlast hm
  rw [label_at hk hf (j := 0) (l := "ssz.ValidateBitvector") (by rfl) (by intro i hi; omega)]
  have h := vbv_reject_pad_main k hk hf st (UInt64.ofBitVec ret.toBitVec) guard fp sp fr rslot hfp hsp hfr hrs init last
    R S scratch hsc Heap avail hav hm hg h8 hlen hbuf hpad hlast hfe hno
  simp only [Nat.add_zero] at h
  exact h

end Fk
