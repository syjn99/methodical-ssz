import Fk.BlAccept

/-!
# BitL.UnmarshalSSZ, ValidateBitlist error path

`bl_reject_invalid_main`: with `len(buf) = 4 + n` (n ≥ 1), offset 4 and a tail
`tl` that EthLib's bitlist rule rejects (`¬ blValid tl`), the decoder calls
`ssz.ValidateBitlist`, reads the errorString itab's type word, wraps the error
-/

open Fk Fk.Code Fv1 EthLib.Serialization.Ssz
variable [Host]

theorem blr_60 (x : BitVec 64) : x - 120 + 96 = x - 24 := by bv_omega
theorem blr_68 (x : BitVec 64) : x - 120 + 104 = x - 16 := by bv_omega

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 100000 in
theorem bl_reject_invalid_main (k : Nat) (hk : BitLUnmarshalSSZ.IsInfixAt Host.prog k)
    (hf : LabelsFresh BitLUnmarshalSSZ k)
    (tl : List UInt8) (hn1 : 1 ≤ tl.length) (hinv : ¬ blValid tl)
    (s : MachineData) (ra guard : UInt64)
    (fp s8 s16 s24 l48 l80 a16 rslot ity : List UInt8)
    (hfp : fp.length = 8) (h8 : s8.length = 8) (h16 : s16.length = 8) (h24 : s24.length = 8)
    (hl48 : l48.length = 8) (hl80 : l80.length = 8) (ha16 : a16.length = 16) (hrs : rslot.length = 8)
    (hity : ity.length = 8)
    (R : DataMem → Prop) (S : Nat) (scratch spl : List UInt8) (hsc : scratch.length = S) (hspl : spl.length = 40)
    (Heap : Nat → DataMem → Prop) (avail : Nat) (hav : 16640 ≤ avail)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s8.At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq (s16.At (s.regs.rsp.toBitVec + 16)) ⋆ Eq (s24.At (s.regs.rsp.toBitVec + 24))
      ⋆ Eq (a16.At (s.regs.rsp.toBitVec - 24))
      ⋆ Eq (l48.At (s.regs.rsp.toBitVec - 48)) ⋆ Eq (l80.At (s.regs.rsp.toBitVec - 80))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 128)) ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - 128 - BitVec.ofNat 64 S))
      ⋆ Eq (spl.At (s.regs.rsp.toBitVec - 120))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16)) ⋆ Heap avail
      ⋆ Eq ([4, 0, 0, 0].At s.regs.rbx.toBitVec) ⋆ Eq (tl.At (s.regs.rbx.toBitVec + 4))
      ⋆ Eq (ity.At ((label "go_itab._errors.errorString_error").toBitVec + 8))
      ⋆ Eq (blFmtB.At blFmtB_addr) ⋆ vblRO ⋆ R)
    (hguard : guard.toNat < s.regs.rsp.toNat) (hsp : 128 ≤ s.regs.rsp.toNat)
    (hlen : s.regs.rcx.toNat = 4 + tl.length) (hcap : s.regs.rcx.toNat ≤ s.regs.rdi.toNat)
    (hcap63 : s.regs.rdi.toNat < 2 ^ 63)
    (hit : (label "go_itab._errors.errorString_error").toBitVec ≠ 0)
    (hvbe : ValidateBitlistErrC Heap S) (hfe : FmtErrorfWC Heap blFmtB vblRO VblMsg S) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax ≠ 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp
        ∧ (Eq ([4, 0, 0, 0].At s.regs.rbx.toBitVec) ⋆ Eq (tl.At (s.regs.rbx.toBitVec + 4)) ⋆ vblRO ⋆ R
          ⋆ fun _ => True) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hguard hsp hlen hcap hcap63 ⊢
  have := rsp.toNat_lt_size; have := guard.toNat_lt_size; have := rcx.toNat_lt_size; have := rdi.toNat_lt_size
  simp only [UInt64.size] at *
  kat hk BitLUnmarshalSSZ 0
  kat hk BitLUnmarshalSSZ 1
  kat hk BitLUnmarshalSSZ 2
  apply load_step _ _ _ _ (Int.toBytes 8 guard.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk BitLUnmarshalSSZ 3
  split
  · rename_i h; exfalso
    simp [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, CondCode.interp, StatusFlags.from_result, BitVec.unsigned] at h
    rcases h with h | h
    · apply h; omega
    · have := congrArg BitVec.toNat h; simp [BitVec.toNat_sub] at this; omega
  simp only [Effects.All]
  kat hk BitLUnmarshalSSZ 4
  apply store_step_at _ _ (rsp.toBitVec - 8) _ _ _ fp _ _ (by bv_omega) (by ecancel) (by exact hfp)
  intro m1 H1
  simp only [Width.bytes, Width.bits] at H1
  kunfold
  kat hk BitLUnmarshalSSZ 5
  kat hk BitLUnmarshalSSZ 6
  kat hk BitLUnmarshalSSZ 7
  apply store_step_at _ _ (rsp.toBitVec + 16) _ _ _ s16 _ _ (by bv_omega) (by ecancel) (by exact h16)
  intro m2 H2
  simp only [Width.bytes, Width.bits] at H2
  kunfold
  kat hk BitLUnmarshalSSZ 8
  kat hk BitLUnmarshalSSZ 9
  kat hk BitLUnmarshalSSZ 10
  split
  case isTrue h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned] at h; omega
  simp only [Effects.All]
  kat hk BitLUnmarshalSSZ 11
  apply load_step_at _ _ rbx.toBitVec _ _ [4, 0, 0, 0] _ _ (by bv_omega) (by ecancel) (by simp)
  simp only [show Int.ofBytes [4, 0, 0, 0] = 4 by simp [Int.ofBytes]]
  kunfold
  kat hk BitLUnmarshalSSZ 12
  kat hk BitLUnmarshalSSZ 13
  kat hk BitLUnmarshalSSZ 14
  kat hk BitLUnmarshalSSZ 15
  split
  case isTrue h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
  simp only [Effects.All]
  kat hk BitLUnmarshalSSZ 16
  apply store_step_at _ _ (rsp.toBitVec + 8) _ _ _ s8 _ _ (by kaddr) (by ecancel) (by exact h8)
  intro m3 H3
  simp only [Width.bytes, Width.bits] at H3
  kunfold
  kat hk BitLUnmarshalSSZ 17
  apply store_step_at _ _ (rsp.toBitVec + 24) _ _ _ s24 _ _ (by kaddr) (by ecancel) (by exact h24)
  intro m4 H4
  simp only [Width.bytes, Width.bits] at H4
  kunfold
  kat hk BitLUnmarshalSSZ 18
  kat hk BitLUnmarshalSSZ 19
  kat hk BitLUnmarshalSSZ 20
  kat hk BitLUnmarshalSSZ 21
  kshl64 63
  kat hk BitLUnmarshalSSZ 22
  intro _
  rw [lc_rdx4 _ (by simp; omega) (by simp; omega)]
  kat hk BitLUnmarshalSSZ 23
  rw [bla_rbx4]
  kat hk BitLUnmarshalSSZ 24
  apply store_step_at _ _ (rsp.toBitVec - 48) _ _ _ l48 _ _ (by kaddr) (by ecancel) (by exact hl48)
  intro m5 H5
  simp only [Width.bytes, Width.bits] at H5
  kunfold
  kat hk BitLUnmarshalSSZ 25
  kat hk BitLUnmarshalSSZ 26
  apply store_step_at _ _ (rsp.toBitVec - 80) _ _ _ l80 _ _ (by kaddr) (by ecancel) (by exact hl80)
  intro m6 H6
  simp only [Width.bytes, Width.bits] at H6
  kunfold
  kat hk BitLUnmarshalSSZ 27
  kat hk BitLUnmarshalSSZ 28
  kat hk BitLUnmarshalSSZ 29
  kat hk BitLUnmarshalSSZ 30
  apply store_step_at _ _ (rsp.toBitVec - 128) _ _ _ rslot _ _ (bla_slot _) (by ecancel) (by exact hrs)
  intro m7 H7
  simp only [Width.bytes, Width.bits] at H7
  kunfold
  rw [bla_slot] at *
  have hn4 : (-4 + rcx.toBitVec).toNat = tl.length := by
    rw [BitVec.add_comm, ← BitVec.sub_eq_add_neg, BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; simp; omega)]
    simp; omega
  have hsv : rsp.toBitVec - 128 + 8 = rsp.toBitVec - 120 := by bv_omega
  rw [← List.take_append_drop 32 spl, at_app (spl.take 32) (spl.drop 32) (b := rsp.toBitVec - 88)
    (by simp [hspl]; bv_omega) (by simp [hspl])] at H7
  refine eventually_trans _ _ _ _ (hvbe _ (Host.addrOf (k + 30 + 1)) avail tl scratch (spl.take 32) _ hn4
    (by apply UInt64.toBitVec_inj.mp; apply BitVec.eq_of_toNat_eq; simp) hsc (by simp [hspl]) hinv (by omega)
    (by dsimp only; rw [hsv]; ecancel)) ?_
  rintro ⟨d1, pc1⟩ ⟨hpc1, hrsp1, -, hrbp1, hrax1, stk1, sv1, msg, hm, esp, av1, hstk1, hsv1, hmsg, -, hav1, Hm1⟩
  dsimp only at hpc1 hrsp1 hrbp1 hrax1 Hm1
  subst hpc1
  obtain ⟨⟨rax1, rbx1, rcx1, rdx1, rsi1, rdi1, rsp1, rbp1, r81, r91, r101, r111, r121, r131, r141, r151⟩,
    zmms1, flags1, mem1⟩ := d1
  simp only at hrsp1 hrbp1 hrax1 Hm1
  subst hrsp1 hrbp1
  rw [hsv] at Hm1
  kat hk BitLUnmarshalSSZ 31
  kat hk BitLUnmarshalSSZ 32
  intro _
  kat hk BitLUnmarshalSSZ 33
  split
  case isTrue h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h; exact hit (by rw [← hrax1, h]; rfl)
  simp only [Effects.All]
  kat hk BitLUnmarshalSSZ 34
  simp only [AvxOperation.interp, MachineData.setAvxLegacy, AvxRegOrMem.interp]
  kunfold
  rw [bla_g, blr_60]
  apply store_avx_step _ _ _ _ a16 _ _ (by ecancel) (by exact ha16) (by decide)
  intro m9 H9
  kunfold
  rw [lr_split16 _ (Int.toBytes_length 16 _) (rsp.toBitVec - 24)] at H9
  kat hk BitLUnmarshalSSZ 35
  intro _
  kat hk BitLUnmarshalSSZ 36
  split
  case isTrue h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h; exact hit (by rw [← hrax1, h]; rfl)
  simp only [Effects.All]
  kat hk BitLUnmarshalSSZ 37
  apply load_step_at _ _ ((label "go_itab._errors.errorString_error").toBitVec + 8) _ _ ity _ _ (by rw [hrax1])
    (by ecancel) (by exact hity)
  kunfold
  kat hk BitLUnmarshalSSZ 38
  kat hk BitLUnmarshalSSZ 39
  rw [bla_g, blr_60]
  apply store_step _ _ _ _ _ ((Int.toBytes 16 (zmms1.get (AvxReg.xmm RegMm.mm15)).toInt).take 8) _ _ (by ecancel)
    (by simp [Int.toBytes_length])
  intro m10 H10
  simp only [Width.bytes, Width.bits] at H10
  kunfold
  kat hk BitLUnmarshalSSZ 40
  rw [bla_g, blr_68, show rsp.toBitVec - 24 + 8 = rsp.toBitVec - 16 by bv_omega] at *
  apply store_step _ _ _ _ _ ((Int.toBytes 16 (zmms1.get (AvxReg.xmm RegMm.mm15)).toInt).drop 8) _ _ (by ecancel)
    (by simp [Int.toBytes_length])
  intro m11 H11
  simp only [Width.bytes, Width.bits] at H11
  kunfold
  kat hk BitLUnmarshalSSZ 41
  kat hk BitLUnmarshalSSZ 42
  kat hk BitLUnmarshalSSZ 43
  rw [bla_g, blr_60]
  kat hk BitLUnmarshalSSZ 44
  kat hk BitLUnmarshalSSZ 45
  kat hk BitLUnmarshalSSZ 46
  rw [bla_slot']
  apply store_step _ _ _ _ _ (Int.toBytes 8 (Host.addrOf (k + 30 + 1)).toBitVec.toInt) _ _ (by ecancel)
    (by exact Int.toBytes_length 8 _)
  intro m12 H12
  simp only [Width.bytes, Width.bits] at H12
  kunfold
  simp only [toBytes_ofInt_ofBytes 64 8 rfl ity hity] at H12
  have hA : Eq ((ity ++ Int.toBytes 8 rbx1.toBitVec.toInt).At (rsp.toBitVec - 24))
      = Eq (ity.At (rsp.toBitVec - 24)) ⋆ Eq ((Int.toBytes 8 rbx1.toBitVec.toInt).At (rsp.toBitVec - 16)) :=
    at_app _ _ (by rw [hity]; bv_omega) (by simp [hity, Int.toBytes_length])
  have hC : Eq ((sv1 ++ spl.drop 32).At (rsp.toBitVec - 128 + 8))
      = Eq (sv1.At (rsp.toBitVec - 120)) ⋆ Eq ((spl.drop 32).At (rsp.toBitVec - 88)) := by
    rw [show rsp.toBitVec - 128 + 8 = rsp.toBitVec - 120 by bv_omega]
    exact at_app _ _ (by rw [hsv1]; bv_omega) (by simp [hsv1, hspl])
  have hml := hmsg.len
  refine eventually_trans _ _ _ _ (hfe _ (Host.addrOf (k + 46 + 1)) av1 ity msg hm
    stk1 (sv1 ++ spl.drop 32) rbx1.toBitVec esp _ ?f1 ?f2 ?f3 hity hmsg hstk1 (by simp [hsv1, hspl])
    (by rw [blFmtB_len]; omega)
    (by dsimp only; rw [hA, hC]; ecancel)) ?_
  case f1 => dsimp only; rfl
  case f2 => dsimp only; first | rfl | decide
  case f3 => dsimp only; first | rfl | decide
  rintro ⟨d3, pc3⟩ ⟨hpc3, hrsp3, -, hrax3, stk3, sp3, av3, hstk3, hsp3, hav3, Hm3⟩
  dsimp only at hpc3 hrsp3 hrax3 Hm3
  subst hpc3
  obtain ⟨⟨rax3, rbx3, rcx3, rdx3, rsi3, rdi3, rsp3, rbp3, r83, r93, r103, r113, r123, r133, r143, r153⟩,
    zmms3, flags3, mem3⟩ := d3
  simp only at hrsp3 hrax3 Hm3
  subst hrsp3
  kat hk BitLUnmarshalSSZ 47
  kat hk BitLUnmarshalSSZ 48
  intro _
  kat hk BitLUnmarshalSSZ 49
  split
  case isFalse h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h; exact hrax3 (UInt64.toBitVec_inj.mp (by simpa using h))
  simp only [Effects.All]
  klabel hk hf BitLUnmarshalSSZ 58
  kat hk BitLUnmarshalSSZ 58
  kat hk BitLUnmarshalSSZ 59
  kat hk BitLUnmarshalSSZ 60
  rw [bla_pop]
  apply load_step _ _ _ _ (Int.toBytes 8 rbp.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk BitLUnmarshalSSZ 61
  rw [show rsp.toBitVec - 8 + 8#64 = rsp.toBitVec by bv_omega]
  apply load_step _ _ _ _ (Int.toBytes 8 ra.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  apply Eventually.done
  refine ⟨?_, ?_, ?_, ?_, sep_true (by ecancel)⟩
  all_goals dsimp only
  all_goals first
    | (simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, Fk.ofInt_ofBytes_toBytes64]; done)
    | exact hrax3
    | (apply UInt64.toBitVec_inj.mp; simp; done)
    | (apply UInt64.toBitVec_inj.mp; simp [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]; done)
