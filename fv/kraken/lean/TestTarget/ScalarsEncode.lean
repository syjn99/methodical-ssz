import Machine.Bytes
import Machine.Labels
import TestTarget.Code

/-!
# Scalars.MarshalSSZTo, fast path, on Kraken main (6064eec)

When `dst` has room (`len + 16 ≤ cap`), the function appends the 16 receiver
bytes to `dst` and returns `(ptr, len + 16, cap, nil)`. No `growslice` call is
taken. Go ABIInternal amd64: rax = c, (rbx, rcx, rdi) = dst, r14 = g (kept:
the result names it).
-/

open Machine TestTarget TestTarget.Code
variable [Host]

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem sc_marshal_main (k : Nat) (hk : ScalarsMarshalSSZTo.IsInfixAt Host.prog k)
    (hf : LabelsFresh ScalarsMarshalSSZTo k)
    (s : MachineData) (ra guard : UInt64) (fp sp1 sp2 cA cB cC cD cE d0 d1 d2 d3 d4 pre : List UInt8)
    (hfp : fp.length = 8) (hs1 : sp1.length = 8) (hs2 : sp2.length = 8)
    (hA : cA.length = 1) (hB : cB.length = 2) (hC : cC.length = 4) (hD : cD.length = 8)
    (hd0 : d0.length = 1) (hd1 : d1.length = 2) (hd2 : d2.length = 4) (hd3 : d3.length = 8) (hd4 : d4.length = 1)
    (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (sp1.At (s.regs.rsp.toBitVec + 8)) ⋆ Eq (sp2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq (cA.At s.regs.rax.toBitVec) ⋆ Eq (cB.At (s.regs.rax.toBitVec + 2))
      ⋆ Eq (cC.At (s.regs.rax.toBitVec + 4)) ⋆ Eq (cD.At (s.regs.rax.toBitVec + 8))
      ⋆ Eq (cE.At (s.regs.rax.toBitVec + 16))
      ⋆ Eq (d0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec)) ⋆ Eq (d1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 1))
      ⋆ Eq (d2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 3)) ⋆ Eq (d3.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 7))
      ⋆ Eq (d4.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 15))
      ⋆ Eq (pre.At s.regs.rbx.toBitVec) ⋆ R)
    (hguard : guard.toNat < s.regs.rsp.toNat)
    (hcap : s.regs.rcx.toNat + 16 ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63)
    (hE : cE = [0] ∨ cE = [1]) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = s.regs.rbx
        ∧ st.data.regs.rbx = s.regs.rcx + 16 ∧ st.data.regs.rcx = s.regs.rdi
        ∧ st.data.regs.rdi = 0 ∧ st.data.regs.rsi = 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14
        ∧ (Eq (cA.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (cB.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 1))
          ⋆ Eq (cC.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 3))
          ⋆ Eq (cD.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 7))
          ⋆ Eq (cE.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 15))
          ⋆ Eq (pre.At s.regs.rbx.toBitVec)
          ⋆ Eq (cA.At s.regs.rax.toBitVec) ⋆ Eq (cB.At (s.regs.rax.toBitVec + 2))
          ⋆ Eq (cC.At (s.regs.rax.toBitVec + 4)) ⋆ Eq (cD.At (s.regs.rax.toBitVec + 8))
          ⋆ Eq (cE.At (s.regs.rax.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16)) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hguard hcap hcap63 ⊢
  have := rcx.toNat_lt_size; have := rdi.toNat_lt_size; have := rsp.toNat_lt_size
  have := guard.toNat_lt_size; simp only [UInt64.size] at *
  kat hk ScalarsMarshalSSZTo 0
  kat hk ScalarsMarshalSSZTo 1
  -- 2: cmp 0x10(%r14),%rsp
  kat hk ScalarsMarshalSSZTo 2
  apply load_step _ _ _ _ (Int.toBytes 8 guard.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  -- 3: jbe (not taken)
  kat hk ScalarsMarshalSSZTo 3
  split
  · rename_i h; exfalso
    simp [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, CondCode.interp, StatusFlags.from_result, BitVec.unsigned] at h
    have := guard.toNat_lt_size; have := rsp.toNat_lt_size
    simp only [UInt64.size] at *
    rcases h with h | h
    · apply h; omega
    · have := congrArg BitVec.toNat h; simp [BitVec.toNat_sub] at this; omega
  simp only [Effects.All]
  -- 4: push %rbp
  kat hk ScalarsMarshalSSZTo 4
  apply store_step_at _ _ (rsp.toBitVec - 8) _ _ _ fp _ _ (by bv_omega) (by ecancel) (by exact hfp)
  intro m1 H1
  simp only [Width.bytes, Width.bits] at H1
  kunfold
  -- 5: mov %rsp,%rbp ; 6: sub $0x50,%rsp
  kat hk ScalarsMarshalSSZTo 5
  kat hk ScalarsMarshalSSZTo 6
  -- 7: mov %rbx,0x68(%rsp) ; 8: mov %rax,0x60(%rsp)
  kat hk ScalarsMarshalSSZTo 7
  apply store_step_at _ _ (rsp.toBitVec + 16) _ _ _ sp2 _ _ (by bv_omega) (by ecancel) (by exact hs2)
  intro m2 H2
  simp only [Width.bytes, Width.bits] at H2
  kunfold
  kat hk ScalarsMarshalSSZTo 8
  apply store_step_at _ _ (rsp.toBitVec + 8) _ _ _ sp1 _ _ (by bv_omega) (by ecancel) (by exact hs1)
  intro m3 H3
  simp only [Width.bytes, Width.bits] at H3
  kunfold
  -- 9: lea 0x1(%rcx),%rdx ; 10: movzbl (%rax),%r8d
  kat hk ScalarsMarshalSSZTo 9
  kat hk ScalarsMarshalSSZTo 10
  apply load_step_at _ _ (rax.toBitVec) _ _ cA _ _ (by bv_omega) (by ecancel) (by exact hA)
  kunfold
  -- 11: cmp %rdx,%rdi ; 12: jae (taken)
  kat hk ScalarsMarshalSSZTo 11
  kat hk ScalarsMarshalSSZTo 12
  split
  case isFalse h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned] at h; omega
  simp only [Effects.All]
  klabel hk hf ScalarsMarshalSSZTo 25
  kat hk ScalarsMarshalSSZTo 25
  kat hk ScalarsMarshalSSZTo 26
  rw [show rcx.toBitVec + 1 + rbx.toBitVec * 1#64 + -1 = rbx.toBitVec + rcx.toBitVec by bv_omega]
  apply store_step _ _ _ _ _ d0 _ _ (by ecancel) (by exact hd0)
  intro m4 H4
  simp only [Width.bytes, Width.bits] at H4
  kunfold
  kat hk ScalarsMarshalSSZTo 27
  kat hk ScalarsMarshalSSZTo 28
  apply load_step_at _ _ (rax.toBitVec + 2) _ _ cB _ _ (by bv_omega) (by ecancel) (by exact hB)
  kunfold
  kat hk ScalarsMarshalSSZTo 29
  kat hk ScalarsMarshalSSZTo 30
  split
  case isFalse h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned] at h; omega
  simp only [Effects.All]
  klabel hk hf ScalarsMarshalSSZTo 43
  kat hk ScalarsMarshalSSZTo 43
  kat hk ScalarsMarshalSSZTo 44
  rw [show 2 + (rcx.toBitVec + 1) + rbx.toBitVec * 1#64 + -2 = rbx.toBitVec + rcx.toBitVec + 1 by bv_omega]
  apply store_step _ _ _ _ _ d1 _ _ (by ecancel) (by exact hd1)
  intro m5 H5
  simp only [Width.bytes, Width.bits] at H5
  kunfold
  kat hk ScalarsMarshalSSZTo 45
  kat hk ScalarsMarshalSSZTo 46
  apply load_step_at _ _ (rax.toBitVec + 4) _ _ cC _ _ (by bv_omega) (by ecancel) (by exact hC)
  kunfold
  kat hk ScalarsMarshalSSZTo 47
  kat hk ScalarsMarshalSSZTo 48
  split
  case isFalse h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned] at h; omega
  simp only [Effects.All]
  klabel hk hf ScalarsMarshalSSZTo 61
  kat hk ScalarsMarshalSSZTo 61
  kat hk ScalarsMarshalSSZTo 62
  rw [show 4 + (2 + (rcx.toBitVec + 1)) + rbx.toBitVec * 1#64 + -4 = rbx.toBitVec + rcx.toBitVec + 3 by bv_omega]
  apply store_step _ _ _ _ _ d2 _ _ (by ecancel) (by exact hd2)
  intro m6 H6
  simp only [Width.bytes, Width.bits] at H6
  kunfold
  kat hk ScalarsMarshalSSZTo 63
  kat hk ScalarsMarshalSSZTo 64
  apply load_step_at _ _ (rax.toBitVec + 8) _ _ cD _ _ (by bv_omega) (by ecancel) (by exact hD)
  kunfold
  kat hk ScalarsMarshalSSZTo 65
  kat hk ScalarsMarshalSSZTo 66
  split
  case isFalse h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned] at h; omega
  simp only [Effects.All]
  klabel hk hf ScalarsMarshalSSZTo 79
  kat hk ScalarsMarshalSSZTo 79
  kat hk ScalarsMarshalSSZTo 80
  rw [show 8 + (4 + (2 + (rcx.toBitVec + 1))) + rbx.toBitVec * 1#64 + -8 = rbx.toBitVec + rcx.toBitVec + 7 by bv_omega]
  apply store_step _ _ _ _ _ d3 _ _ (by ecancel) (by exact hd3)
  intro m7 H7
  simp only [Width.bytes, Width.bits] at H7
  kunfold
  kat hk ScalarsMarshalSSZTo 81
  apply load_step_at _ _ (rax.toBitVec + 16) _ _ cE _ _ (by bv_omega) (by ecancel) (by rcases hE with rfl | rfl <;> rfl)
  kunfold
  rcases hE with rfl | rfl
  · -- E = false
      kat hk ScalarsMarshalSSZTo 82
      split
      case isFalse h => exact absurd h (by decide)
      simp only [Effects.All]
      klabel hk hf ScalarsMarshalSSZTo 98
      kat hk ScalarsMarshalSSZTo 98
      kat hk ScalarsMarshalSSZTo 99
      kat hk ScalarsMarshalSSZTo 100
      kat hk ScalarsMarshalSSZTo 101
      split
      case isFalse h =>
        exfalso; simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned] at h; omega
      simp only [Effects.All]
      klabel hk hf ScalarsMarshalSSZTo 111
      kat hk ScalarsMarshalSSZTo 111
      kat hk ScalarsMarshalSSZTo 112
      rw [show 8 + (4 + (2 + (rcx.toBitVec + 1))) + 1 + rbx.toBitVec * 1#64 + -1 = rbx.toBitVec + rcx.toBitVec + 15 by bv_omega]
      apply store_step _ _ _ _ _ d4 _ _ (by ecancel) (by exact hd4)
      intro m8 H8
      simp only [Width.bytes, Width.bits] at H8
      kunfold
      kat hk ScalarsMarshalSSZTo 113
      kat hk ScalarsMarshalSSZTo 114
      kat hk ScalarsMarshalSSZTo 115
      kat hk ScalarsMarshalSSZTo 116
      kat hk ScalarsMarshalSSZTo 117
      intro _
      kat hk ScalarsMarshalSSZTo 118
      intro _
      kat hk ScalarsMarshalSSZTo 119
      kat hk ScalarsMarshalSSZTo 120
      rw [show 80 + (rsp.toBitVec - 8#64 - 80) = rsp.toBitVec - 8 by bv_omega]
      obtain ⟨F9, H9⟩ : ∃ F, (Eq ((Int.toBytes 8 rbp.toBitVec.toInt).At (rsp.toBitVec - 8)) ⋆ F) m8 := ⟨_, by ecancel⟩
      apply load_step _ _ _ _ _ F9 _ H9 (by exact Int.toBytes_length 8 _)
      kunfold
      kat hk ScalarsMarshalSSZTo 121
      rw [show rsp.toBitVec - 8 + 8#64 = rsp.toBitVec by bv_omega]
      apply load_step _ _ _ _ (Int.toBytes 8 ra.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
      kunfold
      apply Eventually.done
      simp only [Width.bytes, zx8, zx16, zx32, toBytes_ofInt_ofBytes 8 1 rfl cA hA,
        toBytes_ofInt_ofBytes 16 2 rfl cB hB, toBytes_ofInt_ofBytes 32 4 rfl cC hC,
        toBytes_ofInt_ofBytes 64 8 rfl cD hD,
        show Int.toBytes 1 (BitVec.truncate 8 (0 : BitVec 64)).toInt = [0] by decide,
        show Int.toBytes 1 (BitVec.truncate 8 (1 : BitVec 64)).toInt = [1] by decide] at H8
      simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
      refine ⟨trivial, trivial, ?_, trivial, ?_, ?_, ?_, trivial, trivial, ?_⟩
      · apply UInt64.toBitVec_inj.mp; simp; generalize rcx.toBitVec = x; apply BitVec.eq_of_toNat_eq; simp; omega
      · apply UInt64.toBitVec_inj.mp; simp
      · apply UInt64.toBitVec_inj.mp; simp
      · apply UInt64.toBitVec_inj.mp; simp
      · (try simp only [BitVec.ofNat_eq_ofNat] at H8 ⊢); ecancel

  · -- E = true
      kat hk ScalarsMarshalSSZTo 82
      split
      case isTrue h => exact absurd h (by decide)
      simp only [Effects.All]
      kat hk ScalarsMarshalSSZTo 83
      kat hk ScalarsMarshalSSZTo 84
      kat hk ScalarsMarshalSSZTo 85
      split
      case isFalse h =>
        exfalso; simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned] at h; omega
      simp only [Effects.All]
      klabel hk hf ScalarsMarshalSSZTo 95
      kat hk ScalarsMarshalSSZTo 95
      kat hk ScalarsMarshalSSZTo 96
      rw [show 8 + (4 + (2 + (rcx.toBitVec + 1))) + 1 + rbx.toBitVec * 1#64 + -1 = rbx.toBitVec + rcx.toBitVec + 15 by bv_omega]
      apply store_step _ _ _ _ _ d4 _ _ (by ecancel) (by exact hd4)
      intro m8 H8
      simp only [Width.bytes, Width.bits] at H8
      kunfold
      kat hk ScalarsMarshalSSZTo 97
      klabel hk hf ScalarsMarshalSSZTo 113
      kat hk ScalarsMarshalSSZTo 113
      kat hk ScalarsMarshalSSZTo 114
      kat hk ScalarsMarshalSSZTo 115
      kat hk ScalarsMarshalSSZTo 116
      kat hk ScalarsMarshalSSZTo 117
      intro _
      kat hk ScalarsMarshalSSZTo 118
      intro _
      kat hk ScalarsMarshalSSZTo 119
      kat hk ScalarsMarshalSSZTo 120
      rw [show 80 + (rsp.toBitVec - 8#64 - 80) = rsp.toBitVec - 8 by bv_omega]
      obtain ⟨F9, H9⟩ : ∃ F, (Eq ((Int.toBytes 8 rbp.toBitVec.toInt).At (rsp.toBitVec - 8)) ⋆ F) m8 := ⟨_, by ecancel⟩
      apply load_step _ _ _ _ _ F9 _ H9 (by exact Int.toBytes_length 8 _)
      kunfold
      kat hk ScalarsMarshalSSZTo 121
      rw [show rsp.toBitVec - 8 + 8#64 = rsp.toBitVec by bv_omega]
      apply load_step _ _ _ _ (Int.toBytes 8 ra.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
      kunfold
      apply Eventually.done
      simp only [Width.bytes, zx8, zx16, zx32, toBytes_ofInt_ofBytes 8 1 rfl cA hA,
        toBytes_ofInt_ofBytes 16 2 rfl cB hB, toBytes_ofInt_ofBytes 32 4 rfl cC hC,
        toBytes_ofInt_ofBytes 64 8 rfl cD hD,
        show Int.toBytes 1 (BitVec.truncate 8 (0 : BitVec 64)).toInt = [0] by decide,
        show Int.toBytes 1 (BitVec.truncate 8 (1 : BitVec 64)).toInt = [1] by decide] at H8
      simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
      refine ⟨trivial, trivial, ?_, trivial, ?_, ?_, ?_, trivial, trivial, ?_⟩
      · apply UInt64.toBitVec_inj.mp; simp; generalize rcx.toBitVec = x; apply BitVec.eq_of_toNat_eq; simp; omega
      · apply UInt64.toBitVec_inj.mp; simp
      · apply UInt64.toBitVec_inj.mp; simp
      · apply UInt64.toBitVec_inj.mp; simp
      · (try simp only [BitVec.ofNat_eq_ofNat] at H8 ⊢); ecancel
