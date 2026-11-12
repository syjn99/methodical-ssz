import TestTarget.FixedVecDecodeLoop
import Machine.Flags
import Runtime.Contracts

/-!
# FixedVec.UnmarshalSSZ, accept path, on Kraken main

Input `buf` of 64 bytes: `rb` (32, field R) then `ws` (32, field W = 4 uint64).
-/

open Machine Runtime TestTarget TestTarget.Code
variable [Host]

theorem sep_addr_ne {a b : BitVec 64} {xs ys : List UInt8} {F : DataMem → Prop} {m : DataMem}
    (h : (Eq (xs.At a) ⋆ Eq (ys.At b) ⋆ F) m) (hx : xs ≠ []) (hy : ys ≠ []) : a ≠ b := by
  rintro rfl
  obtain ⟨_, _, _, _, ⟨m1, m2, _, hi, rfl, rfl⟩, _⟩ := h
  have h1 : a ∈ xs.At a := (_root_.mem_At_iff _ _ _).mpr ⟨0, List.length_pos_iff.mpr hx, by simp⟩
  have h2 : a ∈ ys.At a := (_root_.mem_At_iff _ _ _).mpr ⟨0, List.length_pos_iff.mpr hy, by simp⟩
  exact (Std.ExtHashMap.eq_empty_iff_forall_not_mem.mp hi a) (Std.ExtHashMap.mem_inter_iff.mpr ⟨h1, h2⟩)

theorem slot40 (x : BitVec 64) : x - 8#64 - 24 - 8#64 = x - 40 := by bv_omega
theorem slot8 (x : BitVec 64) : 24 + ({ toBitVec := x - 40 } + 8 : UInt64).toBitVec = x - 8 := by
  simp only [UInt64.toBitVec_add, UInt64.toBitVec_ofNat]; bv_omega
theorem slot40' (x : BitVec 64) : ({ toBitVec := x - 40 } + 8 : UInt64).toBitVec - 8#64 = x - 40 := by
  simp only [UInt64.toBitVec_add, UInt64.toBitVec_ofNat]; bv_omega

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 100000 in
theorem fv_accept_main (k : Nat) (hk : FixedVecUnmarshalSSZ.IsInfixAt Host.prog k)
    (hf : LabelsFresh FixedVecUnmarshalSSZ k)
    (rb ws : List UInt8) (hrb : rb.length = 32) (hws : ws.length = 8 * 4)
    (s : MachineData) (ra guard : UInt64)
    (fp s1 s2 rslot r0 r1 cP cL cC : List UInt8)
    (hfp : fp.length = 8) (h1 : s1.length = 8) (h2 : s2.length = 8) (hrs : rslot.length = 8)
    (hr0 : r0.length = 1) (hr1 : r1.length = 31)
    (hcP : cP.length = 8) (hcL : cL.length = 8) (hcC : cC.length = 8)
    (R : DataMem → Prop) (S : Nat) (scratch spm : List UInt8) (hsc : scratch.length = S) (hspm : spm.length = 24)
    (Heap : Nat → DataMem → Prop) (avail : Nat)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s1.At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 40)) ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - 40 - BitVec.ofNat 64 S))
      ⋆ Eq (spm.At (s.regs.rsp.toBitVec - 32))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Heap avail
      ⋆ Eq (rb.At s.regs.rbx.toBitVec) ⋆ Eq (ws.At (s.regs.rbx.toBitVec + 32))
      ⋆ Eq (r0.At s.regs.rax.toBitVec) ⋆ Eq (r1.At (s.regs.rax.toBitVec + 1))
      ⋆ Eq (cP.At (s.regs.rax.toBitVec + 32)) ⋆ Eq (cL.At (s.regs.rax.toBitVec + 40))
      ⋆ Eq (cC.At (s.regs.rax.toBitVec + 48))
      ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R)
    (hguard : guard.toNat < s.regs.rsp.toNat) (hsp : 40 ≤ s.regs.rsp.toNat)
    (hlen : s.regs.rcx = 64)
    (hav : 8 * 4 ≤ avail)
    (hmm : MemmoveC S)
    (hms : MakesliceC Heap (label "type__" + 49120).toBitVec 8 S) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ p : BitVec 64, (Eq (rb.At s.regs.rax.toBitVec)
          ⋆ Eq ((Int.toBytes 8 p.toInt).At (s.regs.rax.toBitVec + 32))
          ⋆ Eq ((Int.toBytes 8 4).At (s.regs.rax.toBitVec + 40))
          ⋆ Eq ((Int.toBytes 8 4).At (s.regs.rax.toBitVec + 48)) ⋆ Eq (ws.At p)
          ⋆ Eq (rb.At s.regs.rbx.toBitVec) ⋆ Eq (ws.At (s.regs.rbx.toBitVec + 32))
          ⋆ Heap (avail - 8 * 4) ⋆ R ⋆ fun _ => True) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hguard hsp hlen ⊢
  subst hlen
  have := rsp.toNat_lt_size; have := guard.toNat_lt_size; simp only [UInt64.size] at *
  have hne : rax.toBitVec ≠ rbx.toBitVec := by
    have : (Eq (r0.At rax.toBitVec) ⋆ Eq (rb.At rbx.toBitVec) ⋆ fun _ => True) mem := sep_true (by ecancel)
    exact sep_addr_ne this (by intro h; simp [h] at hr0) (by intro h; simp [h] at hrb)
  kat hk FixedVecUnmarshalSSZ 0
  kat hk FixedVecUnmarshalSSZ 1
  kat hk FixedVecUnmarshalSSZ 2
  apply load_step _ _ _ _ (Int.toBytes 8 guard.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk FixedVecUnmarshalSSZ 3
  split
  · rename_i h; exfalso
    simp [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, CondCode.interp, StatusFlags.from_result, BitVec.unsigned] at h
    rcases h with h | h
    · apply h; omega
    · have := congrArg BitVec.toNat h; simp [BitVec.toNat_sub] at this; omega
  simp only [Effects.All]
  kat hk FixedVecUnmarshalSSZ 4
  apply store_step_at _ _ (rsp.toBitVec - 8) _ _ _ fp _ _ (by bv_omega) (by ecancel) (by exact hfp)
  intro m1 H1
  simp only [Width.bytes, Width.bits] at H1
  kunfold
  kat hk FixedVecUnmarshalSSZ 5
  kat hk FixedVecUnmarshalSSZ 6
  kat hk FixedVecUnmarshalSSZ 7
  apply store_step_at _ _ (rsp.toBitVec + 16) _ _ _ s2 _ _ (by bv_omega) (by ecancel) (by exact h2)
  intro m2 H2
  simp only [Width.bytes, Width.bits] at H2
  kunfold
  kat hk FixedVecUnmarshalSSZ 8
  kat hk FixedVecUnmarshalSSZ 9
  split
  case isTrue h => exact absurd h (by decide)
  simp only [Effects.All]
  kat hk FixedVecUnmarshalSSZ 10
  apply store_step_at _ _ (rsp.toBitVec + 8) _ _ _ s1 _ _ (by bv_omega) (by ecancel) (by exact h1)
  intro m3 H3
  simp only [Width.bytes, Width.bits] at H3
  kunfold
  kat hk FixedVecUnmarshalSSZ 11
  apply store_step_at _ _ (rsp.toBitVec + 16) _ _ _ (Int.toBytes 8 rbx.toBitVec.toInt) _ _ (by bv_omega) (by ecancel) (by exact Int.toBytes_length 8 _)
  intro m4 H4
  simp only [Width.bytes, Width.bits] at H4
  kunfold
  kat hk FixedVecUnmarshalSSZ 12
  apply load_step _ _ _ _ r0 _ _ (by ecancel) (by exact hr0)
  kunfold
  intro _
  kat hk FixedVecUnmarshalSSZ 13
  kat hk FixedVecUnmarshalSSZ 14
  split
  case isTrue h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
    have := rax.toNat_lt_size; have := rbx.toNat_lt_size; simp only [UInt64.size] at *
    apply hne; apply BitVec.eq_of_toNat_eq
    have := congrArg BitVec.toNat h; simp [BitVec.toNat_sub, UInt64.toNat_toBitVec] at this ⊢; omega
  simp only [Effects.All]
  kat hk FixedVecUnmarshalSSZ 15
  kat hk FixedVecUnmarshalSSZ 16
  apply store_step_at _ _ (rsp.toBitVec - 40) _ _ _ rslot _ _ (slot40 _) (by ecancel) (by exact hrs)
  intro m5 H5
  simp only [Width.bytes, Width.bits] at H5
  kunfold
  have hmerge : Eq ((r0 ++ r1).At rax.toBitVec) = Eq (r0.At rax.toBitVec) ⋆ Eq (r1.At (rax.toBitVec + 1)) := by
    rw [Mem.At_append_sep _ _ _ (by simp [hr0, hr1]), hr0]; rfl
  have hsl : rsp.toBitVec - 8#64 - 24 - 8#64 = rsp.toBitVec - 40 := by kaddr
  rw [hsl] at *
  refine eventually_trans _ _ _ _ (hmm _ (Host.addrOf (k + 16 + 1)) rb (r0 ++ r1) scratch _
    (by rw [hrb]; rfl) (by simp [hrb, hr0, hr1]) hsc (by dsimp only; rw [hmerge]; ecancel)) ?_
  rintro ⟨d1, pc1⟩ ⟨hpc1, hrsp1, _hmr141, _hmrbp1, stk1, hstk1, Hm1⟩
  dsimp only at hpc1 hrsp1 Hm1
  subst hpc1
  obtain ⟨⟨rax1, rbx1, rcx1, rdx1, rsi1, rdi1, rsp1, rbp1, r81, r91, r101, r111, r121, r131, r141, r151⟩,
    zmms1, flags1, mem1⟩ := d1
  simp only at hrsp1 _hmr141 Hm1
  subst hrsp1 _hmr141
  kat hk FixedVecUnmarshalSSZ 17
  kat hk FixedVecUnmarshalSSZ 18
  kat hk FixedVecUnmarshalSSZ 19
  kat hk FixedVecUnmarshalSSZ 20
  kat hk FixedVecUnmarshalSSZ 21
  apply store_step_at _ _ (rsp.toBitVec - 40) _ _ _ (Int.toBytes 8 (Host.addrOf (k + 16 + 1)).toBitVec.toInt) _ _
    (slot40' _) (by ecancel) (by exact Int.toBytes_length 8 _)
  intro m6 H6
  simp only [Width.bytes, Width.bits] at H6
  kunfold
  rw [slot40'] at *
  refine eventually_trans _ _ _ _ (hms _ (Host.addrOf (k + 21 + 1)) 4 avail stk1 spm _ rfl (Nat.le_of_eq rfl) (by rfl) hav (by unfold maxAlloc; omega)
    (by omega) hstk1 hspm (by dsimp only; rw [show rsp.toBitVec - 40 + 8 = rsp.toBitVec - 32 by bv_omega]; ecancel)) ?_
  rintro ⟨d2, pc2⟩ ⟨hpc2, hrsp2, hr14c2, -, stk2, spm2, hstk2, hspm2, Hm2⟩
  dsimp only at hpc2 hrsp2 Hm2
  subst hpc2
  obtain ⟨⟨rax2, rbx2, rcx2, rdx2, rsi2, rdi2, rsp2, rbp2, r82, r92, r102, r112, r122, r132, r142, r152⟩,
    zmms2, flags2, mem2⟩ := d2
  simp only at hrsp2 hr14c2 Hm2
  subst hrsp2 hr14c2
  kat hk FixedVecUnmarshalSSZ 22
  apply load_step_at _ _ (rsp.toBitVec + 8) _ _ (Int.toBytes 8 rax.toBitVec.toInt) _ _ (by kaddr) (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk FixedVecUnmarshalSSZ 23
  apply store_step_at _ _ (rax.toBitVec + 40) _ _ _ cL _ _ (by kaddr) (by ecancel) (by exact hcL)
  intro m7 H7
  simp only [Width.bytes, Width.bits] at H7
  kunfold
  kat hk FixedVecUnmarshalSSZ 24
  apply store_step_at _ _ (rax.toBitVec + 48) _ _ _ cC _ _ (by kaddr) (by ecancel) (by exact hcC)
  intro m8 H8
  simp only [Width.bytes, Width.bits] at H8
  kunfold
  kat hk FixedVecUnmarshalSSZ 25
  apply load_step _ _ _ _ [0, 0, 0, 0] _ _ (by ecancel) (by simp)
  simp only [show Int.ofBytes [0, 0, 0, 0] = 0 by simp [Int.ofBytes]]
  kunfold
  kat hk FixedVecUnmarshalSSZ 26
  split
  case isFalse h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
  simp only [Effects.All]
  klabel hk hf FixedVecUnmarshalSSZ 31
  kat hk FixedVecUnmarshalSSZ 31
  kat hk FixedVecUnmarshalSSZ 32
  apply store_step_at _ _ (rax.toBitVec + 32) _ _ _ cP _ _ (by kaddr) (by ecancel) (by exact hcP)
  intro m9 H9
  simp only [Width.bytes, Width.bits] at H9
  kunfold
  kat hk FixedVecUnmarshalSSZ 33
  apply load_step_at _ _ (rsp.toBitVec + 16) _ _ (Int.toBytes 8 rbx.toBitVec.toInt) _ _ (by kaddr) (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk FixedVecUnmarshalSSZ 34
  intro _
  kat hk FixedVecUnmarshalSSZ 35
  klabel hk hf FixedVecUnmarshalSSZ 46
  simp only [show Int.toBytes 8 (BitVec.toInt (4 : BitVec 64)) = Int.toBytes 8 4 by decide] at H9
  refine eventually_trans _ _ _ _ (fv_loop k hk hf ws hws rbx.toBitVec rax.toBitVec rax2.toBitVec _ _ _ _ 4 0 _
    (by omega) (by simp) rfl rfl rfl rfl rfl
    (by simp only [Nat.mul_zero, List.take_zero, List.nil_append, Nat.sub_zero]; ecancel)) ?_
  rintro ⟨d3, pc3⟩ ⟨hpc3, hrsp3, hrbp3, hr14c3, Hm3⟩
  dsimp only at hpc3 hrsp3 hrbp3 hr14c3 Hm3
  subst hpc3
  obtain ⟨⟨rax3, rbx3, rcx3, rdx3, rsi3, rdi3, rsp3, rbp3, r83, r93, r103, r113, r123, r133, r143, r153⟩,
    zmms3, flags3, mem3⟩ := d3
  simp only at hrsp3 hrbp3 hr14c3 Hm3
  subst hrsp3 hrbp3 hr14c3
  kat hk FixedVecUnmarshalSSZ 63
  kat hk FixedVecUnmarshalSSZ 64
  intro _
  kat hk FixedVecUnmarshalSSZ 65
  intro _
  kat hk FixedVecUnmarshalSSZ 66
  kat hk FixedVecUnmarshalSSZ 67
  rw [slot8]
  apply load_step _ _ _ _ (Int.toBytes 8 rbp.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk FixedVecUnmarshalSSZ 68
  kat hk FixedVecUnmarshalSSZ 69
  rw [show rsp.toBitVec - 8 + 8#64 = rsp.toBitVec by bv_omega]
  apply load_step _ _ _ _ (Int.toBytes 8 ra.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  apply Eventually.done
  simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  refine ⟨trivial, ?_, ?_, ?_, ?_, ?_, rax2.toBitVec, ?_⟩
  all_goals first
    | trivial | rfl
    | (apply UInt64.toBitVec_inj.mp; simp; done)
    | (apply UInt64.toBitVec_inj.mp; simp; bv_omega)
    | exact sep_true (by ecancel)
