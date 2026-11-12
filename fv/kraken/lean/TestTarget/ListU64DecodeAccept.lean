import TestTarget.ListU64DecodeLoop
import Machine.Flags
import Runtime.Contracts

/-!
# ListU64.UnmarshalSSZ, accept path, on Kraken main (6064eec)

Input `buf = [4,0,0,0] ++ bs` with `bs` of 8n bytes, n ≤ 16.
-/

open Machine Runtime TestTarget TestTarget.Code
variable [Host]

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 100000 in
theorem lu_accept_main (k : Nat) (hk : ListU64UnmarshalSSZ.IsInfixAt Host.prog k)
    (hf : LabelsFresh ListU64UnmarshalSSZ k)
    (bs : List UInt8) (n : Nat) (hbs : bs.length = 8 * n) (hn : n ≤ 16)
    (s : MachineData) (ra guard : UInt64)
    (fp s28 s30 s38 s90 s98 rslot cP cL cC : List UInt8)
    (hfp : fp.length = 8) (h28 : s28.length = 8) (h30 : s30.length = 8) (h38 : s38.length = 8)
    (h90 : s90.length = 8) (h98 : s98.length = 8) (hrs : rslot.length = 8)
    (hcP : cP.length = 8) (hcL : cL.length = 8) (hcC : cC.length = 8)
    (R : DataMem → Prop) (S : Nat) (scratch spm : List UInt8) (hsc : scratch.length = S) (hspm : spm.length = 24)
    (Heap : Nat → DataMem → Prop) (avail : Nat)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (spm.At (s.regs.rsp.toBitVec - 136))
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s28.At (s.regs.rsp.toBitVec - 96))
      ⋆ Eq (s30.At (s.regs.rsp.toBitVec - 88)) ⋆ Eq (s38.At (s.regs.rsp.toBitVec - 80))
      ⋆ Eq (s90.At (s.regs.rsp.toBitVec + 8)) ⋆ Eq (s98.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 144)) ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - 144 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Heap avail
      ⋆ Eq ([4, 0, 0, 0].At s.regs.rbx.toBitVec)
      ⋆ (Eq (bs.At (s.regs.rbx.toBitVec + 4))
        ⋆ Eq (cP.At s.regs.rax.toBitVec) ⋆ Eq (cL.At (s.regs.rax.toBitVec + 8)) ⋆ Eq (cC.At (s.regs.rax.toBitVec + 16))
        ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R))
    (hguard : guard.toNat < s.regs.rsp.toNat - 8) (hsp : 8 ≤ s.regs.rsp.toNat)
    (hlen : s.regs.rcx.toNat = 4 + 8 * n) (hcap : s.regs.rcx.toNat ≤ s.regs.rdi.toNat)
    (hcap63 : s.regs.rdi.toNat < 2 ^ 63)
    -- Contract of runtime.makeslice (Runtime/Contracts.lean): uint64 elements (8 bytes),
    -- type descriptor at type:*+48128 (link/out/RESULT), heap with avail ≥ 8n bytes.
    (hav : 8 * n ≤ avail)
    (hms : MakesliceC Heap (label "type__" + 49120).toBitVec 8 S) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0 ∧
        st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ (p : BitVec 64) (fp' s28' s30' s38' s90' s98' rslot' scratch' spm' : List UInt8),
        fp'.length = 8 ∧ s28'.length = 8 ∧ s30'.length = 8 ∧ s38'.length = 8 ∧ s90'.length = 8 ∧
        s98'.length = 8 ∧ rslot'.length = 8 ∧ scratch'.length = S ∧ spm'.length = 24 ∧
        (Eq ((Int.toBytes 8 p.toInt).At s.regs.rax.toBitVec)
          ⋆ Eq ((Int.toBytes 8 (n : Int)).At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 (n : Int)).At (s.regs.rax.toBitVec + 16)) ⋆ Eq (bs.At p)
          ⋆ Heap (avail - 8 * n)
          ⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec) ⋆ Eq (spm'.At (s.regs.rsp.toBitVec - 136))
          ⋆ Eq (fp'.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s28'.At (s.regs.rsp.toBitVec - 96))
          ⋆ Eq (s30'.At (s.regs.rsp.toBitVec - 88)) ⋆ Eq (s38'.At (s.regs.rsp.toBitVec - 80))
          ⋆ Eq (s90'.At (s.regs.rsp.toBitVec + 8)) ⋆ Eq (s98'.At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq (rslot'.At (s.regs.rsp.toBitVec - 144)) ⋆ Eq (scratch'.At (s.regs.rsp.toBitVec - 144 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq ([4, 0, 0, 0].At s.regs.rbx.toBitVec) ⋆ Eq (bs.At (s.regs.rbx.toBitVec + 4))
          ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hguard hsp hlen hcap hcap63 ⊢
  have := rcx.toNat_lt_size; have := rdi.toNat_lt_size; have := rsp.toNat_lt_size
  have := guard.toNat_lt_size; simp only [UInt64.size] at *
  -- chunks used only after the call, as one atom for `ecancel`
  generalize hQ : (Eq (bs.At (rbx.toBitVec + 4))
        ⋆ Eq (cP.At rax.toBitVec) ⋆ Eq (cL.At (rax.toBitVec + 8)) ⋆ Eq (cC.At (rax.toBitVec + 16))
        ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R) = Q at h_mem
  kat hk ListU64UnmarshalSSZ 0
  kat hk ListU64UnmarshalSSZ 1
  -- 2: lea -0x8(%rsp),%r12 ; 3: cmp 0x10(%r14),%r12 ; 4: jbe (not taken)
  kat hk ListU64UnmarshalSSZ 2
  kat hk ListU64UnmarshalSSZ 3
  apply load_step _ _ _ _ (Int.toBytes 8 guard.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk ListU64UnmarshalSSZ 4
  split
  case isTrue h =>
    exfalso
    rw [cmp_be_false _ _ _ _ (by rw [toNat_add_neg8 _ (by simpa using hsp)]; simpa using hguard)] at h
    exact absurd h (by simp)
  simp only [Effects.All]
  kat hk ListU64UnmarshalSSZ 5
  apply store_step_at _ _ (rsp.toBitVec - 8) _ _ _ fp _ _ (by kaddr) (by ecancel) (by exact hfp)
  intro m1 H1
  simp only [Width.bytes, Width.bits] at H1
  kunfold
  kat hk ListU64UnmarshalSSZ 6
  kat hk ListU64UnmarshalSSZ 7
  kat hk ListU64UnmarshalSSZ 8
  apply store_step_at _ _ (rsp.toBitVec + 16) _ _ _ s98 _ _ (by kaddr) (by ecancel) (by exact h98)
  intro m2 H2
  simp only [Width.bytes, Width.bits] at H2
  kunfold
  kat hk ListU64UnmarshalSSZ 9
  kat hk ListU64UnmarshalSSZ 10
  kat hk ListU64UnmarshalSSZ 11
  split
  case isTrue h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned] at h; omega
  simp only [Effects.All]
  kat hk ListU64UnmarshalSSZ 12
  apply load_step_at _ _ rbx.toBitVec _ _ [4, 0, 0, 0] _ _ (by bv_omega) (by ecancel) (by simp)
  simp only [show Int.ofBytes [4, 0, 0, 0] = 4 by simp [Int.ofBytes]]
  kunfold
  kat hk ListU64UnmarshalSSZ 13
  kat hk ListU64UnmarshalSSZ 14
  kat hk ListU64UnmarshalSSZ 15
  kat hk ListU64UnmarshalSSZ 16
  split
  case isTrue h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
  simp only [Effects.All]
  kat hk ListU64UnmarshalSSZ 17
  kat hk ListU64UnmarshalSSZ 18
  kat hk ListU64UnmarshalSSZ 19
  kat hk ListU64UnmarshalSSZ 20
  kshl64 63
  kat hk ListU64UnmarshalSSZ 21
  intro _
  kat hk ListU64UnmarshalSSZ 22
  kat hk ListU64UnmarshalSSZ 23
  kat hk ListU64UnmarshalSSZ 24
  intro _
  kat hk ListU64UnmarshalSSZ 25
  split
  case isTrue h =>
    exfalso; rw [and7_zero rcx.toBitVec n hn (by simpa using hlen)] at h
    simp [CondCode.interp, StatusFlags.from_result] at h
  simp only [Effects.All]
  kat hk ListU64UnmarshalSSZ 26
  kshl64 3
  kat hk ListU64UnmarshalSSZ 27
  kat hk ListU64UnmarshalSSZ 28
  split
  case isTrue h =>
    exfalso; rw [jg16_false _ _ (by rw [shr3_toNat rcx.toBitVec n hn (by simpa using hlen)]; omega)] at h
    simp at h
  simp only [Effects.All]
  -- computed values as atoms (ecancel's atom matching unfolds them otherwise)
  generalize hdV : rbx.toBitVec + BitVec.zeroExtend 64
      (BitVec.extractLsb' 0 32 (BitVec.sshiftRight (-(rdi.toBitVec + -4)) 63) &&& BitVec.truncate 32 4) = dV
  generalize hnV : BitVec.ushiftRight (-4 + rcx.toBitVec) 3 = nV
  generalize hcV : rdi.toBitVec + -4 = cV
  kat hk ListU64UnmarshalSSZ 29
  apply store_step_at _ _ (rsp.toBitVec + 8) _ _ _ s90 _ _ (by kaddr) (by ecancel) (by exact h90)
  intro m3 H3
  simp only [Width.bytes, Width.bits] at H3
  kunfold
  kat hk ListU64UnmarshalSSZ 30
  apply store_step_at _ _ (rsp.toBitVec - 88) _ _ _ s30 _ _ (by kaddr) (by ecancel) (by exact h30)
  intro m4 H4
  simp only [Width.bytes, Width.bits] at H4
  kunfold
  kat hk ListU64UnmarshalSSZ 31
  apply store_step_at _ _ (rsp.toBitVec - 80) _ _ _ s38 _ _ (by kaddr) (by ecancel) (by exact h38)
  intro m5 H5
  simp only [Width.bytes, Width.bits] at H5
  kunfold
  kat hk ListU64UnmarshalSSZ 32
  apply store_step_at _ _ (rsp.toBitVec - 96) _ _ _ s28 _ _ (by kaddr) (by ecancel) (by exact h28)
  intro m6 H6
  simp only [Width.bytes, Width.bits] at H6
  kunfold
  kat hk ListU64UnmarshalSSZ 33
  kat hk ListU64UnmarshalSSZ 34
  kat hk ListU64UnmarshalSSZ 35
  apply store_step_at _ _ (rsp.toBitVec - 144) _ _ _ rslot _ _ (call_slot _) (by ecancel) (by exact hrs)
  intro m7 H7
  simp only [Width.bytes, Width.bits] at H7
  kunfold
  -- the call: apply the makeslice contract, continue at the return address
  rw [call_slot] at *
  have hnN : nV.toNat = n := by rw [← hnV]; exact shr3_toNat rcx.toBitVec n hn (by simpa using hlen)
  have hspA : rsp.toBitVec - 144 + 8 = rsp.toBitVec - 136 := by bv_omega
  refine eventually_trans _ _ _ _ (hms _ (Host.addrOf (k + 35 + 1)) n avail scratch spm _ rfl (Nat.le_of_eq hnN) hnN hav
    (by unfold maxAlloc; omega) (by omega) hsc hspm (by dsimp only; rw [hspA]; ecancel)) ?_
  rintro ⟨d1, pc1⟩ ⟨hpc1, hrsp1, hr141, -, stk1, spm1, hstk1, hspm1, Hm1⟩
  dsimp only at hpc1 hrsp1 hr141 Hm1
  subst hpc1
  obtain ⟨⟨rax1, rbx1, rcx1, rdx1, rsi1, rdi1, rsp1, rbp1, r81, r91, r101, r111, r121, r131, r141, r151⟩,
    zmms1, flags1, mem1⟩ := d1
  simp only at hrsp1 hr141 Hm1
  subst hrsp1 hr141 hQ
  rw [hspA] at Hm1
  kat hk ListU64UnmarshalSSZ 36
  apply load_step_at _ _ (rsp.toBitVec - 96) _ _ (Int.toBytes 8 nV.toInt) _ _ (by kaddr) (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk ListU64UnmarshalSSZ 37
  apply load_step_at _ _ (rsp.toBitVec + 8) _ _ (Int.toBytes 8 rax.toBitVec.toInt) _ _ (by kaddr) (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk ListU64UnmarshalSSZ 38
  apply store_step_at _ _ (rax.toBitVec + 8) _ _ _ cL _ _ (by kaddr) (by ecancel) (by exact hcL)
  intro m8 H8
  simp only [Width.bytes, Width.bits] at H8
  kunfold
  kat hk ListU64UnmarshalSSZ 39
  apply store_step_at _ _ (rax.toBitVec + 16) _ _ _ cC _ _ (by kaddr) (by ecancel) (by exact hcC)
  intro m9 H9
  simp only [Width.bytes, Width.bits] at H9
  kunfold
  kat hk ListU64UnmarshalSSZ 40
  apply load_step _ _ _ _ [0, 0, 0, 0] _ _ (by ecancel) (by simp)
  simp only [show Int.ofBytes [0, 0, 0, 0] = 0 by simp [Int.ofBytes]]
  kunfold
  kat hk ListU64UnmarshalSSZ 41
  split
  case isFalse h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
  simp only [Effects.All]
  klabel hk hf ListU64UnmarshalSSZ 46
  kat hk ListU64UnmarshalSSZ 46
  kat hk ListU64UnmarshalSSZ 47
  apply store_step_at _ _ (rax.toBitVec) _ _ _ cP _ _ (by kaddr) (by ecancel) (by exact hcP)
  intro m10 H10
  simp only [Width.bytes, Width.bits] at H10
  kunfold
  kat hk ListU64UnmarshalSSZ 48
  apply load_step_at _ _ (rsp.toBitVec - 88) _ _ (Int.toBytes 8 cV.toInt) _ _ (by kaddr) (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk ListU64UnmarshalSSZ 49
  apply load_step_at _ _ (rsp.toBitVec - 80) _ _ (Int.toBytes 8 dV.toInt) _ _ (by kaddr) (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk ListU64UnmarshalSSZ 50
  intro _
  kat hk ListU64UnmarshalSSZ 51
  klabel hk hf ListU64UnmarshalSSZ 148
  -- the input elements: at rbx + 4 = dV when n > 0; empty when n = 0
  have hbsd : bs.At (rbx.toBitVec + 4) = bs.At dV := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0; have hb0 : bs = [] := List.length_eq_zero_iff.mp (by simpa using hbs)
      subst hb0; simp [List.At]
    · rw [← hdV, dptr_buf rbx rdi n h0 (by simpa using hlen ▸ hcap) hcap63]
  rw [hbsd] at H10
  have hcN : 8 * n ≤ cV.toNat := by rw [← hcV]; exact cap_sub4 rdi n (by rw [← hlen]; exact hcap)
  refine eventually_trans _ _ _ _ (lu_loop k hk hf bs n hbs hn dV rax.toBitVec rax1.toBitVec nV hnN _ _ _ _ n 0 _
    (by omega) (by simp) hnN hcN rfl rfl rfl rfl rfl (by simp only [Nat.mul_zero, List.take_zero, List.nil_append, Nat.sub_zero]; ecancel)) ?_
  rintro ⟨d2, pc2⟩ ⟨hpc2, hrsp2, -, hr142, Hm2⟩
  dsimp only at hpc2 hrsp2 Hm2
  subst hpc2
  obtain ⟨⟨rax2, rbx2, rcx2, rdx2, rsi2, rdi2, rsp2, rbp2, r82, r92, r102, r112, r122, r132, r142, r152⟩,
    zmms2, flags2, mem2⟩ := d2
  simp only at hrsp2 hr142 Hm2
  subst hrsp2 hr142
  kat hk ListU64UnmarshalSSZ 167
  kat hk ListU64UnmarshalSSZ 168
  intro _
  kat hk ListU64UnmarshalSSZ 169
  intro _
  kat hk ListU64UnmarshalSSZ 170
  kat hk ListU64UnmarshalSSZ 171
  apply load_step_at _ _ (rsp.toBitVec - 8) _ _ (Int.toBytes 8 rbp.toBitVec.toInt) _ _ (pop_slot _) (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk ListU64UnmarshalSSZ 172
  rw [pop_slot, ret_slot]
  apply load_step _ _ _ _ (Int.toBytes 8 ra.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  apply Eventually.done
  have hnI : nV.toInt = (n : Int) := by rw [BitVec.toInt_eq_toNat_of_lt (by omega), hnN]
  rw [hnI] at Hm2
  refine ⟨rfl, ?_, ?_, ?_, rfl, rax1.toBitVec, Int.toBytes 8 rbp.toBitVec.toInt, Int.toBytes 8 (n : Int),
    Int.toBytes 8 cV.toInt, Int.toBytes 8 dV.toInt, Int.toBytes 8 rax.toBitVec.toInt, Int.toBytes 8 rbx.toBitVec.toInt,
    Int.toBytes 8 (Host.addrOf (k + 35 + 1)).toBitVec.toInt, stk1, spm1,
    ?l1, ?l2, ?l3, ?l4, ?l5, ?l6, ?l7, ?l8, hspm1, ?mem⟩
  · apply UInt64.toBitVec_inj.mp; simp
  · apply UInt64.toBitVec_inj.mp; simp
  · apply UInt64.toBitVec_inj.mp; simp
  case mem =>
    dsimp only
    simp only [Std.ExtHashMap.sep_emp, Width.bits, Width.bytes] at Hm2
    rw [hbsd]
    ecancel
  all_goals first | exact hstk1 | simp [Int.toBytes_length]
