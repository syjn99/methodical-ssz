import Fk.FvAccept
import Fk.Vbv

/-!
# BitVec.UnmarshalSSZ (Bitvector[4]), on Kraken main (regenerated code)

The generator fix F1 makes the decoder call `ssz.ValidateBitvector(buf[0:1], 4)`
before it allocates J. The callee is our own machine code: its accept path is
the specification `VbvAccC`, derived from `vbv_accept_main` (Fk/Vbv.lean).
-/

open Fk Fk.Code
variable [Host]

theorem bva_call (x : BitVec 64) : x - 8#64 - 72 - 8#64 = x - 88 := by bv_omega
theorem bva_s88 (x : BitVec 64) : x - 8#64 - 72 + 88 = x + 8 := by bv_omega
theorem bva_s96 (x : BitVec 64) : x - 8#64 - 72 + 96 = x + 16 := by bv_omega
theorem bva_fp (x : BitVec 64) : x - 88 - 8 = x - 96 := by bv_omega
theorem bva_sp (x : BitVec 64) : x - 88 + 8 = x - 80 := by bv_omega
theorem bva_scr (x : BitVec 64) (S : Nat) (h : 8 ≤ S) (h2 : S < 2 ^ 64) :
    x - 88 - BitVec.ofNat 64 S + BitVec.ofNat 64 (S - 8) = x - 96 := by
  have : BitVec.ofNat 64 (S - 8) = BitVec.ofNat 64 S - 8 := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_sub]; omega
  rw [this]; bv_omega
theorem bva_pop (x : BitVec 64) : (72 : BitVec 64) + ({ toBitVec := x - 88 } + 8 : UInt64).toBitVec = x - 8 := by
  simp only [UInt64.toBitVec_add, UInt64.toBitVec_ofNat]; bv_omega
theorem bva_spm (x : BitVec 64) : x - 80 + BitVec.ofNat 64 8 = x - 72 := by bv_omega
theorem bva_cnt0 (x : BitVec 64) :
    (BitVec.zeroExtend 64 (BitVec.extractLsb' 0 32 x ^^^ BitVec.extractLsb' 0 32 x)).toNat ≤ 1 := by simp
theorem bva_spill (x : BitVec 64) : x - 88 + 8 = x - 80 := by bv_omega
theorem bvb (x : BitVec 64) : ({ toBitVec := x - 88 } + 8 : UInt64).toBitVec = x - 80 := by
  simp only [UInt64.toBitVec_add, UInt64.toBitVec_ofNat]; bv_omega
theorem bvb48 (x : BitVec 64) : x - 80 + 48 = x - 32 := by bv_omega
theorem bvb40 (x : BitVec 64) : x - 80 + 40 = x - 40 := by bv_omega
theorem bvb88 (x : BitVec 64) : x - 80 + 88 = x + 8 := by bv_omega
theorem bvb96 (x : BitVec 64) : x - 80 + 96 = x + 16 := by bv_omega
theorem bvb8 (x : BitVec 64) : x - 80 - 8#64 = x - 88 := by bv_omega
theorem bvb72 (x : BitVec 64) : (72 : BitVec 64) + (x - 80) = x - 8 := by bv_omega
theorem bva_nat' (x : UInt64) (h : 88 ≤ x.toNat) : (x.toBitVec - 88).toNat = x.toNat - 88 := by
  rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; simp; omega)]; simp
theorem bva_shr4 (b : UInt8) (h : b.toNat < 16) : b.toNat >>> 4 = 0 := by
  rw [Nat.shiftRight_eq_div_pow]; omega

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 100000 in
theorem bv_accept_main (k : Nat) (hk : BitVecUnmarshalSSZ.IsInfixAt Host.prog k)
    (hf : LabelsFresh BitVecUnmarshalSSZ k)
    (b : UInt8) (hb : b.toNat < 16) (s : MachineData) (ra guard : UInt64)
    (fp s1 s2 f40 f32 rslot cP cL cC : List UInt8)
    (hfp : fp.length = 8) (h1 : s1.length = 8) (h2 : s2.length = 8) (h40 : f40.length = 8) (h32 : f32.length = 8)
    (hrs : rslot.length = 8) (hcP : cP.length = 8) (hcL : cL.length = 8) (hcC : cC.length = 8)
    (R : DataMem → Prop) (S : Nat) (scratch spm : List UInt8) (hsc : scratch.length = S) (h8S : 8 ≤ S)
    (hspm : spm.length = 24)
    (Heap : Nat → DataMem → Prop) (avail : Nat)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s1.At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq (f40.At (s.regs.rsp.toBitVec - 40)) ⋆ Eq (f32.At (s.regs.rsp.toBitVec - 32))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 88)) ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - 88 - BitVec.ofNat 64 S))
      ⋆ Eq (spm.At (s.regs.rsp.toBitVec - 80))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Heap avail
      ⋆ Eq ([b].At s.regs.rbx.toBitVec)
      ⋆ Eq (cP.At s.regs.rax.toBitVec) ⋆ Eq (cL.At (s.regs.rax.toBitVec + 8)) ⋆ Eq (cC.At (s.regs.rax.toBitVec + 16))
      ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R)
    (hguard : guard.toNat + 88 < s.regs.rsp.toNat) (hsp : 96 + S ≤ s.regs.rsp.toNat)
    (hlen : s.regs.rcx = 1) (hav : 1 * 1 ≤ avail)
    (hvbv : VbvAccC) (hms : MakesliceC Heap (label "type__" + 48736).toBitVec 1 S) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ (p : BitVec 64) (fp' s1' s2' f40' f32' rs' sc' spm' : List UInt8),
          fp'.length = 8 ∧ s1'.length = 8 ∧ s2'.length = 8 ∧ f40'.length = 8 ∧ f32'.length = 8 ∧ rs'.length = 8
          ∧ sc'.length = S ∧ spm'.length = 24 ∧
        (Eq ((Int.toBytes 8 p.toInt).At s.regs.rax.toBitVec)
          ⋆ Eq ((Int.toBytes 8 1).At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 1).At (s.regs.rax.toBitVec + 16)) ⋆ Eq ([b].At p)
          ⋆ Eq ([b].At s.regs.rbx.toBitVec) ⋆ Heap (avail - 1 * 1)
          ⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq (fp'.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s1'.At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq (s2'.At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq (f40'.At (s.regs.rsp.toBitVec - 40)) ⋆ Eq (f32'.At (s.regs.rsp.toBitVec - 32))
          ⋆ Eq (rs'.At (s.regs.rsp.toBitVec - 88)) ⋆ Eq (sc'.At (s.regs.rsp.toBitVec - 88 - BitVec.ofNat 64 S))
          ⋆ Eq (spm'.At (s.regs.rsp.toBitVec - 80))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hguard hsp hlen ⊢
  subst hlen
  have := rsp.toNat_lt_size; have := guard.toNat_lt_size; simp only [UInt64.size] at *
  have hS64 : S < 2 ^ 64 := by omega
  kat hk BitVecUnmarshalSSZ 0
  kat hk BitVecUnmarshalSSZ 1
  kat hk BitVecUnmarshalSSZ 2
  apply load_step _ _ _ _ (Int.toBytes 8 guard.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk BitVecUnmarshalSSZ 3
  split
  · rename_i h; exfalso
    simp [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, CondCode.interp, StatusFlags.from_result, BitVec.unsigned] at h
    rcases h with h | h
    · apply h; omega
    · have := congrArg BitVec.toNat h; simp [BitVec.toNat_sub] at this; omega
  simp only [Effects.All]
  kat hk BitVecUnmarshalSSZ 4
  apply store_step_at _ _ (rsp.toBitVec - 8) _ _ _ fp _ _ (by bv_omega) (by ecancel) (by exact hfp)
  intro m1 H1
  simp only [Width.bytes, Width.bits] at H1
  kunfold
  kat hk BitVecUnmarshalSSZ 5
  kat hk BitVecUnmarshalSSZ 6
  kat hk BitVecUnmarshalSSZ 7
  rw [bva_s96]
  apply store_step _ _ _ _ _ s2 _ _ (by ecancel) (by exact h2)
  intro m2 H2
  simp only [Width.bytes, Width.bits] at H2
  kunfold
  kat hk BitVecUnmarshalSSZ 8
  kat hk BitVecUnmarshalSSZ 9
  kat hk BitVecUnmarshalSSZ 10
  split
  case isTrue h => exact absurd h (by decide)
  simp only [Effects.All]
  kat hk BitVecUnmarshalSSZ 11
  rw [bva_s88]
  apply store_step _ _ _ _ _ s1 _ _ (by ecancel) (by exact h1)
  intro m3 H3
  simp only [Width.bytes, Width.bits] at H3
  kunfold
  kat hk BitVecUnmarshalSSZ 12
  rw [bva_s96]
  apply store_step _ _ _ _ _ (Int.toBytes 8 rbx.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  intro m4 H4
  simp only [Width.bytes, Width.bits] at H4
  kunfold
  kat hk BitVecUnmarshalSSZ 13
  kat hk BitVecUnmarshalSSZ 14
  kat hk BitVecUnmarshalSSZ 15
  kat hk BitVecUnmarshalSSZ 16
  kat hk BitVecUnmarshalSSZ 17
  rw [bva_call]
  apply store_step _ _ _ _ _ rslot _ _ (by ecancel) (by exact hrs)
  intro m5 H5
  simp only [Width.bytes, Width.bits] at H5
  kunfold
  rw [← List.take_append_drop (S - 8) scratch, Mem.At_append_sep _ _ _ (by simp [hsc]; omega),
    ← List.take_append_drop 8 spm, Mem.At_append_sep (spm.take 8) _ _ (by simp [hspm])] at H5
  simp only [List.length_take, hsc, hspm, show min (S - 8) S = S - 8 by omega, show min 8 24 = 8 by rfl,
    bva_scr _ S h8S hS64, bva_spm] at H5
  refine eventually_trans _ _ _ _ (hvbv _ (Host.addrOf (k + 17 + 1)) guard (scratch.drop (S - 8)) (spm.take 8) [] b _
    (by simp [hsc]; omega) (by simp [hspm]) ?g1 ?g2 ?g3 ?g4 ?g5 ?g6
    (by dsimp only; rw [bva_fp, bva_sp, List.nil_append]; ecancel)) ?_
  case g1 => dsimp only; show guard.toNat < (rsp.toBitVec - 88).toNat; rw [bva_nat' _ (by omega)]; omega
  case g2 => dsimp only; show 8 ≤ (rsp.toBitVec - 88).toNat; rw [bva_nat' _ (by omega)]; omega
  case g3 => dsimp only; rfl
  case g4 => dsimp only; rfl
  case g5 => dsimp only; simp; decide
  case g6 => dsimp only; exact bva_shr4 b hb
  rintro ⟨d2, pc2⟩ ⟨hpc2, hrax2, hrbx2, hrsp2, hrbp2, hr142, fp2, sp2, hfp2, hsp2, Hm2⟩
  dsimp only at hpc2 hrax2 hrbx2 hrsp2 hrbp2 hr142 Hm2
  subst hpc2
  obtain ⟨⟨rax2, rbx2, rcx2, rdx2, rsi2, rdi2, rsp2, rbp2, r82, r92, r102, r112, r122, r132, r142, r152⟩,
    zmms2, flags2, mem2⟩ := d2
  simp only [List.nil_append] at hrax2 hrbx2 hrsp2 hrbp2 hr142 Hm2
  subst hrax2 hrbx2 hrsp2 hrbp2 hr142
  rw [bva_fp, bva_sp] at Hm2
  kat hk BitVecUnmarshalSSZ 18
  intro _
  kat hk BitVecUnmarshalSSZ 19
  split
  case isFalse h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
  simp only [Effects.All]
  klabel hk hf BitVecUnmarshalSSZ 47
  kat hk BitVecUnmarshalSSZ 47
  kat hk BitVecUnmarshalSSZ 48
  rw [bvb, bvb48]
  apply store_step _ _ _ _ _ f32 _ _ (by ecancel) (by exact h32)
  intro m6 H6
  simp only [Width.bytes, Width.bits] at H6
  kunfold
  kat hk BitVecUnmarshalSSZ 49
  rw [bvb, bvb40]
  apply store_step _ _ _ _ _ f40 _ _ (by ecancel) (by exact h40)
  intro m7 H7
  simp only [Width.bytes, Width.bits] at H7
  kunfold
  kat hk BitVecUnmarshalSSZ 50
  kat hk BitVecUnmarshalSSZ 51
  intro _
  kat hk BitVecUnmarshalSSZ 52
  kat hk BitVecUnmarshalSSZ 53
  rw [bvb, bvb8]
  apply store_step _ _ _ _ _ (Int.toBytes 8 (Host.addrOf (k + 17 + 1)).toBitVec.toInt) _ _ (by ecancel)
    (by exact Int.toBytes_length 8 _)
  intro m8 H8
  simp only [Width.bytes, Width.bits] at H8
  kunfold
  have hlen1 : (scratch.take (S - 8) ++ fp2).length = S := by simp [hsc, hfp2]; omega
  have hlen2 : (sp2 ++ spm.drop 8).length = 24 := by simp [hsp2, hspm]
  refine eventually_trans _ _ _ _ (hms _ (Host.addrOf (k + 53 + 1)) 1 avail (scratch.take (S - 8) ++ fp2)
    (sp2 ++ spm.drop 8) _ rfl (bva_cnt0 _) (by rfl) hav (by unfold maxAlloc; omega) (by omega) hlen1 hlen2
    (by
      dsimp only
      rw [Mem.At_append_sep _ _ _ (by simp [hsc, hfp2]; omega), Mem.At_append_sep _ _ _ (by simp [hsp2, hspm])]
      simp only [List.length_take, hsc, hsp2, show min (S - 8) S = S - 8 by omega, bva_scr _ S h8S hS64, bva_spill]
      rw [show rsp.toBitVec - 80 + BitVec.ofNat 64 8 = rsp.toBitVec - 72 from bva_spm _]
      ecancel)) ?_
  rintro ⟨d3, pc3⟩ ⟨hpc3, hrsp3, hr143, -, stk3, spm3, hstk3, hspm3, Hm3⟩
  dsimp only at hpc3 hrsp3 hr143 Hm3
  subst hpc3
  obtain ⟨⟨rax3, rbx3, rcx3, rdx3, rsi3, rdi3, rsp3, rbp3, r83, r93, r103, r113, r123, r133, r143, r153⟩,
    zmms3, flags3, mem3⟩ := d3
  simp only at hrsp3 hr143 Hm3
  subst hrsp3 hr143
  rw [bva_sp] at Hm3
  kat hk BitVecUnmarshalSSZ 54
  rw [bvb, bvb88]
  apply load_step _ _ _ _ (Int.toBytes 8 rax.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk BitVecUnmarshalSSZ 55
  apply store_step_at _ _ (rax.toBitVec + 8) _ _ _ cL _ _ (by kaddr) (by ecancel) (by exact hcL)
  intro m9 H9
  simp only [Width.bytes, Width.bits] at H9
  kunfold
  kat hk BitVecUnmarshalSSZ 56
  apply store_step_at _ _ (rax.toBitVec + 16) _ _ _ cC _ _ (by kaddr) (by ecancel) (by exact hcC)
  intro m10 H10
  simp only [Width.bytes, Width.bits] at H10
  kunfold
  kat hk BitVecUnmarshalSSZ 57
  apply load_step _ _ _ _ [0, 0, 0, 0] _ _ (by ecancel) (by simp)
  simp only [show Int.ofBytes [0, 0, 0, 0] = 0 by simp [Int.ofBytes]]
  kunfold
  kat hk BitVecUnmarshalSSZ 58
  split
  case isFalse h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
  simp only [Effects.All]
  klabel hk hf BitVecUnmarshalSSZ 63
  kat hk BitVecUnmarshalSSZ 63
  kat hk BitVecUnmarshalSSZ 64
  apply store_step _ _ _ _ _ cP _ _ (by ecancel) (by exact hcP)
  intro m11 H11
  simp only [Width.bytes, Width.bits] at H11
  kunfold
  kat hk BitVecUnmarshalSSZ 65
  rw [bvb, bvb96]
  apply load_step _ _ _ _ (Int.toBytes 8 rbx.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk BitVecUnmarshalSSZ 66
  apply load_step _ _ _ _ [b] _ _ (by ecancel) (by rfl)
  kunfold
  kat hk BitVecUnmarshalSSZ 67
  apply store_step _ _ _ _ _ (List.replicate (1 * 1) 0) _ _ (by ecancel) (by rfl)
  intro m12 H12
  simp only [Width.bytes, Width.bits, zx8, toBytes_ofInt_ofBytes 8 1 rfl [b] rfl] at H12
  kunfold
  kat hk BitVecUnmarshalSSZ 68
  apply store_step_at _ _ (rax.toBitVec + 8) _ _ _ (Int.toBytes 8 (BitVec.toInt (0 : BitVec 64))) _ _ (by kaddr) (by ecancel) (by exact Int.toBytes_length 8 _)
  intro m13 H13
  simp only [Width.bytes, Width.bits] at H13
  kunfold
  kat hk BitVecUnmarshalSSZ 69
  apply store_step_at _ _ (rax.toBitVec + 16) _ _ _ (Int.toBytes 8 (BitVec.toInt (1 : BitVec 64))) _ _ (by kaddr) (by ecancel) (by exact Int.toBytes_length 8 _)
  intro m14 H14
  simp only [Width.bytes, Width.bits] at H14
  kunfold
  kat hk BitVecUnmarshalSSZ 70
  apply load_step _ _ _ _ [0, 0, 0, 0] _ _ (by ecancel) (by simp)
  simp only [show Int.ofBytes [0, 0, 0, 0] = 0 by simp [Int.ofBytes]]
  kunfold
  kat hk BitVecUnmarshalSSZ 71
  split
  case isFalse h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
  simp only [Effects.All]
  klabel hk hf BitVecUnmarshalSSZ 76
  kat hk BitVecUnmarshalSSZ 76
  kat hk BitVecUnmarshalSSZ 77
  apply store_step _ _ _ _ _ (Int.toBytes 8 rax3.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  intro m15 H15
  simp only [Width.bytes, Width.bits] at H15
  kunfold
  kat hk BitVecUnmarshalSSZ 78
  rw [bvb, bvb40]
  apply load_step _ _ _ _ (Int.toBytes 8 (0#64).toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk BitVecUnmarshalSSZ 79
  rw [bvb, bvb48]
  apply load_step _ _ _ _ (Int.toBytes 8 (0#64).toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk BitVecUnmarshalSSZ 80
  kat hk BitVecUnmarshalSSZ 81
  rw [bvb, bvb72]
  apply load_step _ _ _ _ (Int.toBytes 8 rbp.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk BitVecUnmarshalSSZ 82
  rw [show rsp.toBitVec - 8 + 8#64 = rsp.toBitVec from vbv_ret _]
  apply load_step _ _ _ _ (Int.toBytes 8 ra.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  apply Eventually.done
  simp only [show Int.toBytes 8 (BitVec.toInt (1 : BitVec 64)) = Int.toBytes 8 1 by decide] at H15
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, rax3.toBitVec, Int.toBytes 8 rbp.toBitVec.toInt, Int.toBytes 8 rax.toBitVec.toInt,
    Int.toBytes 8 rbx.toBitVec.toInt, Int.toBytes 8 (0#64).toInt, Int.toBytes 8 (0#64).toInt,
    Int.toBytes 8 (Host.addrOf (k + 53 + 1)).toBitVec.toInt, stk3, spm3,
    Int.toBytes_length 8 _, Int.toBytes_length 8 _, Int.toBytes_length 8 _, Int.toBytes_length 8 _,
    Int.toBytes_length 8 _, Int.toBytes_length 8 _, hstk3, hspm3, ?mem⟩
  case mem => dsimp only; ecancel
  all_goals first
    | trivial | rfl
    | (simp [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, Fk.ofInt_ofBytes_toBytes64]; done)
    | (apply UInt64.toBitVec_inj.mp; simp [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]; done)
    | (apply UInt64.toBitVec_inj.mp; simp [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]; bv_omega)
