import E2e.OptR1.Head

/-! # OPT-R1 reserve encoder: the grow prefix (`cap − len < 40`), directives 0–47. See `E2e.OptR1.Head`. -/

open Fk E2e.OptR1.Code
variable [Host]

namespace E2e.OptR1

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
theorem head_grow (k : Nat) (hk : CpMarshalO.IsInfixAt Host.prog k) (hf : LabelsFresh CpMarshalO k)
    (pre : List UInt8) (s : MachineData) (ra guard : UInt64) (hpre : pre.length = s.regs.rcx.toNat)
    (fp s1 s2 s3 l16 l24 zA zB zC spl rslot : List UInt8)
    (hfp : fp.length = 8) (h1 : s1.length = 8) (h2 : s2.length = 8) (h3 : s3.length = 8)
    (hl16 : l16.length = 8) (hl24 : l24.length = 8) (hzA : zA.length = 16) (hzB : zB.length = 16)
    (hzC : zC.length = 8) (hspl : spl.length = 40) (hrs : rslot.length = 8)
    (R : DataMem → Prop) (S : Nat) (scratch : List UInt8) (hsc : scratch.length = S)
    (Heap : Nat → DataMem → Prop) (avail : Nat)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s1.At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16)) ⋆ Eq (s3.At (s.regs.rsp.toBitVec + 24))
      ⋆ Eq (l16.At (s.regs.rsp.toBitVec - 16)) ⋆ Eq (l24.At (s.regs.rsp.toBitVec - 24))
      ⋆ Eq (zA.At (s.regs.rsp.toBitVec - 112)) ⋆ Eq (zB.At (s.regs.rsp.toBitVec - 96))
      ⋆ Eq (zC.At (s.regs.rsp.toBitVec - 80)) ⋆ Eq (spl.At (s.regs.rsp.toBitVec - 152))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 160)) ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - 160 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq (pre.At s.regs.rbx.toBitVec) ⋆ Heap avail ⋆ R)
    (hguard : guard.toNat + 24 < s.regs.rsp.toNat)
    (hlc : s.regs.rcx.toNat ≤ s.regs.rdi.toNat) (hgrow : s.regs.rdi.toNat < s.regs.rcx.toNat + 40)
    (hbud : 2 * nextSliceCap (s.regs.rcx.toNat + 40) s.regs.rdi.toNat + 8192 ≤ avail) (hmax : avail ≤ maxAlloc)
    (hgs : GrowsliceC Heap E2e.Data.e2eU8Type_addr 1 S) (hmm : MemmoveC S) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 48) ∧ st.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - 152 }
        ∧ st.data.regs.rbp = { toBitVec := s.regs.rsp.toBitVec - 8#64 } ∧ st.data.regs.r14 = s.regs.r14
        ∧ st.data.regs.rax = s.regs.rax ∧ st.data.regs.rcx = s.regs.rcx
        ∧ nextSliceCap (s.regs.rcx.toNat + 40) s.regs.rdi.toNat ≤ st.data.regs.rdx.toNat
        ∧ st.data.regs.rdx.toNat ≤ 2 * nextSliceCap (s.regs.rcx.toNat + 40) s.regs.rdi.toNat + 8192 ∧
        ∃ (z scr spl' tail : List UInt8) (av' : Nat), z.length = 40 ∧ scr.length = S ∧ spl'.length = 40
          ∧ s.regs.rcx.toNat + 40 + tail.length = st.data.regs.rdx.toNat ∧ av' + st.data.regs.rdx.toNat ≤ avail ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rcx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 24))
          ⋆ Eq ((Int.toBytes 8 st.data.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 16))
          ⋆ Eq ((Int.toBytes 8 st.data.regs.rdx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 24))
          ⋆ Eq (z.At (s.regs.rsp.toBitVec - 112)) ⋆ Eq (spl'.At (s.regs.rsp.toBitVec - 152))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 41)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 160))
          ⋆ Eq (scr.At (s.regs.rsp.toBitVec - 160 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (pre.At s.regs.rbx.toBitVec)
          ⋆ Eq (pre.At st.data.regs.rbx.toBitVec) ⋆ Eq (z.At (st.data.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (tail.At (st.data.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 40))
          ⋆ Heap av' ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hguard hlc hgrow hbud hpre ⊢
  have := rsp.toNat_lt_size; have := guard.toNat_lt_size; have := rcx.toNat_lt_size; have := rdi.toNat_lt_size
  simp only [UInt64.size] at *
  have hnsc := nextSliceCap_le (rcx.toNat + 40) rdi.toNat (by omega)
  have hnge := nextSliceCap_ge (rcx.toNat + 40) rdi.toNat
  have hrcx48 : rcx.toNat + 40 ≤ 2 ^ 48 := by unfold maxAlloc at hmax; omega
  have hn40 := o_n40 rcx (by omega)
  kat hk CpMarshalO 0
  kat hk CpMarshalO 1
  kat hk CpMarshalO 2
  kat hk CpMarshalO 3
  apply load_step _ _ _ _ (Int.toBytes 8 guard.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk CpMarshalO 4
  split
  case isTrue h =>
    exfalso
    rw [E2eScal.lea_cmp_be_false rsp.toBitVec _ guard.toBitVec _ _ 24 (by rfl) hguard] at h
    exact Bool.noConfusion h
  simp only [Effects.All]
  kat hk CpMarshalO 5
  apply store_step_at _ _ (rsp.toBitVec - 8) _ _ _ fp _ _ (by bv_omega) (by ecancel) (by exact hfp)
  intro m1 H1
  simp only [Width.bytes, Width.bits] at H1
  kunfold
  kat hk CpMarshalO 6
  kat hk CpMarshalO 7
  kat hk CpMarshalO 8
  apply store_step_at _ _ (rsp.toBitVec + 16) _ _ _ s2 _ _ (by bv_omega) (by ecancel) (by exact h2)
  intro m2 H2
  simp only [Width.bytes, Width.bits] at H2
  kunfold
  kat hk CpMarshalO 9
  apply store_step_at _ _ (rsp.toBitVec + 8) _ _ _ s1 _ _ (by bv_omega) (by ecancel) (by exact h1)
  intro m3 H3
  simp only [Width.bytes, Width.bits] at H3
  kunfold
  kat hk CpMarshalO 10
  apply store_step_at _ _ (rsp.toBitVec + 24) _ _ _ s3 _ _ (by bv_omega) (by ecancel) (by exact h3)
  intro m4 H4
  simp only [Width.bytes, Width.bits] at H4
  kunfold
  kat hk CpMarshalO 11
  kat hk CpMarshalO 12
  kat hk CpMarshalO 13
  kat hk CpMarshalO 14
  kat hk CpMarshalO 15
  split
  case isTrue h =>
    exfalso
    rw [o_lt _ _ _ _ ?g1 ?g2] at h
    · exact Bool.noConfusion h
    · exact o_sub40c rcx rdi hlc hgrow
    · decide
  simp only [Effects.All]
  -- the reserve: z := 0 (three movups of X15), directives 16–19
  kat hk CpMarshalO 16
  kat hk CpMarshalO 17
  simp only [AvxOperation.interp, MachineData.setAvxLegacy, AvxRegOrMem.interp]
  kunfold
  rw [show rsp.toBitVec - 8#64 - 144 + 40 = rsp.toBitVec - 112 by bv_omega]
  apply store_avx_step _ _ _ _ zA _ _ (by ecancel) (by exact hzA) (by decide)
  intro m5 H5
  kunfold
  kat hk CpMarshalO 18
  simp only [AvxOperation.interp, MachineData.setAvxLegacy, AvxRegOrMem.interp]
  kunfold
  rw [show rsp.toBitVec - 112 + 16 = rsp.toBitVec - 96 by bv_omega]
  apply store_avx_step _ _ _ _ zB _ _ (by ecancel) (by exact hzB) (by decide)
  intro m6 H6
  kunfold
  rw [lr_split16 _ (Int.toBytes_length 16 _) (rsp.toBitVec - 96),
    show rsp.toBitVec - 96 + 8 = rsp.toBitVec - 88 by bv_omega] at H6
  kat hk CpMarshalO 19
  simp only [AvxOperation.interp, MachineData.setAvxLegacy, AvxRegOrMem.interp]
  kunfold
  rw [show rsp.toBitVec - 112 + 24 = rsp.toBitVec - 88 by bv_omega]
  apply store_avx_step _ _ _ _ ((Int.toBytes 16 (zmms.get (AvxReg.xmm RegMm.mm15)).toInt).drop 8 ++ zC) _ _
    (by
      rw [at_app _ zC (b := rsp.toBitVec - 80) (by simp only [List.length_drop, Int.toBytes_length]; bv_omega)
        (by simp [hzC, Int.toBytes_length])]
      ecancel)
    (by simp only [List.length_append, List.length_drop, Int.toBytes_length, hzC]) (by decide)
  intro m7 H7
  kunfold
  -- capacity test of the reserve's append (directives 20–22): not taken
  kat hk CpMarshalO 20
  kat hk CpMarshalO 21
  kat hk CpMarshalO 22
  split
  case isTrue h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned, BitVec.toNat_add] at h; omega
  simp only [Effects.All]
  -- growslice call (directives 23–29)
  kat hk CpMarshalO 23
  kat hk CpMarshalO 24
  kat hk CpMarshalO 25
  kat hk CpMarshalO 26
  kat hk CpMarshalO 27
  kat hk CpMarshalO 28
  kat hk CpMarshalO 29
  apply store_step_at _ _ (rsp.toBitVec - 160) _ _ _ rslot _ _ (o_slot _) (by ecancel) (by exact hrs)
  intro m8 H8
  simp only [Width.bytes, Width.bits] at H8
  kunfold
  rw [o_slot] at *
  refine eventually_trans _ _ _ _ (hgs _ (Host.addrOf (k + 29 + 1)) pre scratch spl avail _ (by decide) rfl
    ?gnum ?gold ?gcap ?gbud hmax ?glen hsc hspl
    (by dsimp only; rw [show rsp.toBitVec - 160 + 8 = rsp.toBitVec - 152 by bv_omega]; ecancel)) ?_
  case gnum => dsimp only; (try rw [cpg_w rdi]); (try rw [o_e40]); (try rw [hn40]); omega
  case gold => dsimp only; (try rw [cpg_w rdi]); (try rw [o_e40]); (try rw [hn40]); omega
  case gcap => dsimp only; (try rw [cpg_w rdi]); (try rw [o_e40]); (try rw [hn40]); omega
  case gbud => dsimp only; (try rw [cpg_w rdi]); (try rw [o_e40]); (try rw [hn40]); omega
  case glen => dsimp only; (try rw [cpg_w rdi]); (try rw [o_e40]); (try rw [hn40]); omega
  rintro ⟨d1, pc1⟩ ⟨hpc1, hrsp1, hrbp1, hr141, hrbx1, hnc1, hub1, stk1, spl1, tail, av1, hstk1, hspl1, htail, hav1,
    Hm1⟩
  dsimp only at hpc1 hrsp1 hrbp1 hr141 hrbx1 hnc1 hub1 htail hav1 Hm1
  subst hpc1
  obtain ⟨⟨rax1, rbx1, rcx1, rdx1, rsi1, rdi1, rsp1, rbp1, r81, r91, r101, r111, r121, r131, r141, r151⟩,
    zmms1, flags1, mem1⟩ := d1
  simp only at hrsp1 hrbp1 hr141 hrbx1 hnc1 hub1 htail hav1 Hm1
  simp only [cpg_w rdi, hn40] at hnc1 hub1
  obtain ⟨hc1, hc2⟩ := growslice_cap_bounds (by decide) (Nat.le_trans (by simpa using hbud) hmax) hnc1 hub1
  rw [o_ret] at hrsp1
  subst rsp1 r141 rbp1 rbx1
  rw [show rsp.toBitVec - 160 + 8 = rsp.toBitVec - 152 by bv_omega] at Hm1
  have htl : 40 ≤ tail.length := by simp only [hpre] at htail; omega
  rw [o_split40 rax1.toBitVec rcx pre tail hpre htl (by simp only [hpre] at htail ⊢; omega)] at Hm1
  -- directives 30–34: restore, then the copy of z into the new block
  kat hk CpMarshalO 30
  kat hk CpMarshalO 31
  kat hk CpMarshalO 32
  kat hk CpMarshalO 33
  apply load_step_at _ _ (rsp.toBitVec + 24) _ _ (Int.toBytes 8 rcx.toBitVec.toInt) _ _ (by eaddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk CpMarshalO 34
  kat hk CpMarshalO 35
  apply store_step_at _ _ (rsp.toBitVec - 24) _ _ _ l24 _ _ (by eaddr) (by ecancel) (by exact hl24)
  intro m9 H9
  simp only [Width.bytes, Width.bits] at H9
  kunfold
  kat hk CpMarshalO 36
  apply store_step_at _ _ (rsp.toBitVec - 16) _ _ _ l16 _ _ (by eaddr) (by ecancel) (by exact hl16)
  intro m10 H10
  simp only [Width.bytes, Width.bits] at H10
  kunfold
  kat hk CpMarshalO 37
  kat hk CpMarshalO 38
  kat hk CpMarshalO 39
  kat hk CpMarshalO 40
  apply store_step_at _ _ (rsp.toBitVec - 160) _ _ _ (Int.toBytes 8 (Host.addrOf (k + 29 + 1)).toBitVec.toInt) _ _
    (o_call _) (by ecancel) (by exact Int.toBytes_length 8 _)
  intro m11 H11
  simp only [Width.bytes, Width.bits] at H11
  kunfold
  rw [o_call] at *
  try rw [cpm_mul] at *
  try rw [show rsp.toBitVec - 152 + 40 = rsp.toBitVec - 112 by bv_omega] at *
  have hX := Int.toBytes_length 16 (zmms.get (AvxReg.xmm RegMm.mm15)).toInt
  generalize Int.toBytes 16 (zmms.get (AvxReg.xmm RegMm.mm15)).toInt = X at *
  refine eventually_trans _ _ _ _ (hmm _ (Host.addrOf (k + 40 + 1)) (X ++ (X.take 8 ++ X)) (tail.take 40) stk1 _
    (by dsimp only; (try simp only [o_e40]); simp [hX])
    (by simp only [List.length_append, List.length_take, hX]; omega) hstk1
    (by
      dsimp only
      rw [at_app X _ (b := rsp.toBitVec - 96) (by rw [hX]; bv_omega) (by simp [hX]),
        at_app (X.take 8) X (b := rsp.toBitVec - 88) (by simp [hX]; bv_omega) (by simp [hX])]
      try rw [show rcx.toBitVec + rax1.toBitVec = rax1.toBitVec + rcx.toBitVec from BitVec.add_comm _ _]
      ecancel)) ?_
  rintro ⟨e1, pc2⟩ ⟨hpc2, hrsp2, hr142, hrbp2, stk2, hstk2, Hm2⟩
  dsimp only at hpc2 hrsp2 hr142 hrbp2 Hm2
  subst hpc2
  obtain ⟨⟨rax2, rbx2, rcx2, rdx2, rsi2, rdi2, rsp2, rbp2, r82, r92, r102, r112, r122, r132, r142, r152⟩,
    zmms2, flags2, mem2⟩ := e1
  simp only at hrsp2 hr142 hrbp2 Hm2
  rw [o_ret] at hrsp2
  subst rsp2 r142 rbp2
  -- directives 41–47: the [:len(dst)] bounds check and the reload
  kat hk CpMarshalO 41
  apply load_step_at _ _ (rsp.toBitVec + 24) _ _ (Int.toBytes 8 rcx.toBitVec.toInt) _ _ (by eaddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk CpMarshalO 42
  apply load_step_at _ _ (rsp.toBitVec - 24) _ _ (Int.toBytes 8 rcx1.toBitVec.toInt) _ _ (by eaddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk CpMarshalO 43
  kat hk CpMarshalO 44
  split
  case isTrue h =>
    exfalso
    try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl] at h
    rw [o_ja_false _ _ _ _ ?gb] at h
    · exact Bool.noConfusion h
    · have e1 : rcx.toBitVec.toNat = rcx.toNat := rfl
      have e2 : rcx1.toBitVec.toNat = rcx1.toNat := rfl
      omega
  simp only [Effects.All]
  kat hk CpMarshalO 45
  apply load_step_at _ _ (rsp.toBitVec + 8) _ _ (Int.toBytes 8 rax.toBitVec.toInt) _ _ (by eaddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk CpMarshalO 46
  kat hk CpMarshalO 47
  apply load_step_at _ _ (rsp.toBitVec - 16) _ _ (Int.toBytes 8 rax1.toBitVec.toInt) _ _ (by eaddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  apply Eventually.done
  refine ⟨rfl, ?_, ?_, rfl, ?_, ?_, ?nc, ?ub, X ++ (X.take 8 ++ X), stk2, spl1, tail.drop 40, av1,
    by simp only [List.length_append, List.length_take, hX]; omega, hstk2, hspl1, ?htl, ?hav, ?hmem⟩
  case nc => simpa using hnc1
  case ub => simpa using hub1
  case htl => simp only [List.length_drop] at htail ⊢; simp only [hpre] at htail; simp; omega
  case hav => simpa using hav1
  case hmem =>
    rw [show k + 40 + 1 = k + 41 from rfl] at Hm2
    dsimp only
    try rw [show rsp.toBitVec - 152 + 40 = rsp.toBitVec - 112 by bv_omega] at Hm2
    rw [show rcx.toBitVec + rax1.toBitVec = rax1.toBitVec + rcx.toBitVec from BitVec.add_comm _ _] at Hm2
    ecancel
  all_goals first
    | with_reducible rfl
    | (apply UInt64.toBitVec_inj.mp; simp; done)
    | (apply UInt64.toBitVec_inj.mp; eaddr)

end E2e.OptR1
