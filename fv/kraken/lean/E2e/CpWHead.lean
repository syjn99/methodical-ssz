import E2e.CpWTailG

/-!
# `(*v1alpha1.Checkpoint).MarshalSSZTo`: the two prefixes up to `L_7b` (directive 33) (INBOX 009)

- `cpw_head_fit`: `len + 8 ≤ cap`: directives 0–18 (`jae L_7b` taken): guard, prologue, the
  inlined Epoch encoder's stack temp (rsp0 − 64 … rsp0 − 33; X15 is not assumed zero), the block
  stays the caller's `dst`. The text of `cp_e2e_marshal_main`'s proof up to directive 33.
- `cpw_head_grow`: `cap < len + 8`: directives 0–32: the first `runtime.growslice(old = dst.ptr,
  newLen = len + 8, oldCap = cap, num = 8, et = uint8)` (`GrowsliceC Heap e2eU8Type_addr 1 S`,
  existing form, instance esz 1); the block becomes the new one (`pre ++ tail`, `tail` of
  `newCap − len` bytes), the old block keeps `pre`. No premise on `nextSliceCap` beyond the
  heap budget. The text of `cp_e2e_marshal_grow_main`'s proof up to directive 33.

Both end at `L_7b` in the register and stack state that the tails of `E2e.CpWTail` /
`E2e.CpWTailG` take.
-/

open Fk E2e.Code
variable [Host]

namespace E2e

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
theorem cpw_head_fit (k : Nat) (hk : CpMarshal.IsInfixAt Host.prog k) (hf : LabelsFresh CpMarshal k)
    (e8 : List UInt8) (he8 : e8.length = 8) (s : MachineData) (ra guard : UInt64)
    (fp s2 t40 t30 : List UInt8) (hfp : fp.length = 8) (h2 : s2.length = 8) (ht40 : t40.length = 16)
    (ht30 : t30.length = 16) (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq (t30.At (s.regs.rsp.toBitVec - 48)) ⋆ Eq (t40.At (s.regs.rsp.toBitVec - 64))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq (e8.At (s.regs.rax.toBitVec + 8)) ⋆ R)
    (hguard : guard.toNat < s.regs.rsp.toNat) (hsp : 120 ≤ s.regs.rsp.toNat)
    (hfit : s.regs.rcx.toNat + 8 ≤ s.regs.rdi.toNat) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 33) ∧ st.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - 112 }
        ∧ st.data.regs.rbp = { toBitVec := s.regs.rsp.toBitVec - 8#64 } ∧ st.data.regs.r14 = s.regs.r14
        ∧ st.data.regs.rax = s.regs.rax ∧ st.data.regs.rbx = s.regs.rbx ∧ st.data.regs.rcx = s.regs.rcx
        ∧ st.data.regs.rdx = { toBitVec := s.regs.rcx.toBitVec + 8 } ∧ st.data.regs.rdi = s.regs.rdi ∧
        ∃ (t u : List UInt8), t.length = 8 ∧ u.length = 16 ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq (u.At (s.regs.rsp.toBitVec - 48)) ⋆ Eq (e8.At (s.regs.rsp.toBitVec - 64))
          ⋆ Eq (t.At (s.regs.rsp.toBitVec - 56))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (e8.At (s.regs.rax.toBitVec + 8)) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hguard hsp hfit ⊢
  have := rsp.toNat_lt_size; have := guard.toNat_lt_size; have := rcx.toNat_lt_size; have := rdi.toNat_lt_size
  simp only [UInt64.size] at *
  kat hk CpMarshal 0
  kat hk CpMarshal 1
  kat hk CpMarshal 2
  apply load_step _ _ _ _ (Int.toBytes 8 guard.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk CpMarshal 3
  split
  · rename_i h; exfalso
    simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned] at h
    rcases h with h | h
    · apply h; omega
    · have := congrArg BitVec.toNat h; simp [BitVec.toNat_sub] at this; omega
  simp only [Effects.All]
  kat hk CpMarshal 4
  apply store_step_at _ _ (rsp.toBitVec - 8) _ _ _ fp _ _ (by bv_omega) (by ecancel) (by exact hfp)
  intro m1 H1
  simp only [Width.bytes, Width.bits] at H1
  kunfold
  kat hk CpMarshal 5
  kat hk CpMarshal 6
  kat hk CpMarshal 7
  apply store_step_at _ _ (rsp.toBitVec + 16) _ _ _ s2 _ _ (by bv_omega) (by ecancel) (by exact h2)
  intro m2 H2
  simp only [Width.bytes, Width.bits] at H2
  kunfold
  kat hk CpMarshal 8
  kat hk CpMarshal 9
  apply load_step _ _ _ _ e8 _ _ (by ecancel) (by exact he8)
  kunfold
  kat hk CpMarshal 10
  kat hk CpMarshal 11
  kat hk CpMarshal 12
  kat hk CpMarshal 13
  kat hk CpMarshal 14
  simp only [AvxOperation.interp, MachineData.setAvxLegacy, AvxRegOrMem.interp]
  kunfold
  rw [show rsp.toBitVec - 8#64 - 104 + 48 = rsp.toBitVec - 64 by bv_omega]
  apply store_avx_step _ _ _ _ t40 _ _ (by ecancel) (by exact ht40) (by decide)
  intro m3 H3
  kunfold
  kat hk CpMarshal 15
  simp only [AvxOperation.interp, MachineData.setAvxLegacy, AvxRegOrMem.interp]
  kunfold
  rw [show rsp.toBitVec - 64 + 16 = rsp.toBitVec - 48 by bv_omega]
  apply store_avx_step _ _ _ _ t30 _ _ (by ecancel) (by exact ht30) (by decide)
  intro m4 H4
  kunfold
  rw [lr_split16 _ (Int.toBytes_length 16 _) (rsp.toBitVec - 64),
    show rsp.toBitVec - 64 + 8 = rsp.toBitVec - 56 by bv_omega] at H4
  kat hk CpMarshal 16
  apply store_step_at _ _ (rsp.toBitVec - 64) _ _ _ ((Int.toBytes 16 (zmms.get (AvxReg.xmm RegMm.mm15)).toInt).take 8)
    _ _ (by eaddr) (by ecancel) (by rw [List.length_take, Int.toBytes_length]; rfl)
  intro m5 H5
  simp only [Width.bytes, Width.bits, toBytes_ofInt_ofBytes 64 8 rfl e8 he8] at H5
  kunfold
  kat hk CpMarshal 17
  kat hk CpMarshal 18
  split
  case isFalse h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned, BitVec.toNat_add] at h; omega
  simp only [Effects.All]
  klabel hk hf CpMarshal 33
  apply Eventually.done
  refine ⟨rfl, ?_, ?_, rfl, rfl, rfl, rfl, ?_, rfl, ?tt, ?uu, ?htt, ?huu, ?hmem⟩
  case hmem => ecancel
  case htt => simp [Int.toBytes_length]
  case huu => simp [Int.toBytes_length]
  all_goals first
    | with_reducible rfl
    | (apply UInt64.toBitVec_inj.mp; simp; done)
    | (apply UInt64.toBitVec_inj.mp; eaddr)

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
theorem cpw_head_grow (k : Nat) (hk : CpMarshal.IsInfixAt Host.prog k) (hf : LabelsFresh CpMarshal k)
    (e8 pre : List UInt8) (he8 : e8.length = 8)
    (s : MachineData) (ra guard : UInt64) (hpre : pre.length = s.regs.rcx.toNat)
    (fp s1 s2 s3 t40 t30 rslot spl : List UInt8)
    (hfp : fp.length = 8) (h1 : s1.length = 8) (h2 : s2.length = 8) (h3 : s3.length = 8)
    (ht40 : t40.length = 16) (ht30 : t30.length = 16) (hrs : rslot.length = 8) (hspl : spl.length = 40)
    (R : DataMem → Prop) (S : Nat) (scratch : List UInt8) (hsc : scratch.length = S)
    (Heap : Nat → DataMem → Prop) (avail : Nat)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s1.At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16)) ⋆ Eq (s3.At (s.regs.rsp.toBitVec + 24))
      ⋆ Eq (t30.At (s.regs.rsp.toBitVec - 48))
      ⋆ Eq (t40.At (s.regs.rsp.toBitVec - 64)) ⋆ Eq (spl.At (s.regs.rsp.toBitVec - 112))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 120)) ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - 120 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq (e8.At (s.regs.rax.toBitVec + 8))
      ⋆ Eq (pre.At s.regs.rbx.toBitVec) ⋆ Heap avail ⋆ R)
    (hguard : guard.toNat < s.regs.rsp.toNat) (hsp : 120 ≤ s.regs.rsp.toNat)
    (hlc : s.regs.rcx.toNat ≤ s.regs.rdi.toNat) (hgrow : s.regs.rdi.toNat < s.regs.rcx.toNat + 8)
    (hbud : 2 * nextSliceCap (s.regs.rcx.toNat + 8) s.regs.rdi.toNat + 8192 ≤ avail) (hmax : avail ≤ maxAlloc)
    (hgs : GrowsliceC Heap E2e.Data.e2eU8Type_addr 1 S) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 33) ∧ st.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - 112 }
        ∧ st.data.regs.rbp = { toBitVec := s.regs.rsp.toBitVec - 8#64 } ∧ st.data.regs.r14 = s.regs.r14
        ∧ st.data.regs.rax = s.regs.rax ∧ st.data.regs.rcx = s.regs.rcx
        ∧ st.data.regs.rdx = { toBitVec := s.regs.rcx.toBitVec + 8 }
        ∧ nextSliceCap (s.regs.rcx.toNat + 8) s.regs.rdi.toNat ≤ st.data.regs.rdi.toNat
        ∧ st.data.regs.rdi.toNat ≤ 2 * nextSliceCap (s.regs.rcx.toNat + 8) s.regs.rdi.toNat + 8192 ∧
        ∃ (t u scr spl' tail : List UInt8) (av' : Nat), t.length = 8 ∧ u.length = 16 ∧ scr.length = S
          ∧ spl'.length = 40 ∧ s.regs.rcx.toNat + tail.length = st.data.regs.rdi.toNat
          ∧ av' + st.data.regs.rdi.toNat ≤ avail ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rcx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 24))
          ⋆ Eq (u.At (s.regs.rsp.toBitVec - 48)) ⋆ Eq (e8.At (s.regs.rsp.toBitVec - 64))
          ⋆ Eq (t.At (s.regs.rsp.toBitVec - 56)) ⋆ Eq (spl'.At (s.regs.rsp.toBitVec - 112))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 28)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 120))
          ⋆ Eq (scr.At (s.regs.rsp.toBitVec - 120 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (e8.At (s.regs.rax.toBitVec + 8))
          ⋆ Eq (pre.At s.regs.rbx.toBitVec) ⋆ Eq ((pre ++ tail).At st.data.regs.rbx.toBitVec)
          ⋆ Heap av' ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hguard hsp hlc hgrow hbud hpre ⊢
  have := rsp.toNat_lt_size; have := guard.toNat_lt_size; have := rcx.toNat_lt_size; have := rdi.toNat_lt_size
  simp only [UInt64.size] at *
  have hnsc := nextSliceCap_le (rcx.toNat + 8) rdi.toNat (by omega)
  have hnge := nextSliceCap_ge (rcx.toNat + 8) rdi.toNat
  have hrcx48 : rcx.toNat + 8 ≤ 2 ^ 48 := by unfold maxAlloc at hmax; omega
  have hn8 := cpg_n8 rcx (by omega)
  kat hk CpMarshal 0
  kat hk CpMarshal 1
  kat hk CpMarshal 2
  apply load_step _ _ _ _ (Int.toBytes 8 guard.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk CpMarshal 3
  split
  · rename_i h; exfalso
    simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned] at h
    rcases h with h | h
    · apply h; omega
    · have := congrArg BitVec.toNat h; simp [BitVec.toNat_sub] at this; omega
  simp only [Effects.All]
  kat hk CpMarshal 4
  apply store_step_at _ _ (rsp.toBitVec - 8) _ _ _ fp _ _ (by bv_omega) (by ecancel) (by exact hfp)
  intro m1 H1
  simp only [Width.bytes, Width.bits] at H1
  kunfold
  kat hk CpMarshal 5
  kat hk CpMarshal 6
  kat hk CpMarshal 7
  apply store_step_at _ _ (rsp.toBitVec + 16) _ _ _ s2 _ _ (by bv_omega) (by ecancel) (by exact h2)
  intro m2 H2
  simp only [Width.bytes, Width.bits] at H2
  kunfold
  kat hk CpMarshal 8
  kat hk CpMarshal 9
  apply load_step _ _ _ _ e8 _ _ (by ecancel) (by exact he8)
  kunfold
  kat hk CpMarshal 10
  kat hk CpMarshal 11
  kat hk CpMarshal 12
  kat hk CpMarshal 13
  kat hk CpMarshal 14
  simp only [AvxOperation.interp, MachineData.setAvxLegacy, AvxRegOrMem.interp]
  kunfold
  rw [show rsp.toBitVec - 8#64 - 104 + 48 = rsp.toBitVec - 64 by bv_omega]
  apply store_avx_step _ _ _ _ t40 _ _ (by ecancel) (by exact ht40) (by decide)
  intro m3 H3
  kunfold
  kat hk CpMarshal 15
  simp only [AvxOperation.interp, MachineData.setAvxLegacy, AvxRegOrMem.interp]
  kunfold
  rw [show rsp.toBitVec - 64 + 16 = rsp.toBitVec - 48 by bv_omega]
  apply store_avx_step _ _ _ _ t30 _ _ (by ecancel) (by exact ht30) (by decide)
  intro m4 H4
  kunfold
  rw [lr_split16 _ (Int.toBytes_length 16 _) (rsp.toBitVec - 64),
    show rsp.toBitVec - 64 + 8 = rsp.toBitVec - 56 by bv_omega] at H4
  kat hk CpMarshal 16
  apply store_step_at _ _ (rsp.toBitVec - 64) _ _ _ ((Int.toBytes 16 (zmms.get (AvxReg.xmm RegMm.mm15)).toInt).take 8)
    _ _ (by eaddr) (by ecancel) (by rw [List.length_take, Int.toBytes_length]; rfl)
  intro m5 H5
  simp only [Width.bytes, Width.bits, toBytes_ofInt_ofBytes 64 8 rfl e8 he8] at H5
  kunfold
  kat hk CpMarshal 17
  kat hk CpMarshal 18
  split
  case isTrue h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned, BitVec.toNat_add] at h; omega
  simp only [Effects.All]
  -- growslice call (directives 19–27)
  kat hk CpMarshal 19
  apply store_step_at _ _ (rsp.toBitVec + 8) _ _ _ s1 _ _ (by eaddr) (by ecancel) (by exact h1)
  intro m6 H6
  simp only [Width.bytes, Width.bits] at H6
  kunfold
  kat hk CpMarshal 20
  apply store_step_at _ _ (rsp.toBitVec + 24) _ _ _ s3 _ _ (by eaddr) (by ecancel) (by exact h3)
  intro m7 H7
  simp only [Width.bytes, Width.bits] at H7
  kunfold
  kat hk CpMarshal 21
  kat hk CpMarshal 22
  kat hk CpMarshal 23
  kat hk CpMarshal 24
  kat hk CpMarshal 25
  kat hk CpMarshal 26
  kat hk CpMarshal 27
  apply store_step_at _ _ (rsp.toBitVec - 120) _ _ _ rslot _ _ (cpm_slot _) (by ecancel) (by exact hrs)
  intro m8 H8
  simp only [Width.bytes, Width.bits] at H8
  kunfold
  rw [cpm_slot] at *
  refine eventually_trans _ _ _ _ (hgs _ (Host.addrOf (k + 27 + 1)) pre scratch spl avail _ (by decide) rfl
    ?gnum ?gold ?gcap ?gbud hmax ?glen hsc hspl
    (by dsimp only; rw [show rsp.toBitVec - 120 + 8 = rsp.toBitVec - 112 by bv_omega]; ecancel)) ?_
  case gnum => dsimp only; rw [cpg_e8, hn8]; omega
  case gold => dsimp only; (try simp) <;> omega
  case gcap => dsimp only; rw [cpg_w rdi, hn8]; omega
  case gbud => dsimp only; rw [cpg_w rdi, hn8]; omega
  case glen => dsimp only; rw [cpg_e8, hn8]; omega
  rintro ⟨d1, pc1⟩ ⟨hpc1, hrsp1, hrbp1, hr141, hrbx1, hnc1, hub1, stk1, spl1, tail, av1, hstk1, hspl1, htail, hav1,
    Hm1⟩
  dsimp only at hpc1 hrsp1 hrbp1 hr141 hrbx1 hnc1 hub1 htail hav1 Hm1
  subst hpc1
  obtain ⟨⟨rax1, rbx1, rcx1, rdx1, rsi1, rdi1, rsp1, rbp1, r81, r91, r101, r111, r121, r131, r141, r151⟩,
    zmms1, flags1, mem1⟩ := d1
  simp only at hrsp1 hrbp1 hr141 hrbx1 hnc1 hub1 htail hav1 Hm1
  simp only [cpg_w rdi, hn8] at hnc1 hub1
  obtain ⟨hc1, hc2⟩ := growslice_cap_bounds (by decide) (Nat.le_trans (by simpa using hbud) hmax) hnc1 hub1
  rw [cpm_ret] at hrsp1
  subst rsp1 r141 rbp1 rbx1
  rw [show rsp.toBitVec - 120 + 8 = rsp.toBitVec - 112 by bv_omega] at Hm1
  kat hk CpMarshal 28
  kat hk CpMarshal 29
  kat hk CpMarshal 30
  apply load_step_at _ _ (rsp.toBitVec + 24) _ _ (Int.toBytes 8 rcx.toBitVec.toInt) _ _ (by eaddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk CpMarshal 31
  kat hk CpMarshal 32
  apply load_step_at _ _ (rsp.toBitVec + 8) _ _ (Int.toBytes 8 rax.toBitVec.toInt) _ _ (by eaddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  try simp only [ofInt_ofBytes_toBytes64]
  apply Eventually.done
  refine ⟨rfl, ?_, ?_, rfl, ?_, rfl, ?_, hnc1, by simpa using hub1, ?tt, ?uu, stk1, spl1, tail, av1, ?htt, ?huu, hstk1, hspl1,
    by simpa [hpre] using htail, by simpa using hav1, ?hmem⟩
  case hmem => rw [show k + 27 + 1 = k + 28 from rfl] at Hm1; ecancel
  case htt => simp [Int.toBytes_length]
  case huu => simp [Int.toBytes_length]
  all_goals first
    | with_reducible rfl
    | (apply UInt64.toBitVec_inj.mp; simp; done)
    | (apply UInt64.toBitVec_inj.mp; eaddr)

end E2e
