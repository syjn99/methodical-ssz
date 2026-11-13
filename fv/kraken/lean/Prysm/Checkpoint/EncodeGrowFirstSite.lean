import Prysm.Checkpoint.EncodeFastPath

/-!
# Real Prysm `(*v1alpha1.Checkpoint).MarshalSSZTo`, growslice path, Go 1.26.10 machine code

`Encode.grow_first_site`: `cap(dst) < len(dst) + 8` (the first capacity test,
directives 17–18, fails), so the inlined `append(dst, epoch bytes...)` calls
`runtime.growslice(old = dst.ptr, newLen = len + 8, oldCap = cap, num = 8,
et = uint8)` (directives 19–27, contract `GrowsliceC Heap e2eU8Type_addr 1 S`,
an existing contract form; instance esz 1, Go 1.26.10 `growslice` /
`nextslicecap` byte-identical to 1.26.3 in the runtime source). With the
premise `len + 40 ≤ nextSliceCap (len + 8) cap` the new capacity is enough for
the root, so the second site (directives 39–41) does not grow. The code
continues at `L_7b` (directive 33) on the new block: the 8 epoch bytes at
`new[len..len+8]`, the 32 root bytes at `new[len+8..len+40]` (memmove), return
`(new, len + 40, newCap, nil)`. The new block holds the copied prefix; the old
block is unchanged; the rest of the new block (`newCap − len − 40` bytes) is
named. The spill slots that only this path writes: rax at rsp + 8 (directive
19), rcx at rsp + 24 (directive 20); the 40-byte growslice spill area at
rsp − 112.
-/

open Machine Runtime Prysm.Checkpoint.Code
variable [Host]

namespace Prysm.Checkpoint

theorem Encode.grow_first_site_split (np len : BitVec 64) (pre tail : List UInt8) (hpre : pre.length = len.toNat)
    (ht : 40 ≤ tail.length) (hb : pre.length + tail.length < 2 ^ 64) :
    Eq ((pre ++ tail).At np) = Eq (pre.At np) ⋆ Eq ((tail.take 8).At (np + len))
      ⋆ Eq (((tail.drop 8).take 32).At (np + len + 8)) ⋆ Eq ((tail.drop 40).At (np + len + 40)) := by
  rw [at_app pre tail (b := np + len) (by rw [hpre, BitVec.ofNat_toNat, BitVec.setWidth_eq]) (by omega)]
  have e1 : Eq (tail.At (np + len)) = Eq ((tail.take 8).At (np + len)) ⋆ Eq ((tail.drop 8).At (np + len + 8)) := by
    conv => lhs; rw [← List.take_append_drop 8 tail]
    exact at_app _ _ (by rw [List.length_take, Nat.min_eq_left (by omega)]; rfl) (by simp; omega)
  have e2 : Eq ((tail.drop 8).At (np + len + 8)) =
      Eq (((tail.drop 8).take 32).At (np + len + 8)) ⋆ Eq ((tail.drop 40).At (np + len + 40)) := by
    conv => lhs; rw [← List.take_append_drop 32 (tail.drop 8)]
    rw [List.drop_drop]
    refine at_app _ _ ?_ (by simp; omega)
    rw [List.length_take, List.length_drop, Nat.min_eq_left (by omega)]
    bv_omega
  rw [e1, e2]
  simp only [Std.ExtHashMap.sep_assoc]

theorem Encode.grow_first_site_n8 (x : UInt64) (h : x.toNat + 8 < 2 ^ 64) : ({ toBitVec := x.toBitVec + 8 } : UInt64).toNat = x.toNat + 8 := by
  show (x.toBitVec + 8).toNat = x.toNat + 8
  simp [BitVec.toNat_add]; omega

theorem Encode.grow_first_site_w (x : UInt64) : ({ toBitVec := x.toBitVec } : UInt64).toNat = x.toNat := rfl

theorem Encode.grow_first_site_e8 : ({ toBitVec := BitVec.zeroExtend 64 (BitVec.truncate 32 (8 : BitVec 64)) } : UInt64).toNat = 8 := by
  decide

theorem Encode.grow_first_site_slot2 (x : BitVec 64) : x - 112 - 8#64 = x - 120 := by bv_omega

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
theorem Encode.grow_first_site (k : Nat) (hk : marshalSSZTo.IsInfixAt Host.prog k) (hf : LabelsFresh marshalSSZTo k)
    (cst e8 cC ctl root pre : List UInt8) (hcst : cst.length = 8) (he8 : e8.length = 8) (hcC : cC.length = 8)
    (hctl : ctl.length = 32) (hroot : root.length = 32)
    (p : BitVec 64) (s : MachineData) (ra guard : UInt64) (hpre : pre.length = s.regs.rcx.toNat)
    (fp s1 s2 s3 l16 l24 l32 t40 t30 rslot spl : List UInt8)
    (hfp : fp.length = 8) (h1 : s1.length = 8) (h2 : s2.length = 8) (h3 : s3.length = 8)
    (hl16 : l16.length = 8) (hl24 : l24.length = 8)
    (hl32 : l32.length = 8) (ht40 : t40.length = 16) (ht30 : t30.length = 16) (hrs : rslot.length = 8)
    (hspl : spl.length = 40)
    (R : DataMem → Prop) (S : Nat) (scratch : List UInt8) (hsc : scratch.length = S)
    (Heap : Nat → DataMem → Prop) (avail : Nat)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s1.At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16)) ⋆ Eq (s3.At (s.regs.rsp.toBitVec + 24))
      ⋆ Eq (l16.At (s.regs.rsp.toBitVec - 16)) ⋆ Eq (l24.At (s.regs.rsp.toBitVec - 24))
      ⋆ Eq (l32.At (s.regs.rsp.toBitVec - 32)) ⋆ Eq (t30.At (s.regs.rsp.toBitVec - 48))
      ⋆ Eq (t40.At (s.regs.rsp.toBitVec - 64)) ⋆ Eq (spl.At (s.regs.rsp.toBitVec - 112))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 120)) ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - 120 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq (cst.At s.regs.rax.toBitVec) ⋆ Eq (e8.At (s.regs.rax.toBitVec + 8))
      ⋆ Eq ((Int.toBytes 8 p.toInt).At (s.regs.rax.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 24)) ⋆ Eq (cC.At (s.regs.rax.toBitVec + 32))
      ⋆ Eq (ctl.At (s.regs.rax.toBitVec + 40)) ⋆ Eq (root.At p)
      ⋆ Eq (pre.At s.regs.rbx.toBitVec) ⋆ Heap avail ⋆ R)
    (hguard : guard.toNat < s.regs.rsp.toNat) (hsp : 120 ≤ s.regs.rsp.toNat)
    (hlc : s.regs.rcx.toNat ≤ s.regs.rdi.toNat) (hgrow : s.regs.rdi.toNat < s.regs.rcx.toNat + 8)
    (hfit : s.regs.rcx.toNat + 40 ≤ nextSliceCap (s.regs.rcx.toNat + 8) s.regs.rdi.toNat)
    (hbud : 2 * nextSliceCap (s.regs.rcx.toNat + 8) s.regs.rdi.toNat + 8192 ≤ avail) (hmax : avail ≤ maxAlloc)
    (hgs : GrowsliceC Heap ElfData.CheckpointAndEpoch.e2eU8Type_addr 1 S) (hmm : MemmoveC S) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec
        ∧ st.data.regs.rbx.toNat = s.regs.rcx.toNat + 40
        ∧ nextSliceCap (s.regs.rcx.toNat + 8) s.regs.rdi.toNat ≤ st.data.regs.rcx.toNat
        ∧ st.data.regs.rdi = 0 ∧ st.data.regs.rsi = 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ (t u scr spl' rest : List UInt8) (av' : Nat), t.length = 8 ∧ u.length = 16 ∧ scr.length = S
          ∧ spl'.length = 40 ∧ s.regs.rcx.toNat + 40 + rest.length = st.data.regs.rcx.toNat
          ∧ av' + st.data.regs.rcx.toNat ≤ avail ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rcx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 24))
          ⋆ Eq ((Int.toBytes 8 st.data.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec - 16))
          ⋆ Eq ((Int.toBytes 8 st.data.regs.rcx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 24))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 40).toInt).At (s.regs.rsp.toBitVec - 32))
          ⋆ Eq (u.At (s.regs.rsp.toBitVec - 48)) ⋆ Eq (e8.At (s.regs.rsp.toBitVec - 64))
          ⋆ Eq (t.At (s.regs.rsp.toBitVec - 56)) ⋆ Eq (spl'.At (s.regs.rsp.toBitVec - 112))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 63)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 120))
          ⋆ Eq (scr.At (s.regs.rsp.toBitVec - 120 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (cst.At s.regs.rax.toBitVec) ⋆ Eq (e8.At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 p.toInt).At (s.regs.rax.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 24)) ⋆ Eq (cC.At (s.regs.rax.toBitVec + 32))
          ⋆ Eq (ctl.At (s.regs.rax.toBitVec + 40)) ⋆ Eq (root.At p)
          ⋆ Eq (pre.At s.regs.rbx.toBitVec)
          ⋆ Eq (pre.At st.data.regs.rax.toBitVec) ⋆ Eq (e8.At (st.data.regs.rax.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (root.At (st.data.regs.rax.toBitVec + s.regs.rcx.toBitVec + 8))
          ⋆ Eq (rest.At (st.data.regs.rax.toBitVec + s.regs.rcx.toBitVec + 40))
          ⋆ Heap av' ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hguard hsp hlc hgrow hfit hbud hpre ⊢
  have := rsp.toNat_lt_size; have := guard.toNat_lt_size; have := rcx.toNat_lt_size; have := rdi.toNat_lt_size
  simp only [UInt64.size] at *
  have hnsc := nextSliceCap_le (rcx.toNat + 8) rdi.toNat (by omega)
  have hrcx48 : rcx.toNat + 40 ≤ 2 ^ 48 := by unfold maxAlloc at hmax; omega
  have hn8 := Encode.grow_first_site_n8 rcx (by omega)
  kat hk marshalSSZTo 0
  kat hk marshalSSZTo 1
  kat hk marshalSSZTo 2
  apply load_step _ _ _ _ (Int.toBytes 8 guard.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk marshalSSZTo 3
  split
  · rename_i h; exfalso
    simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned] at h
    rcases h with h | h
    · apply h; omega
    · have := congrArg BitVec.toNat h; simp [BitVec.toNat_sub] at this; omega
  simp only [Effects.All]
  kat hk marshalSSZTo 4
  apply store_step_at _ _ (rsp.toBitVec - 8) _ _ _ fp _ _ (by bv_omega) (by ecancel) (by exact hfp)
  intro m1 H1
  simp only [Width.bytes, Width.bits] at H1
  kunfold
  kat hk marshalSSZTo 5
  kat hk marshalSSZTo 6
  kat hk marshalSSZTo 7
  apply store_step_at _ _ (rsp.toBitVec + 16) _ _ _ s2 _ _ (by bv_omega) (by ecancel) (by exact h2)
  intro m2 H2
  simp only [Width.bytes, Width.bits] at H2
  kunfold
  kat hk marshalSSZTo 8
  kat hk marshalSSZTo 9
  apply load_step _ _ _ _ e8 _ _ (by ecancel) (by exact he8)
  kunfold
  kat hk marshalSSZTo 10
  kat hk marshalSSZTo 11
  kat hk marshalSSZTo 12
  kat hk marshalSSZTo 13
  kat hk marshalSSZTo 14
  simp only [AvxOperation.interp, MachineData.setAvxLegacy, AvxRegOrMem.interp]
  kunfold
  rw [show rsp.toBitVec - 8#64 - 104 + 48 = rsp.toBitVec - 64 by bv_omega]
  apply Machine.store_avx_step _ _ _ _ t40 _ _ (by ecancel) (by exact ht40) (by decide)
  intro m3 H3
  kunfold
  kat hk marshalSSZTo 15
  simp only [AvxOperation.interp, MachineData.setAvxLegacy, AvxRegOrMem.interp]
  kunfold
  rw [show rsp.toBitVec - 64 + 16 = rsp.toBitVec - 48 by bv_omega]
  apply Machine.store_avx_step _ _ _ _ t30 _ _ (by ecancel) (by exact ht30) (by decide)
  intro m4 H4
  kunfold
  rw [Machine.at_split16 _ (Int.toBytes_length 16 _) (rsp.toBitVec - 64),
    show rsp.toBitVec - 64 + 8 = rsp.toBitVec - 56 by bv_omega] at H4
  kat hk marshalSSZTo 16
  apply store_step_at _ _ (rsp.toBitVec - 64) _ _ _ ((Int.toBytes 16 (zmms.get (AvxReg.xmm RegMm.mm15)).toInt).take 8)
    _ _ (by checkpoint_addr) (by ecancel) (by rw [List.length_take, Int.toBytes_length]; rfl)
  intro m5 H5
  simp only [Width.bytes, Width.bits, toBytes_ofInt_ofBytes 64 8 rfl e8 he8] at H5
  kunfold
  kat hk marshalSSZTo 17
  kat hk marshalSSZTo 18
  split
  case isTrue h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned, BitVec.toNat_add] at h; omega
  simp only [Effects.All]
  -- growslice call (directives 19–27)
  kat hk marshalSSZTo 19
  apply store_step_at _ _ (rsp.toBitVec + 8) _ _ _ s1 _ _ (by checkpoint_addr) (by ecancel) (by exact h1)
  intro m6 H6
  simp only [Width.bytes, Width.bits] at H6
  kunfold
  kat hk marshalSSZTo 20
  apply store_step_at _ _ (rsp.toBitVec + 24) _ _ _ s3 _ _ (by checkpoint_addr) (by ecancel) (by exact h3)
  intro m7 H7
  simp only [Width.bytes, Width.bits] at H7
  kunfold
  kat hk marshalSSZTo 21
  kat hk marshalSSZTo 22
  kat hk marshalSSZTo 23
  kat hk marshalSSZTo 24
  kat hk marshalSSZTo 25
  kat hk marshalSSZTo 26
  kat hk marshalSSZTo 27
  apply store_step_at _ _ (rsp.toBitVec - 120) _ _ _ rslot _ _ (Encode.fast_path_slot _) (by ecancel) (by exact hrs)
  intro m8 H8
  simp only [Width.bytes, Width.bits] at H8
  kunfold
  rw [Encode.fast_path_slot] at *
  refine eventually_trans _ _ _ _ (hgs _ (Host.addrOf (k + 27 + 1)) pre scratch spl avail _ (by decide) rfl
    ?gnum ?gold ?gcap ?gbud hmax ?glen hsc hspl
    (by dsimp only; rw [show rsp.toBitVec - 120 + 8 = rsp.toBitVec - 112 by bv_omega]; ecancel)) ?_
  case gnum => dsimp only; rw [Encode.grow_first_site_e8, hn8]; omega
  case gold => dsimp only; (try simp) <;> omega
  case gcap => dsimp only; rw [Encode.grow_first_site_w rdi, hn8]; omega
  case gbud => dsimp only; rw [Encode.grow_first_site_w rdi, hn8]; omega
  case glen => dsimp only; rw [Encode.grow_first_site_e8, hn8]; omega
  rintro ⟨d1, pc1⟩ ⟨hpc1, hrsp1, hrbp1, hr141, hrbx1, hnc1, hub1, stk1, spl1, tail, av1, hstk1, hspl1, htail, hav1,
    Hm1⟩
  dsimp only at hpc1 hrsp1 hrbp1 hr141 hrbx1 hnc1 hub1 htail hav1 Hm1
  subst hpc1
  obtain ⟨⟨rax1, rbx1, rcx1, rdx1, rsi1, rdi1, rsp1, rbp1, r81, r91, r101, r111, r121, r131, r141, r151⟩,
    zmms1, flags1, mem1⟩ := d1
  simp only at hrsp1 hrbp1 hr141 hrbx1 hnc1 hub1 htail hav1 Hm1
  simp only [Encode.grow_first_site_w rdi, hn8] at hnc1 hub1
  obtain ⟨hc1, hc2⟩ := growslice_cap_bounds (by decide) (Nat.le_trans (by simpa using hbud) hmax) hnc1 hub1
  have htl : 40 ≤ tail.length := by omega
  have ht8 : (tail.take 8).length = 8 := by simp only [List.length_take]; omega
  have ht32 : ((tail.drop 8).take 32).length = 32 := by simp only [List.length_take, List.length_drop]; omega
  rw [Encode.fast_path_ret] at hrsp1
  subst rsp1 r141 rbp1 rbx1
  rw [Encode.grow_first_site_split rax1.toBitVec rcx.toBitVec pre tail hpre htl (by omega),
    show rsp.toBitVec - 120 + 8 = rsp.toBitVec - 112 by bv_omega] at Hm1
  kat hk marshalSSZTo 28
  kat hk marshalSSZTo 29
  kat hk marshalSSZTo 30
  apply load_step_at _ _ (rsp.toBitVec + 24) _ _ (Int.toBytes 8 rcx.toBitVec.toInt) _ _ (by checkpoint_addr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk marshalSSZTo 31
  kat hk marshalSSZTo 32
  apply load_step_at _ _ (rsp.toBitVec + 8) _ _ (Int.toBytes 8 rax.toBitVec.toInt) _ _ (by checkpoint_addr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  try simp only [ofInt_ofBytes_toBytes64]
  kat hk marshalSSZTo 33
  kat hk marshalSSZTo 34
  apply load_step_at _ _ (rsp.toBitVec - 64) _ _ e8 _ _ (by checkpoint_addr) (by ecancel) (by exact he8)
  kunfold
  kat hk marshalSSZTo 35
  rw [Codec.add_mul_one]
  apply store_step _ _ _ _ _ (tail.take 8) _ _ (by ecancel) (by exact ht8)
  intro m9 H9
  simp only [Width.bytes, Width.bits, toBytes_ofInt_ofBytes 64 8 rfl e8 he8] at H9
  kunfold
  kat hk marshalSSZTo 36
  apply load_step_at _ _ (rax.toBitVec + 16) _ _ (Int.toBytes 8 p.toInt) _ _ (by checkpoint_addr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk marshalSSZTo 37
  apply load_step_at _ _ (rax.toBitVec + 24) _ _ (Int.toBytes 8 32) _ _ (by checkpoint_addr) (by ecancel) (by rfl)
  simp only [show Int.ofBytes (Int.toBytes 8 32) = 32 by decide]
  kunfold
  kat hk marshalSSZTo 38
  split
  case isTrue h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
  simp only [Effects.All]
  kat hk marshalSSZTo 39
  kat hk marshalSSZTo 40
  kat hk marshalSSZTo 41
  split
  case isFalse h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned, BitVec.toNat_add] at h; omega
  simp only [Effects.All]
  klabel hk hf marshalSSZTo 55
  kat hk marshalSSZTo 55
  kat hk marshalSSZTo 56
  apply store_step_at _ _ (rsp.toBitVec - 24) _ _ _ l24 _ _ (by checkpoint_addr) (by ecancel) (by exact hl24)
  intro m10 H10
  simp only [Width.bytes, Width.bits] at H10
  kunfold
  kat hk marshalSSZTo 57
  apply store_step_at _ _ (rsp.toBitVec - 32) _ _ _ l32 _ _ (by checkpoint_addr) (by ecancel) (by exact hl32)
  intro m11 H11
  simp only [Width.bytes, Width.bits] at H11
  kunfold
  kat hk marshalSSZTo 58
  apply store_step_at _ _ (rsp.toBitVec - 16) _ _ _ l16 _ _ (by checkpoint_addr) (by ecancel) (by exact hl16)
  intro m12 H12
  simp only [Width.bytes, Width.bits] at H12
  kunfold
  kat hk marshalSSZTo 59
  kat hk marshalSSZTo 60
  kat hk marshalSSZTo 61
  kat hk marshalSSZTo 62
  apply store_step_at _ _ (rsp.toBitVec - 120) _ _ _ (Int.toBytes 8 (Host.addrOf (k + 27 + 1)).toBitVec.toInt) _ _
    (by checkpoint_addr) (by ecancel) (by exact Int.toBytes_length 8 _)
  intro m13 H13
  simp only [Width.bytes, Width.bits] at H13
  kunfold
  try rw [Encode.grow_first_site_slot2] at *
  try rw [Encode.fast_path_slot] at *
  rw [Codec.add_add_8_mul_one] at *
  refine eventually_trans _ _ _ _ (hmm _ (Host.addrOf (k + 62 + 1)) root ((tail.drop 8).take 32) stk1 _
    (by rw [hroot]; rfl) (by rw [hroot, ht32]) hstk1 (by dsimp only; ecancel)) ?_
  rintro ⟨e1, pc2⟩ ⟨hpc2, hrsp2, hr142, hrbp2, stk2, hstk2, Hm2⟩
  dsimp only at hpc2 hrsp2 hr142 hrbp2 Hm2
  subst hpc2
  obtain ⟨⟨rax2, rbx2, rcx2, rdx2, rsi2, rdi2, rsp2, rbp2, r82, r92, r102, r112, r122, r132, r142, r152⟩,
    zmms2, flags2, mem2⟩ := e1
  simp only at hrsp2 hr142 hrbp2 Hm2
  rw [Encode.fast_path_ret] at hrsp2
  subst rsp2 r142 rbp2
  kat hk marshalSSZTo 63
  apply load_step_at _ _ (rsp.toBitVec - 16) _ _ (Int.toBytes 8 rax1.toBitVec.toInt) _ _ (by checkpoint_addr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk marshalSSZTo 64
  apply load_step_at _ _ (rsp.toBitVec - 32) _ _ (Int.toBytes 8 (rcx.toBitVec + 8 + 32).toInt) _ _ (by checkpoint_addr)
    (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk marshalSSZTo 65
  apply load_step_at _ _ (rsp.toBitVec - 24) _ _ (Int.toBytes 8 rcx1.toBitVec.toInt) _ _ (by checkpoint_addr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk marshalSSZTo 66
  intro _
  kat hk marshalSSZTo 67
  intro _
  kat hk marshalSSZTo 68
  kat hk marshalSSZTo 69
  apply load_step_at _ _ (rsp.toBitVec - 8) _ _ (Int.toBytes 8 rbp.toBitVec.toInt) _ _ (by checkpoint_addr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk marshalSSZTo 70
  apply load_step_at _ _ rsp.toBitVec _ _ (Int.toBytes 8 ra.toBitVec.toInt) _ _ (by checkpoint_addr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  apply Eventually.done
  simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?tt, ?uu, stk2, spl1, tail.drop 40, av1, ?htt, ?huu, hstk2, hspl1, ?hrest,
    ?hav, ?hmem⟩
  case hmem =>
    rw [show k + 62 + 1 = k + 63 from rfl] at Hm2
    rw [show rcx.toBitVec + 40 = rcx.toBitVec + 8 + 32 by bv_omega]
    ecancel
  case htt => simp [Int.toBytes_length]
  case huu => simp [Int.toBytes_length]
  case hrest => show rcx.toNat + 40 + (tail.drop 40).length = rcx1.toNat; simp only [List.length_drop]; omega
  case hav => show av1 + rcx1.toNat ≤ avail; omega
  all_goals first
    | exact trivial
    | with_reducible rfl
    | (exact Encode.fast_path_len40 rcx (by omega))
    | (exact hnc1)
    | (dsimp only; omega)
    | (apply UInt64.toBitVec_inj.mp; simp; done)
    | (apply UInt64.toBitVec_inj.mp; checkpoint_addr)

end Prysm.Checkpoint
