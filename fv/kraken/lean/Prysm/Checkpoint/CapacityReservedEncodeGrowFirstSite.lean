import Prysm.Checkpoint.CapacityReservedEncodeFastPath

/-! # OPT-R1 reserve encoder: the grow path (`len ≤ cap < len + 40`), valid and invalid root. See `Prysm.Checkpoint.CapacityReservedEncodeFastPath`. -/

open Machine Runtime Prysm.Checkpoint.CapacityReserved.Code
variable [Host]

namespace Prysm.Checkpoint.CapacityReserved

omit [Host] in
theorem Encode.reserve_split8 (z : List UInt8) (a : BitVec 64) (hz : z.length = 40) :
    Eq (z.At a) = Eq ((z.take 8).At a) ⋆ Eq ((z.drop 8).At (a + 8)) := by
  conv => lhs; rw [← List.take_append_drop 8 z]
  exact at_app _ _ (by rw [List.length_take, hz]; rfl) (by simp [hz])

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
theorem Encode.grow_first_site (k : Nat) (hk : marshalSSZTo.IsInfixAt Host.prog k) (hf : LabelsFresh marshalSSZTo k)
    (cst e8 cC ctl root pre spare : List UInt8) (hcst : cst.length = 8) (he8 : e8.length = 8) (hcC : cC.length = 8)
    (hctl : ctl.length = 32) (hroot : root.length = 32)
    (p : BitVec 64) (s : MachineData) (ra guard : UInt64) (hpre : pre.length = s.regs.rcx.toNat)
    (hspare : pre.length + spare.length = s.regs.rdi.toNat)
    (fp s1 s2 s3 l16 l24 l32 t40 t30 zA zB zC spl rslot : List UInt8)
    (hfp : fp.length = 8) (h1 : s1.length = 8) (h2 : s2.length = 8) (h3 : s3.length = 8) (hl16 : l16.length = 8)
    (hl24 : l24.length = 8) (hl32 : l32.length = 8) (ht40 : t40.length = 16) (ht30 : t30.length = 16)
    (hzA : zA.length = 16) (hzB : zB.length = 16) (hzC : zC.length = 8) (hspl : spl.length = 40)
    (hrs : rslot.length = 8)
    (R : DataMem → Prop) (S : Nat) (scratch : List UInt8) (hsc : scratch.length = S)
    (Heap : Nat → DataMem → Prop) (avail : Nat)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s1.At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16)) ⋆ Eq (s3.At (s.regs.rsp.toBitVec + 24))
      ⋆ Eq (l16.At (s.regs.rsp.toBitVec - 16)) ⋆ Eq (l24.At (s.regs.rsp.toBitVec - 24))
      ⋆ Eq (l32.At (s.regs.rsp.toBitVec - 32)) ⋆ Eq (t30.At (s.regs.rsp.toBitVec - 48))
      ⋆ Eq (t40.At (s.regs.rsp.toBitVec - 64))
      ⋆ Eq (zA.At (s.regs.rsp.toBitVec - 112)) ⋆ Eq (zB.At (s.regs.rsp.toBitVec - 96))
      ⋆ Eq (zC.At (s.regs.rsp.toBitVec - 80)) ⋆ Eq (spl.At (s.regs.rsp.toBitVec - 152))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 160)) ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - 160 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq (cst.At s.regs.rax.toBitVec) ⋆ Eq (e8.At (s.regs.rax.toBitVec + 8))
      ⋆ Eq ((Int.toBytes 8 p.toInt).At (s.regs.rax.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 24)) ⋆ Eq (cC.At (s.regs.rax.toBitVec + 32))
      ⋆ Eq (ctl.At (s.regs.rax.toBitVec + 40)) ⋆ Eq (root.At p)
      ⋆ Eq (pre.At s.regs.rbx.toBitVec) ⋆ Eq (spare.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
      ⋆ Heap avail ⋆ R)
    (hguard : guard.toNat + 24 < s.regs.rsp.toNat) (hgrow : s.regs.rdi.toNat < s.regs.rcx.toNat + 40)
    (hbud : 2 * nextSliceCap (s.regs.rcx.toNat + 40) s.regs.rdi.toNat + 8192 ≤ avail) (hmax : avail ≤ maxAlloc)
    (hgs : GrowsliceC Heap ElfData.CheckpointAndEpoch.e2eU8Type_addr 1 S) (hmm : MemmoveC S) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rbx.toNat = s.regs.rcx.toNat + 40
        ∧ nextSliceCap (s.regs.rcx.toNat + 40) s.regs.rdi.toNat ≤ st.data.regs.rcx.toNat
        ∧ st.data.regs.rcx.toNat ≤ 2 * nextSliceCap (s.regs.rcx.toNat + 40) s.regs.rdi.toNat + 8192
        ∧ st.data.regs.rdi = 0 ∧ st.data.regs.rsi = 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ (z t u scr spl' tail : List UInt8) (av' : Nat), z.length = 40 ∧ t.length = 8 ∧ u.length = 16
          ∧ scr.length = S ∧ spl'.length = 40 ∧ s.regs.rcx.toNat + 40 + tail.length = st.data.regs.rcx.toNat
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
          ⋆ Eq (t.At (s.regs.rsp.toBitVec - 56))
          ⋆ Eq (z.At (s.regs.rsp.toBitVec - 112)) ⋆ Eq (spl'.At (s.regs.rsp.toBitVec - 152))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 103)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 160))
          ⋆ Eq (scr.At (s.regs.rsp.toBitVec - 160 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (cst.At s.regs.rax.toBitVec) ⋆ Eq (e8.At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 p.toInt).At (s.regs.rax.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 24)) ⋆ Eq (cC.At (s.regs.rax.toBitVec + 32))
          ⋆ Eq (ctl.At (s.regs.rax.toBitVec + 40)) ⋆ Eq (root.At p)
          ⋆ Eq (pre.At s.regs.rbx.toBitVec) ⋆ Eq (spare.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (pre.At st.data.regs.rax.toBitVec) ⋆ Eq (e8.At (st.data.regs.rax.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (root.At (st.data.regs.rax.toBitVec + s.regs.rcx.toBitVec + 8))
          ⋆ Eq (tail.At (st.data.regs.rax.toBitVec + s.regs.rcx.toBitVec + 40))
          ⋆ Heap av' ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hguard hgrow hbud hpre hspare ⊢
  have hlc : rcx.toNat ≤ rdi.toNat := by omega
  have hng := nextSliceCap_ge (rcx.toNat + 40) rdi.toNat
  refine eventually_trans _ _ _ _ (Encode.head_grow k hk hf pre _ ra guard hpre fp s1 s2 s3 l16 l24 zA zB zC spl rslot
    hfp h1 h2 h3 hl16 hl24 hzA hzB hzC hspl hrs _ S scratch hsc Heap avail (by dsimp only; ecancel) hguard hlc hgrow
    hbud hmax hgs hmm) ?_
  rintro ⟨d, pc1⟩ ⟨hpc1, hrsp1, hrbp1, hr141, hrax1, hrcx1, hnc1, hub1, z, scr1, spl1, tail, av1, hz, hscr1, hspl1,
    htail, hav1, Hm1⟩
  dsimp only at hpc1 hrsp1 hrbp1 hr141 hrax1 hrcx1 hnc1 hub1 htail hav1 Hm1
  subst hpc1
  rw [Encode.reserve_split8 z (d.regs.rbx.toBitVec + rcx.toBitVec) hz] at Hm1
  refine eventually_mono (Encode.tail_fit k hk hf rsp r14 rbp ra rcx d.regs.rdx rax.toBitVec d.regs.rbx.toBitVec p e8 root pre
    (z.take 8) (z.drop 8) (Int.toBytes 8 d.regs.rbx.toBitVec.toInt) (Int.toBytes 8 d.regs.rdx.toBitVec.toInt) l32 t40 t30
    (Int.toBytes 8 (Host.addrOf (k + 41)).toBitVec.toInt) scr1 he8 hroot hpre (by simp [hz]) (by simp [hz])
    (Int.toBytes_length 8 _) (Int.toBytes_length 8 _) hl32 ht40 ht30 (Int.toBytes_length 8 _) S hscr1 _ d hrsp1 hrbp1
    hr141 (by rw [hrax1]) rfl hrcx1 rfl (by ecancel) (by omega) hmm) ?_
  rintro st ⟨e1, e2, e3, e4, e5, e6, e7, e8', e9, t, u, scr, ht, hu, hscr, Hm⟩
  refine ⟨e1, e3, by rw [e4]; exact hnc1, by rw [e4]; exact hub1, e5, e6, e7, e8', e9, z, t, u, scr, spl1, tail, av1,
    hz, ht, hu, hscr, hspl1, by rw [e4]; exact htail, by rw [e4]; exact hav1, ?_⟩
  rw [e2, e4]
  ecancel

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
theorem Encode.reject_length_grow_first_site (k : Nat) (hk : marshalSSZTo.IsInfixAt Host.prog k)
    (hf : LabelsFresh marshalSSZTo k)
    (cst e8 cC ctl pre spare : List UInt8) (hcst : cst.length = 8) (he8 : e8.length = 8) (hcC : cC.length = 8)
    (hctl : ctl.length = 32)
    (p : BitVec 64) (rl e0 e1 : UInt64) (hrl : rl ≠ 32) (s : MachineData) (ra guard : UInt64)
    (hpre : pre.length = s.regs.rcx.toNat) (hspare : pre.length + spare.length = s.regs.rdi.toNat)
    (fp s1 s2 s3 l16 l24 t40 t30 zA zB zC spl rslot : List UInt8)
    (hfp : fp.length = 8) (h1 : s1.length = 8) (h2 : s2.length = 8) (h3 : s3.length = 8) (hl16 : l16.length = 8)
    (hl24 : l24.length = 8) (ht40 : t40.length = 16) (ht30 : t30.length = 16)
    (hzA : zA.length = 16) (hzB : zB.length = 16) (hzC : zC.length = 8) (hspl : spl.length = 40)
    (hrs : rslot.length = 8)
    (R : DataMem → Prop) (S : Nat) (scratch : List UInt8) (hsc : scratch.length = S)
    (Heap : Nat → DataMem → Prop) (avail : Nat)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s1.At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16)) ⋆ Eq (s3.At (s.regs.rsp.toBitVec + 24))
      ⋆ Eq (l16.At (s.regs.rsp.toBitVec - 16)) ⋆ Eq (l24.At (s.regs.rsp.toBitVec - 24))
      ⋆ Eq (t30.At (s.regs.rsp.toBitVec - 48)) ⋆ Eq (t40.At (s.regs.rsp.toBitVec - 64))
      ⋆ Eq (zA.At (s.regs.rsp.toBitVec - 112)) ⋆ Eq (zB.At (s.regs.rsp.toBitVec - 96))
      ⋆ Eq (zC.At (s.regs.rsp.toBitVec - 80)) ⋆ Eq (spl.At (s.regs.rsp.toBitVec - 152))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 160)) ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - 160 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq (cst.At s.regs.rax.toBitVec) ⋆ Eq (e8.At (s.regs.rax.toBitVec + 8))
      ⋆ Eq ((Int.toBytes 8 p.toInt).At (s.regs.rax.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 rl.toBitVec.toInt).At (s.regs.rax.toBitVec + 24)) ⋆ Eq (cC.At (s.regs.rax.toBitVec + 32))
      ⋆ Eq (ctl.At (s.regs.rax.toBitVec + 40))
      ⋆ Eq (pre.At s.regs.rbx.toBitVec) ⋆ Eq (spare.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
      ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At ElfData.CheckpointAndEpoch.e2eErrBytesLength_addr)
      ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrBytesLength" + 8).toBitVec)
      ⋆ Heap avail ⋆ R)
    (hguard : guard.toNat + 24 < s.regs.rsp.toNat) (hgrow : s.regs.rdi.toNat < s.regs.rcx.toNat + 40)
    (hbud : 2 * nextSliceCap (s.regs.rcx.toNat + 40) s.regs.rdi.toNat + 8192 ≤ avail) (hmax : avail ≤ maxAlloc)
    (hgs : GrowsliceC Heap ElfData.CheckpointAndEpoch.e2eU8Type_addr 1 S) (hmm : MemmoveC S) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0
        ∧ st.data.regs.rcx = 0 ∧ st.data.regs.rdi = e0 ∧ st.data.regs.rsi = e1
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ (np : BitVec 64) (nc : UInt64) (z t u scr spl' tail : List UInt8) (av' : Nat),
          nextSliceCap (s.regs.rcx.toNat + 40) s.regs.rdi.toNat ≤ nc.toNat
          ∧ nc.toNat ≤ 2 * nextSliceCap (s.regs.rcx.toNat + 40) s.regs.rdi.toNat + 8192
          ∧ z.length = 40 ∧ t.length = 8 ∧ u.length = 16 ∧ scr.length = S ∧ spl'.length = 40
          ∧ s.regs.rcx.toNat + 40 + tail.length = nc.toNat ∧ av' + nc.toNat ≤ avail ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rcx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 24))
          ⋆ Eq ((Int.toBytes 8 np.toInt).At (s.regs.rsp.toBitVec - 16))
          ⋆ Eq ((Int.toBytes 8 nc.toBitVec.toInt).At (s.regs.rsp.toBitVec - 24))
          ⋆ Eq (u.At (s.regs.rsp.toBitVec - 48)) ⋆ Eq (e8.At (s.regs.rsp.toBitVec - 64))
          ⋆ Eq (t.At (s.regs.rsp.toBitVec - 56))
          ⋆ Eq (z.At (s.regs.rsp.toBitVec - 112)) ⋆ Eq (spl'.At (s.regs.rsp.toBitVec - 152))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 41)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 160))
          ⋆ Eq (scr.At (s.regs.rsp.toBitVec - 160 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (cst.At s.regs.rax.toBitVec) ⋆ Eq (e8.At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 p.toInt).At (s.regs.rax.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 rl.toBitVec.toInt).At (s.regs.rax.toBitVec + 24)) ⋆ Eq (cC.At (s.regs.rax.toBitVec + 32))
          ⋆ Eq (ctl.At (s.regs.rax.toBitVec + 40))
          ⋆ Eq (pre.At s.regs.rbx.toBitVec) ⋆ Eq (spare.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (pre.At np) ⋆ Eq (e8.At (np + s.regs.rcx.toBitVec)) ⋆ Eq ((z.drop 8).At (np + s.regs.rcx.toBitVec + 8))
          ⋆ Eq (tail.At (np + s.regs.rcx.toBitVec + 40))
          ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At ElfData.CheckpointAndEpoch.e2eErrBytesLength_addr)
          ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrBytesLength" + 8).toBitVec)
          ⋆ Heap av' ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hguard hgrow hbud hpre hspare ⊢
  have hlc : rcx.toNat ≤ rdi.toNat := by omega
  have hng := nextSliceCap_ge (rcx.toNat + 40) rdi.toNat
  refine eventually_trans _ _ _ _ (Encode.head_grow k hk hf pre _ ra guard hpre fp s1 s2 s3 l16 l24 zA zB zC spl rslot
    hfp h1 h2 h3 hl16 hl24 hzA hzB hzC hspl hrs _ S scratch hsc Heap avail (by dsimp only; ecancel) hguard hlc hgrow
    hbud hmax hgs hmm) ?_
  rintro ⟨d, pc1⟩ ⟨hpc1, hrsp1, hrbp1, hr141, hrax1, hrcx1, hnc1, hub1, z, scr1, spl1, tail, av1, hz, hscr1, hspl1,
    htail, hav1, Hm1⟩
  dsimp only at hpc1 hrsp1 hrbp1 hr141 hrax1 hrcx1 hnc1 hub1 htail hav1 Hm1
  subst hpc1
  rw [Encode.reserve_split8 z (d.regs.rbx.toBitVec + rcx.toBitVec) hz] at Hm1
  refine eventually_mono (Encode.tail_rej k hk hf rsp r14 rbp ra rcx d.regs.rdx e0 e1 rl hrl rax.toBitVec d.regs.rbx.toBitVec p
    e8 pre (z.take 8) t40 t30 he8 (by simp [hz]) ht40 ht30 _ d hrsp1 hrbp1 hr141 (by rw [hrax1]) rfl hrcx1 rfl
    (by ecancel) (by omega)) ?_
  rintro st ⟨e1', e2, e3, e4, e5, e6, e7, e8', e9, t, u, ht, hu, Hm⟩
  exact ⟨e1', e2, e3, e4, e5, e6, e7, e8', e9, d.regs.rbx.toBitVec, d.regs.rdx, z, t, u, scr1, spl1, tail, av1, hnc1,
    hub1, hz, ht, hu, hscr1, hspl1, htail, hav1, by ecancel⟩

end Prysm.Checkpoint.CapacityReserved
