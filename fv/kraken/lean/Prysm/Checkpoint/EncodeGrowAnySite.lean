import Prysm.Checkpoint.EncodeGrowSecondSite

/-!
# `(*v1alpha1.Checkpoint).MarshalSSZTo`: first growth in every case, and the reject after the first growth

See `Prysm/Checkpoint/EncodeGrowSecondSite.lean` for the case map. `Encode.grow_any_site` has no premise on
`nextSliceCap`: the code branches on the capacity that `growslice` returned, and the conclusion is the
exact disjunction of the two branches. Left: the block from the first growth holds the root
(`Encode.tail_fit`, return with `dst ++ epoch ++ root`). Right: the code reaches the entry of the second
`runtime.growslice` call (directive 49) in the exact state that `Encode.tail_grow_call` states (first new
block `pre ++ epoch ++ mid`, `rbx = len + 40`, `rcx = C1 < len + 40`, `rdi = 32`). **The run after that
call is not proved**: `GrowsliceC`'s result gives only `avail' + newCap ≤ avail` for the remaining heap
(an upper bound), so the budget premise of a second `GrowsliceC` application cannot be derived; the
existing contract form does not chain two growslice calls. `Encode.tail_grow` proves the
second call and the rest when the caller supplies its budget (first append fitted:
`Encode.grow_second_site`).
-/

open Machine Runtime Prysm.Checkpoint.Code
variable [Host]

namespace Prysm.Checkpoint

theorem Encode.grow_any_site_split8 (np : BitVec 64) (L : UInt64) (pre tail : List UInt8) (hpre : pre.length = L.toNat)
    (ht : 8 ≤ tail.length) (hb : pre.length + tail.length < 2 ^ 64) :
    Eq ((pre ++ tail).At np) = Eq (pre.At np) ⋆ Eq ((tail.take 8).At (np + L.toBitVec))
      ⋆ Eq ((tail.drop 8).At (np + L.toBitVec + 8)) := by
  have e : pre ++ tail = pre ++ (tail.take 8 ++ tail.drop 8) := by simp only [List.take_append_drop]
  rw [e, at_app pre _ (b := np + L.toBitVec) (by rw [hpre]; apply BitVec.eq_of_toNat_eq; simp)
      (by simp only [List.length_append, List.length_take, List.length_drop]; omega),
    at_app (tail.take 8) _ (b := np + L.toBitVec + 8) (by rw [List.length_take, Nat.min_eq_left ht]; rfl)
      (by simp only [List.length_take, List.length_drop]; omega)]
  simp only [Std.ExtHashMap.sep_assoc]

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
theorem Encode.grow_any_site (k : Nat) (hk : marshalSSZTo.IsInfixAt Host.prog k) (hf : LabelsFresh marshalSSZTo k)
    (cst e8 cC ctl root pre : List UInt8) (hcst : cst.length = 8) (he8 : e8.length = 8) (hcC : cC.length = 8)
    (hctl : ctl.length = 32) (hroot : root.length = 32)
    (p : BitVec 64) (s : MachineData) (ra guard : UInt64) (hpre : pre.length = s.regs.rcx.toNat)
    (fp s1 s2 s3 l16 l24 l32 t40 t30 l72 spl rslot : List UInt8)
    (hfp : fp.length = 8) (h1 : s1.length = 8) (h2 : s2.length = 8) (h3 : s3.length = 8) (hl16 : l16.length = 8) (hl24 : l24.length = 8)
    (hl32 : l32.length = 8) (ht40 : t40.length = 16) (ht30 : t30.length = 16) (hl72 : l72.length = 8)
    (hspl : spl.length = 40) (hrs : rslot.length = 8)
    (R : DataMem → Prop) (S : Nat) (scratch : List UInt8) (hsc : scratch.length = S)
    (Heap : Nat → DataMem → Prop) (avail : Nat)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s1.At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16)) ⋆ Eq (s3.At (s.regs.rsp.toBitVec + 24))
      ⋆ Eq (l16.At (s.regs.rsp.toBitVec - 16)) ⋆ Eq (l24.At (s.regs.rsp.toBitVec - 24))
      ⋆ Eq (l32.At (s.regs.rsp.toBitVec - 32)) ⋆ Eq (t30.At (s.regs.rsp.toBitVec - 48))
      ⋆ Eq (t40.At (s.regs.rsp.toBitVec - 64)) ⋆ Eq (l72.At (s.regs.rsp.toBitVec - 72))
      ⋆ Eq (spl.At (s.regs.rsp.toBitVec - 112))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 120)) ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - 120 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq (cst.At s.regs.rax.toBitVec) ⋆ Eq (e8.At (s.regs.rax.toBitVec + 8))
      ⋆ Eq ((Int.toBytes 8 p.toInt).At (s.regs.rax.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 24)) ⋆ Eq (cC.At (s.regs.rax.toBitVec + 32))
      ⋆ Eq (ctl.At (s.regs.rax.toBitVec + 40)) ⋆ Eq (root.At p)
      ⋆ Eq (pre.At s.regs.rbx.toBitVec) ⋆ Heap avail ⋆ R)
    (hguard : guard.toNat < s.regs.rsp.toNat) (hsp : 120 ≤ s.regs.rsp.toNat)
    (hlc : s.regs.rcx.toNat ≤ s.regs.rdi.toNat) (hgrow : s.regs.rdi.toNat < s.regs.rcx.toNat + 8)
    (hbud : 2 * nextSliceCap (s.regs.rcx.toNat + 8) s.regs.rdi.toNat + 8192 ≤ avail) (hmax : avail ≤ maxAlloc)
    (hgs : GrowsliceC Heap ElfData.CheckpointAndEpoch.e2eU8Type_addr 1 S) (hmm : MemmoveC S) :
    Eventually (step1 Host.exe)
      (fun st => (st.pc = Int64.ofBitVec ra.toBitVec
        ∧ st.data.regs.rbx.toNat = s.regs.rcx.toNat + 40 ∧ st.data.regs.rdi = 0 ∧ st.data.regs.rsi = 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14 ∧
        (∃ (t u scr spl' rest : List UInt8) (av' : Nat), t.length = 8 ∧ u.length = 16 ∧ scr.length = S
          ∧ spl'.length = 40 ∧ s.regs.rcx.toNat + 40 + rest.length = st.data.regs.rcx.toNat
          ∧ nextSliceCap (s.regs.rcx.toNat + 8) s.regs.rdi.toNat ≤ st.data.regs.rcx.toNat
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
          ⋆ Eq (t.At (s.regs.rsp.toBitVec - 56)) ⋆ Eq (l72.At (s.regs.rsp.toBitVec - 72))
          ⋆ Eq (spl'.At (s.regs.rsp.toBitVec - 112))
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
        ∨ (st.pc = label "runtime.growslice" ∧ st.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - 120 }
          ∧ st.data.regs.rbp = { toBitVec := s.regs.rsp.toBitVec - 8#64 } ∧ st.data.regs.r14 = s.regs.r14
          ∧ st.data.regs.rbx.toNat = s.regs.rcx.toNat + 40 ∧ st.data.regs.rdi.toNat = 32
          ∧ st.data.regs.rsi.toBitVec = ElfData.CheckpointAndEpoch.e2eU8Type_addr
          ∧ nextSliceCap (s.regs.rcx.toNat + 8) s.regs.rdi.toNat ≤ st.data.regs.rcx.toNat
          ∧ st.data.regs.rcx.toNat < s.regs.rcx.toNat + 40 ∧
          ∃ (t u scr spl' mid : List UInt8) (av' : Nat), t.length = 8 ∧ u.length = 16 ∧ scr.length = S
            ∧ spl'.length = 40 ∧ s.regs.rcx.toNat + 8 + mid.length = st.data.regs.rcx.toNat
            ∧ av' + st.data.regs.rcx.toNat ≤ avail ∧
          (Eq ((Int.toBytes 8 (Host.addrOf (k + 50)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 120))
            ⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
            ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
            ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
            ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
            ⋆ Eq ((Int.toBytes 8 s.regs.rcx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 24))
            ⋆ Eq ((Int.toBytes 8 p.toInt).At (s.regs.rsp.toBitVec - 16)) ⋆ Eq (l24.At (s.regs.rsp.toBitVec - 24))
            ⋆ Eq (l32.At (s.regs.rsp.toBitVec - 32))
            ⋆ Eq (u.At (s.regs.rsp.toBitVec - 48)) ⋆ Eq (e8.At (s.regs.rsp.toBitVec - 64))
            ⋆ Eq (t.At (s.regs.rsp.toBitVec - 56))
            ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 8).toInt).At (s.regs.rsp.toBitVec - 72))
            ⋆ Eq (spl'.At (s.regs.rsp.toBitVec - 112))
            ⋆ Eq (scr.At (s.regs.rsp.toBitVec - 120 - BitVec.ofNat 64 S))
            ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
            ⋆ Eq (cst.At s.regs.rax.toBitVec) ⋆ Eq (e8.At (s.regs.rax.toBitVec + 8))
            ⋆ Eq ((Int.toBytes 8 p.toInt).At (s.regs.rax.toBitVec + 16))
            ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 24)) ⋆ Eq (cC.At (s.regs.rax.toBitVec + 32))
            ⋆ Eq (ctl.At (s.regs.rax.toBitVec + 40)) ⋆ Eq (root.At p)
            ⋆ Eq (pre.At s.regs.rbx.toBitVec)
            ⋆ Eq (pre.At st.data.regs.rax.toBitVec) ⋆ Eq (e8.At (st.data.regs.rax.toBitVec + s.regs.rcx.toBitVec))
            ⋆ Eq (mid.At (st.data.regs.rax.toBitVec + s.regs.rcx.toBitVec + 8))
            ⋆ Heap av' ⋆ R) st.data.dmem)))
      ⟨s, Host.addrOf k⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hguard hsp hlc hgrow hbud hpre ⊢
  have := rcx.toNat_lt_size; have := rdi.toNat_lt_size; simp only [UInt64.size] at *
  have hn1 := nextSliceCap_le (rcx.toNat + 8) rdi.toNat (by omega)
  have hn1g := nextSliceCap_ge (rcx.toNat + 8) rdi.toNat
  refine eventually_trans _ _ _ _ (Encode.head_grow k hk hf e8 pre he8 _ ra guard hpre fp s1 s2 s3 t40 t30 rslot spl
    hfp h1 h2 h3 ht40 ht30 hrs hspl _ S scratch hsc Heap avail (by dsimp only; ecancel) hguard hsp hlc hgrow
    hbud hmax hgs) ?_
  rintro ⟨d1, pc1⟩ ⟨hpc1, hrsp1, hrbp1, hr141, hrax1, hrcx1, hrdx1, hnc1, hub1, t, u, scr1, spl1, tail, av1, ht, hu,
    hscr1, hspl1, htail, hav1, Hm1⟩
  dsimp only at hpc1 hrsp1 hrbp1 hr141 hrax1 hrcx1 hrdx1 hnc1 hub1 htail hav1 Hm1
  subst hpc1
  have hC1 := d1.regs.rdi.toNat_lt_size
  simp only [UInt64.size] at hC1
  by_cases hfit2 : rcx.toNat + 40 ≤ d1.regs.rdi.toNat
  · -- the block from growslice holds the root: tail_fit (left disjunct)
    have htl : 40 ≤ tail.length := by omega
    have ht8 : (tail.take 8).length = 8 := by simp only [List.length_take]; omega
    have ht32 : ((tail.drop 8).take 32).length = 32 := by simp only [List.length_take, List.length_drop]; omega
    rw [Encode.grow_first_site_split d1.regs.rbx.toBitVec rcx.toBitVec pre tail hpre htl (by omega)] at Hm1
    refine eventually_mono (Encode.tail_fit k hk hf rsp r14 rbp ra rcx d1.regs.rdi rax.toBitVec d1.regs.rbx.toBitVec p
      e8 root pre (tail.take 8) ((tail.drop 8).take 32) l16 l24 l32 (Int.toBytes 8 (Host.addrOf (k + 28)).toBitVec.toInt)
      scr1 he8 hroot hpre ht8 ht32 hl16 hl24 hl32 (Int.toBytes_length 8 _) S hscr1 _ d1 hrsp1 hrbp1 hr141
      (by rw [hrax1]) rfl hrcx1 hrdx1 rfl (by ecancel) hfit2 hmm) ?_
    rintro st ⟨e1, e2, e3, e4, e5, e6, e7, e8', e9, scr, hscr, Hm⟩
    refine Or.inl ⟨e1, e3, e5, e6, e7, e8', e9, ⟨t, u, scr, spl1, tail.drop 40, av1, ht, hu, hscr, hspl1,
      by rw [e4]; simp only [List.length_drop]; omega, by rw [e4]; exact hnc1, by rw [e4]; omega, ?_⟩⟩
    rw [e4]
    have e2' : st.data.regs.rax = d1.regs.rbx := UInt64.toBitVec_inj.mp e2
    rw [e2']
    simp only [Std.ExtHashMap.sep_assoc, Std.ExtHashMap.sep_emp] at Hm ⊢
    simp only [Std.ExtHashMap.sep_comm, Std.ExtHashMap.sep_comm_l] at Hm ⊢
    exact Hm
  · -- the block is too small for the root: second growslice (right disjunct)
    have hlt : d1.regs.rdi.toNat < rcx.toNat + 40 := by omega
    have htl : 8 ≤ tail.length := by omega
    have ht8 : (tail.take 8).length = 8 := by simp only [List.length_take]; omega
    rw [Encode.grow_any_site_split8 d1.regs.rbx.toBitVec rcx pre tail hpre htl (by omega)] at Hm1
    refine eventually_mono (Encode.tail_grow_call k hk hf rsp r14 rbp ra rcx d1.regs.rdi rax.toBitVec d1.regs.rbx.toBitVec p
      e8 root pre (tail.take 8) l16 l24 l32 l72 spl1 (Int.toBytes 8 (Host.addrOf (k + 28)).toBitVec.toInt) scr1
      he8 hroot hpre ht8 hl16 hl24 hl32 hl72 hspl1 (Int.toBytes_length 8 _) S hscr1 _ d1 hrsp1 hrbp1 hr141
      (by rw [hrax1]) rfl hrcx1 hrdx1 rfl (by ecancel) (by omega) hlt (by unfold maxAlloc at hmax; omega)) ?_
    rintro st ⟨e1, e2, e3, e4, e5, e6, e7, e8', e9, Hm⟩
    refine Or.inr ⟨e1, e2, e3, e4, e6, e8', e9, by rw [e7]; exact hnc1, by rw [e7]; exact hlt,
      t, u, scr1, spl1, tail.drop 8, av1, ht, hu, hscr1, hspl1, by rw [e7]; simp only [List.length_drop]; omega,
      by rw [e7]; exact hav1, ?_⟩
    have e5' : st.data.regs.rax.toBitVec = d1.regs.rbx.toBitVec := e5
    rw [e5']
    simp only [Std.ExtHashMap.sep_assoc, Std.ExtHashMap.sep_emp] at Hm ⊢
    simp only [Std.ExtHashMap.sep_comm, Std.ExtHashMap.sep_comm_l] at Hm ⊢
    exact Hm

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
theorem Encode.reject_length_grow_first_site (k : Nat) (hk : marshalSSZTo.IsInfixAt Host.prog k) (hf : LabelsFresh marshalSSZTo k)
    (cst e8 cC ctl pre : List UInt8) (hcst : cst.length = 8) (he8 : e8.length = 8) (hcC : cC.length = 8)
    (hctl : ctl.length = 32)
    (p : BitVec 64) (s : MachineData) (ra guard : UInt64) (hpre : pre.length = s.regs.rcx.toNat)
    (fp s1 s2 s3 l16 l24 l32 t40 t30 l72 spl rslot : List UInt8)
    (hfp : fp.length = 8) (h1 : s1.length = 8) (h2 : s2.length = 8) (h3 : s3.length = 8) (hl16 : l16.length = 8) (hl24 : l24.length = 8)
    (hl32 : l32.length = 8) (ht40 : t40.length = 16) (ht30 : t30.length = 16) (hl72 : l72.length = 8)
    (hspl : spl.length = 40) (hrs : rslot.length = 8)
    (R : DataMem → Prop) (S : Nat) (scratch : List UInt8) (hsc : scratch.length = S)
    (Heap : Nat → DataMem → Prop) (avail : Nat) (rl e0 e1 : UInt64) (hrl : rl ≠ 32)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s1.At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16)) ⋆ Eq (s3.At (s.regs.rsp.toBitVec + 24))
      ⋆ Eq (l16.At (s.regs.rsp.toBitVec - 16)) ⋆ Eq (l24.At (s.regs.rsp.toBitVec - 24))
      ⋆ Eq (l32.At (s.regs.rsp.toBitVec - 32)) ⋆ Eq (t30.At (s.regs.rsp.toBitVec - 48))
      ⋆ Eq (t40.At (s.regs.rsp.toBitVec - 64)) ⋆ Eq (l72.At (s.regs.rsp.toBitVec - 72))
      ⋆ Eq (spl.At (s.regs.rsp.toBitVec - 112))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 120)) ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - 120 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq (cst.At s.regs.rax.toBitVec) ⋆ Eq (e8.At (s.regs.rax.toBitVec + 8))
      ⋆ Eq ((Int.toBytes 8 p.toInt).At (s.regs.rax.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 rl.toBitVec.toInt).At (s.regs.rax.toBitVec + 24)) ⋆ Eq (cC.At (s.regs.rax.toBitVec + 32))
      ⋆ Eq (ctl.At (s.regs.rax.toBitVec + 40))
      ⋆ Eq (pre.At s.regs.rbx.toBitVec) ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At ElfData.CheckpointAndEpoch.e2eErrBytesLength_addr)
      ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrBytesLength" + 8).toBitVec) ⋆ Heap avail ⋆ R)
    (hguard : guard.toNat < s.regs.rsp.toNat) (hsp : 120 ≤ s.regs.rsp.toNat)
    (hlc : s.regs.rcx.toNat ≤ s.regs.rdi.toNat) (hgrow : s.regs.rdi.toNat < s.regs.rcx.toNat + 8)
    (hbud : 2 * nextSliceCap (s.regs.rcx.toNat + 8) s.regs.rdi.toNat + 8192 ≤ avail) (hmax : avail ≤ maxAlloc)
    (hgs : GrowsliceC Heap ElfData.CheckpointAndEpoch.e2eU8Type_addr 1 S) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0
        ∧ st.data.regs.rcx = 0 ∧ st.data.regs.rdi = e0 ∧ st.data.regs.rsi = e1
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ (t u scr spl' mid : List UInt8) (nb : BitVec 64) (C1 av' : Nat), t.length = 8 ∧ u.length = 16
          ∧ scr.length = S ∧ spl'.length = 40 ∧ nextSliceCap (s.regs.rcx.toNat + 8) s.regs.rdi.toNat ≤ C1
          ∧ s.regs.rcx.toNat + 8 + mid.length = C1 ∧ av' + C1 ≤ avail ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rcx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 24))
          ⋆ Eq (l16.At (s.regs.rsp.toBitVec - 16)) ⋆ Eq (l24.At (s.regs.rsp.toBitVec - 24))
          ⋆ Eq (l32.At (s.regs.rsp.toBitVec - 32))
          ⋆ Eq (u.At (s.regs.rsp.toBitVec - 48)) ⋆ Eq (e8.At (s.regs.rsp.toBitVec - 64))
          ⋆ Eq (t.At (s.regs.rsp.toBitVec - 56)) ⋆ Eq (l72.At (s.regs.rsp.toBitVec - 72))
          ⋆ Eq (spl'.At (s.regs.rsp.toBitVec - 112))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 28)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 120))
          ⋆ Eq (scr.At (s.regs.rsp.toBitVec - 120 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (cst.At s.regs.rax.toBitVec) ⋆ Eq (e8.At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 p.toInt).At (s.regs.rax.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 rl.toBitVec.toInt).At (s.regs.rax.toBitVec + 24)) ⋆ Eq (cC.At (s.regs.rax.toBitVec + 32))
          ⋆ Eq (ctl.At (s.regs.rax.toBitVec + 40))
          ⋆ Eq (pre.At s.regs.rbx.toBitVec)
          ⋆ Eq (pre.At nb) ⋆ Eq (e8.At (nb + s.regs.rcx.toBitVec)) ⋆ Eq (mid.At (nb + s.regs.rcx.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At ElfData.CheckpointAndEpoch.e2eErrBytesLength_addr)
          ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrBytesLength" + 8).toBitVec)
          ⋆ Heap av' ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hguard hsp hlc hgrow hbud hpre ⊢
  have := rcx.toNat_lt_size; have := rdi.toNat_lt_size; simp only [UInt64.size] at *
  have hn1g := nextSliceCap_ge (rcx.toNat + 8) rdi.toNat
  refine eventually_trans _ _ _ _ (Encode.head_grow k hk hf e8 pre he8 _ ra guard hpre fp s1 s2 s3 t40 t30 rslot spl
    hfp h1 h2 h3 ht40 ht30 hrs hspl _ S scratch hsc Heap avail (by dsimp only; ecancel) hguard hsp hlc hgrow
    hbud hmax hgs) ?_
  rintro ⟨d1, pc1⟩ ⟨hpc1, hrsp1, hrbp1, hr141, hrax1, hrcx1, hrdx1, hnc1, hub1, t, u, scr1, spl1, tail, av1, ht, hu,
    hscr1, hspl1, htail, hav1, Hm1⟩
  dsimp only at hpc1 hrsp1 hrbp1 hr141 hrax1 hrcx1 hrdx1 hnc1 hub1 htail hav1 Hm1
  subst hpc1
  have hC1 := d1.regs.rdi.toNat_lt_size
  simp only [UInt64.size] at hC1
  have htl : 8 ≤ tail.length := by omega
  have ht8 : (tail.take 8).length = 8 := by simp only [List.length_take]; omega
  rw [Encode.grow_any_site_split8 d1.regs.rbx.toBitVec rcx pre tail hpre htl (by omega)] at Hm1
  refine eventually_mono (Encode.tail_rej k hk hf rsp r14 rbp ra rcx d1.regs.rdi e0 e1 rl hrl rax.toBitVec
    d1.regs.rbx.toBitVec p e8 pre (tail.take 8) he8 ht8 _ d1 hrsp1 hrbp1 hr141 (by rw [hrax1]) rfl hrcx1
    (by ecancel)) ?_
  rintro st ⟨e1', e2', e3', e4', e5', e6', e7', e8', e9', Hm⟩
  refine ⟨e1', e2', e3', e4', e5', e6', e7', e8', e9', t, u, scr1, spl1, tail.drop 8, d1.regs.rbx.toBitVec,
    d1.regs.rdi.toNat, av1, ht, hu, hscr1, hspl1, hnc1, by simp only [List.length_drop]; omega, hav1, ?_⟩
  simp only [Std.ExtHashMap.sep_assoc, Std.ExtHashMap.sep_emp] at Hm ⊢
  simp only [Std.ExtHashMap.sep_comm, Std.ExtHashMap.sep_comm_l] at Hm ⊢
  exact Hm

end Prysm.Checkpoint
