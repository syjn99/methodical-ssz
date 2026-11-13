import Prysm.Checkpoint.EncodeGrowAnySite

/-!
# `(*v1alpha1.Checkpoint).MarshalSSZTo`: first growth, then the sharp case split of the second call

`Encode.grow_any_site_three_cases` has exactly the premises of `Encode.grow_any_site` (`len(Root) = 32`,
`cap < len + 8`, nil / cap 0 `dst` included; no new premise, no new contract form: `GrowsliceC` esz 1 and
`MemmoveC`, both existing). Its conclusion is a three-way disjunction, each with the exact frame:

- (A) the block `C1` from the first growth holds the root (`len + 40 ≤ C1`): return through `Encode.tail_fit`
  (same as the left disjunct of `Encode.grow_any_site`).
- (B) `C1 < len + 40` and the heap that the first call left is at least the budget of the second call
  (`2·nextSliceCap (len+40) C1 + 8192 ≤ av1`): return through the second `runtime.growslice` call
  (`Encode.tail_grow`). The caller's block keeps `pre`; the first new block `nb` keeps `pre ++ epoch ++ mid`;
  the returned block is `pre ++ epoch ++ root ++ rest`.
- (C) `C1 < len + 40` and the heap left is **below** that budget: the code is at the entry of the second
  call in the exact state of `Encode.tail_grow_call`, with `Heap av'` in memory and
  `av' < 2·nextSliceCap (len+40) C1 + 8192`.

Only (C) is not a return. It is the one state that the existing form cannot continue: `GrowsliceC`
gives the remaining heap of the first call only as an upper bound (`av' + C1 ≤ avail`), so the budget
premise of the second call is not derivable. The return in (C) is differential only.
Idea of the proof: the probe `r3_grow_any_sharp` (registers only); re-proved here with the frame.
-/

open Machine Runtime Prysm.Checkpoint.Code
variable [Host]

namespace Prysm.Checkpoint

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
theorem Encode.grow_any_site_three_cases (k : Nat) (hk : marshalSSZTo.IsInfixAt Host.prog k) (hf : LabelsFresh marshalSSZTo k)
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
      (fun st =>
        -- (A) first growth, the new block holds the root: return
        (st.pc = Int64.ofBitVec ra.toBitVec
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
          ⋆ Heap av' ⋆ R) st.data.dmem))
        -- (B) first growth, then second growth (the heap left covers the second call's budget): return
        ∨ (st.pc = Int64.ofBitVec ra.toBitVec
        ∧ st.data.regs.rbx.toNat = s.regs.rcx.toNat + 40 ∧ st.data.regs.rdi = 0 ∧ st.data.regs.rsi = 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14 ∧
        (∃ (t u scr spl' mid rest : List UInt8) (nb : BitVec 64) (C1 av1 av' : Nat), t.length = 8 ∧ u.length = 16
          ∧ scr.length = S ∧ spl'.length = 40
          ∧ nextSliceCap (s.regs.rcx.toNat + 8) s.regs.rdi.toNat ≤ C1 ∧ C1 < s.regs.rcx.toNat + 40
          ∧ s.regs.rcx.toNat + 8 + mid.length = C1 ∧ av1 + C1 ≤ avail
          ∧ 2 * nextSliceCap (s.regs.rcx.toNat + 40) C1 + 8192 ≤ av1
          ∧ nextSliceCap (s.regs.rcx.toNat + 40) C1 ≤ st.data.regs.rcx.toNat
          ∧ s.regs.rcx.toNat + 40 + rest.length = st.data.regs.rcx.toNat
          ∧ av' + st.data.regs.rcx.toNat ≤ av1 ∧
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
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 8).toInt).At (s.regs.rsp.toBitVec - 72))
          ⋆ Eq (spl'.At (s.regs.rsp.toBitVec - 112))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 63)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 120))
          ⋆ Eq (scr.At (s.regs.rsp.toBitVec - 120 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (cst.At s.regs.rax.toBitVec) ⋆ Eq (e8.At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 p.toInt).At (s.regs.rax.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 24)) ⋆ Eq (cC.At (s.regs.rax.toBitVec + 32))
          ⋆ Eq (ctl.At (s.regs.rax.toBitVec + 40)) ⋆ Eq (root.At p)
          ⋆ Eq (pre.At s.regs.rbx.toBitVec)
          ⋆ Eq (pre.At nb) ⋆ Eq (e8.At (nb + s.regs.rcx.toBitVec)) ⋆ Eq (mid.At (nb + s.regs.rcx.toBitVec + 8))
          ⋆ Eq (pre.At st.data.regs.rax.toBitVec) ⋆ Eq (e8.At (st.data.regs.rax.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (root.At (st.data.regs.rax.toBitVec + s.regs.rcx.toBitVec + 8))
          ⋆ Eq (rest.At (st.data.regs.rax.toBitVec + s.regs.rcx.toBitVec + 40))
          ⋆ Heap av' ⋆ R) st.data.dmem))
        -- (C) first growth, the heap left is below the second call's budget: entry of the second call
        ∨ (st.pc = label "runtime.growslice" ∧ st.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - 120 }
          ∧ st.data.regs.rbp = { toBitVec := s.regs.rsp.toBitVec - 8#64 } ∧ st.data.regs.r14 = s.regs.r14
          ∧ st.data.regs.rbx.toNat = s.regs.rcx.toNat + 40 ∧ st.data.regs.rdi.toNat = 32
          ∧ st.data.regs.rsi.toBitVec = ElfData.CheckpointAndEpoch.e2eU8Type_addr
          ∧ nextSliceCap (s.regs.rcx.toNat + 8) s.regs.rdi.toNat ≤ st.data.regs.rcx.toNat
          ∧ st.data.regs.rcx.toNat < s.regs.rcx.toNat + 40 ∧
          ∃ (t u scr spl' mid : List UInt8) (av' : Nat), t.length = 8 ∧ u.length = 16 ∧ scr.length = S
            ∧ spl'.length = 40 ∧ s.regs.rcx.toNat + 8 + mid.length = st.data.regs.rcx.toNat
            ∧ av' + st.data.regs.rcx.toNat ≤ avail
            ∧ av' < 2 * nextSliceCap (s.regs.rcx.toNat + 40) st.data.regs.rcx.toNat + 8192 ∧
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
            ⋆ Heap av' ⋆ R) st.data.dmem))
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
  · -- (A): the block from the first growth holds the root (Encode.tail_fit)
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
  · have hlt : d1.regs.rdi.toNat < rcx.toNat + 40 := by omega
    have htl : 8 ≤ tail.length := by omega
    have ht8 : (tail.take 8).length = 8 := by simp only [List.length_take]; omega
    rw [Encode.grow_any_site_split8 d1.regs.rbx.toBitVec rcx pre tail hpre htl (by omega)] at Hm1
    by_cases hb2 : 2 * nextSliceCap (rcx.toNat + 40) d1.regs.rdi.toNat + 8192 ≤ av1
    · -- (B): the heap left covers the second call's budget (Encode.tail_grow, GrowsliceC esz 1, existing form)
      refine eventually_mono (Encode.tail_grow k hk hf rsp r14 rbp ra rcx d1.regs.rdi rax.toBitVec d1.regs.rbx.toBitVec p
        e8 root pre (tail.take 8) l16 l24 l32 l72 spl1 (Int.toBytes 8 (Host.addrOf (k + 28)).toBitVec.toInt) scr1
        he8 hroot hpre ht8 hl16 hl24 hl32 hl72 hspl1 (Int.toBytes_length 8 _) S hscr1 _ Heap av1 d1 hrsp1 hrbp1 hr141
        (by rw [hrax1]) rfl hrcx1 hrdx1 rfl (by ecancel) (by omega) hlt hb2 (by omega) hgs hmm) ?_
      rintro st ⟨e1, e2, e3, e4, e5, e6, e7, e8', scr, spl', rest, av', hscr, hspl', hrest, hav', Hm⟩
      refine Or.inr (Or.inl ⟨e1, e2, e4, e5, e6, e7, e8', t, u, scr, spl', tail.drop 8, rest, d1.regs.rbx.toBitVec,
        d1.regs.rdi.toNat, av1, av', ht, hu, hscr, hspl', hnc1, hlt, by simp only [List.length_drop]; omega, hav1, hb2,
        e3, hrest, hav', ?_⟩)
      simp only [Std.ExtHashMap.sep_assoc, Std.ExtHashMap.sep_emp] at Hm ⊢
      simp only [Std.ExtHashMap.sep_comm, Std.ExtHashMap.sep_comm_l] at Hm ⊢
      exact Hm
    · -- (C): no lower bound on av1 from the contract; the run is at the second call, av1 below its budget
      refine eventually_mono (Encode.tail_grow_call k hk hf rsp r14 rbp ra rcx d1.regs.rdi rax.toBitVec d1.regs.rbx.toBitVec p
        e8 root pre (tail.take 8) l16 l24 l32 l72 spl1 (Int.toBytes 8 (Host.addrOf (k + 28)).toBitVec.toInt) scr1
        he8 hroot hpre ht8 hl16 hl24 hl32 hl72 hspl1 (Int.toBytes_length 8 _) S hscr1 _ d1 hrsp1 hrbp1 hr141
        (by rw [hrax1]) rfl hrcx1 hrdx1 rfl (by ecancel) (by omega) hlt (by unfold maxAlloc at hmax; omega)) ?_
      rintro st ⟨e1, e2, e3, e4, e5, e6, e7, e8', e9, Hm⟩
      refine Or.inr (Or.inr ⟨e1, e2, e3, e4, e6, e8', e9, by rw [e7]; exact hnc1, by rw [e7]; exact hlt,
        t, u, scr1, spl1, tail.drop 8, av1, ht, hu, hscr1, hspl1, by rw [e7]; simp only [List.length_drop]; omega,
        by rw [e7]; exact hav1, by rw [e7]; omega, ?_⟩)
      have e5' : st.data.regs.rax.toBitVec = d1.regs.rbx.toBitVec := e5
      rw [e5']
      simp only [Std.ExtHashMap.sep_assoc, Std.ExtHashMap.sep_emp] at Hm ⊢
      simp only [Std.ExtHashMap.sep_comm, Std.ExtHashMap.sep_comm_l] at Hm ⊢
      exact Hm

end Prysm.Checkpoint
