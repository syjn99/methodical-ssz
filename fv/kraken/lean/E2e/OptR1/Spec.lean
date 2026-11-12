import E2e.OptR1.MainG
import E2e.CpWCover

/-!
# OPT-R1 reserve encoder against EthLib: spec corollary and the two covers

- `cpo_marshal_spec_k`: the conclusion of the baseline `E2e.cp_e2e_marshal_spec_k`, word for word, for the
  new code constant `CpMarshalO` (fast path, `L + 40 ≤ C`). Its premises are the new frame (spills at
  rsp + 8 / + 24, return slot rsp − 160, large-frame guard `guard + 24 < rsp`).
- `cpo_marshal_cover` (`len(Root) = 32`): for every `L ≤ C` (caller array `pre ++ spare`), the code returns
  `pre ++ serialize prysmCpDesc g.toValue` at the returned pointer. One disjunct only: unlike the baseline
  `E2e.cp_e2e_marshal_cover` there is no "reaches the second growslice call" case (the case where the heap left after the first growth is below the second call's budget).
- `cpo_marshal_reject_cover` (`len(Root) ≠ 32`): for every `L ≤ C`, `(nil, ErrBytesLength)` and some block
  holds `pre ++ epoch`.
Heap budget of both covers: `4·len + 8736 ≤ avail` (the baseline covers' premise).
-/

open Machine Runtime TestTarget E2e.OptR1.Code EthLib.Serialization.Ssz
variable [Host]

namespace E2e.OptR1

set_option maxHeartbeats 4000000 in
theorem cpo_marshal_spec_k (k : Nat) (hk : CpMarshalO.IsInfixAt Host.prog k) (hf : LabelsFresh CpMarshalO k)
    (g : PCp) (cst cC ctl pre d0 d1 : List UInt8) (hcst : cst.length = 8) (hcC : cC.length = 8)
    (hctl : ctl.length = 32) (hd0 : d0.length = 8) (hd1 : d1.length = 32)
    (p : BitVec 64) (s : MachineData) (ra guard : UInt64) (hpre : pre.length = s.regs.rcx.toNat)
    (fp s1 s2 s3 l16 l24 l32 t40 t30 rslot : List UInt8)
    (hfp : fp.length = 8) (h1 : s1.length = 8) (h2 : s2.length = 8) (h3 : s3.length = 8) (hl16 : l16.length = 8)
    (hl24 : l24.length = 8) (hl32 : l32.length = 8) (ht40 : t40.length = 16) (ht30 : t30.length = 16)
    (hrs : rslot.length = 8)
    (R : DataMem → Prop) (S : Nat) (scratch : List UInt8) (hsc : scratch.length = S)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s1.At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16)) ⋆ Eq (s3.At (s.regs.rsp.toBitVec + 24))
      ⋆ Eq (l16.At (s.regs.rsp.toBitVec - 16)) ⋆ Eq (l24.At (s.regs.rsp.toBitVec - 24))
      ⋆ Eq (l32.At (s.regs.rsp.toBitVec - 32)) ⋆ Eq (t30.At (s.regs.rsp.toBitVec - 48))
      ⋆ Eq (t40.At (s.regs.rsp.toBitVec - 64))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 160)) ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - 160 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq (cst.At s.regs.rax.toBitVec) ⋆ Eq ((uintBytes 8 g.epoch.toNat).toList.At (s.regs.rax.toBitVec + 8))
      ⋆ Eq ((Int.toBytes 8 p.toInt).At (s.regs.rax.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 24)) ⋆ Eq (cC.At (s.regs.rax.toBitVec + 32))
      ⋆ Eq (ctl.At (s.regs.rax.toBitVec + 40)) ⋆ Eq (g.root.toList.At p)
      ⋆ Eq (pre.At s.regs.rbx.toBitVec) ⋆ Eq (d0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
      ⋆ Eq (d1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 8)) ⋆ R)
    (hguard : guard.toNat + 24 < s.regs.rsp.toNat)
    (hcap : s.regs.rcx.toNat + 40 ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63)
    (hmm : MemmoveC S) :
    ∃ bs, serialize prysmCpDesc g.toValue = .ok bs ∧
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = s.regs.rbx
        ∧ st.data.regs.rbx.toNat = s.regs.rcx.toNat + 40 ∧ st.data.regs.rcx = s.regs.rdi
        ∧ st.data.regs.rdi = 0 ∧ st.data.regs.rsi = 0
        ∧ (Eq (pre.At s.regs.rbx.toBitVec) ⋆ Eq (bs.toList.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ fun _ => True) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  refine ⟨pcpEnc g, pcp_serialize g, ?_⟩
  have he8 : (uintBytes 8 g.epoch.toNat).toList.length = 8 := by simp [Spec.uintBytes_size]
  have hroot : g.root.toList.length = 32 := by simp
  refine eventually_mono (cpo_marshal_main k hk hf cst _ cC ctl _ pre d0 d1 hcst he8 hcC hctl hroot hd0 hd1 p s ra
    guard hpre fp s1 s2 s3 l16 l24 l32 t40 t30 rslot hfp h1 h2 h3 hl16 hl24 hl32 ht40 ht30 hrs R S scratch hsc h_mem
    hguard hcap hcap63 hmm) (fun st ⟨hpc, hrax, hrbx, hrcx, hrdi, hrsi, _, _, _, t, u, scr, _, _, _, hm⟩ =>
      ⟨hpc, hrax, hrbx, hrcx, hrdi, hrsi, ?_⟩)
  rw [pcp_enc_toList,
    at_app _ g.root.toList (b := s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 8) (by rw [he8]; rfl) (by simp [he8]), ← Std.ExtHashMap.sep_assoc]
  generalize (uintBytes 8 g.epoch.toNat).toList = E8 at hm ⊢
  generalize g.root.toList = Rt at hm ⊢
  exact sep_true (by ecancel)

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
theorem cpo_marshal_cover (k : Nat) (hk : CpMarshalO.IsInfixAt Host.prog k) (hf : LabelsFresh CpMarshalO k)
    (g : PCp) (cst cC ctl pre spare : List UInt8) (hcst : cst.length = 8) (hcC : cC.length = 8)
    (hctl : ctl.length = 32)
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
      ⋆ Eq (cst.At s.regs.rax.toBitVec) ⋆ Eq ((uintBytes 8 g.epoch.toNat).toList.At (s.regs.rax.toBitVec + 8))
      ⋆ Eq ((Int.toBytes 8 p.toInt).At (s.regs.rax.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 24)) ⋆ Eq (cC.At (s.regs.rax.toBitVec + 32))
      ⋆ Eq (ctl.At (s.regs.rax.toBitVec + 40)) ⋆ Eq (g.root.toList.At p)
      ⋆ Eq ((pre ++ spare).At s.regs.rbx.toBitVec) ⋆ Heap avail ⋆ R)
    (hguard : guard.toNat + 24 < s.regs.rsp.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63)
    (hbud : 4 * s.regs.rcx.toNat + 8736 ≤ avail) (hmax : avail ≤ maxAlloc)
    (hgs : GrowsliceC Heap E2e.Data.e2eU8Type_addr 1 S) (hmm : MemmoveC S) :
    ∃ bs, serialize prysmCpDesc g.toValue = .ok bs ∧
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rbx.toNat = s.regs.rcx.toNat + 40
          ∧ s.regs.rcx.toNat + 40 ≤ st.data.regs.rcx.toNat ∧ st.data.regs.rdi = 0 ∧ st.data.regs.rsi = 0
          ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14
          ∧ (Eq ((pre ++ bs.toList).At st.data.regs.rax.toBitVec) ⋆ Eq (g.root.toList.At p) ⋆ R ⋆ fun _ => True)
            st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  refine ⟨pcpEnc g, pcp_serialize g, ?_⟩
  rw [pcp_enc_toList]
  have he8 : (uintBytes 8 g.epoch.toNat).toList.length = 8 := by simp [Spec.uintBytes_size]
  have hroot : g.root.toList.length = 32 := by simp
  generalize (uintBytes 8 g.epoch.toNat).toList = e8 at *
  generalize g.root.toList = root at *
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hguard hcap63 hbud hpre hspare ⊢
  have := rcx.toNat_lt_size; have := rdi.toNat_lt_size; simp only [UInt64.size] at *
  have hL : rcx.toNat + 40 < 2 ^ 64 := by unfold maxAlloc at hmax; omega
  by_cases c1 : rcx.toNat + 40 ≤ rdi.toNat
  · -- fast path (no allocation)
    have htl : 40 ≤ spare.length := by omega
    rw [cpg_split rbx.toBitVec rcx.toBitVec pre spare hpre htl (by omega)] at h_mem
    refine eventually_mono (cpo_marshal_main k hk hf cst _ cC ctl _ pre (spare.take 8) ((spare.drop 8).take 32)
      hcst he8 hcC hctl hroot (by simp only [List.length_take]; omega)
      (by simp only [List.length_take, List.length_drop]; omega) p _ ra guard hpre fp s1 s2 s3 l16 l24 l32 t40 t30
      rslot hfp h1 h2 h3 hl16 hl24 hl32 ht40 ht30 hrs _ S scratch hsc (by dsimp only; ecancel) hguard c1 hcap63
      hmm) ?_
    rintro st ⟨e1, e2, e3, e4, e5, e6, e7, e8', e9, t, u, scr, ht, hu, hscr, Hm⟩
    refine ⟨e1, e3, by rw [e4]; exact c1, e5, e6, e7, e8', e9, ?_⟩
    rw [e2]
    apply sep_true
    rw [cpw_out rbx.toBitVec rcx pre _ _ hpre he8 hroot hL]
    ecancel
  · -- grow path: the reserve's one growslice call
    have hgrow : rdi.toNat < rcx.toNat + 40 := by omega
    rw [cpw_pre rbx.toBitVec rcx pre spare hpre (by omega)] at h_mem
    have hn := nextSliceCap_le (rcx.toNat + 40) rdi.toNat (by omega)
    have hng := nextSliceCap_ge (rcx.toNat + 40) rdi.toNat
    refine eventually_mono (cpo_marshal_grow_main k hk hf cst _ cC ctl _ pre spare hcst he8 hcC hctl hroot p _ ra
      guard hpre hspare fp s1 s2 s3 l16 l24 l32 t40 t30 zA zB zC spl rslot hfp h1 h2 h3 hl16 hl24 hl32 ht40 ht30
      hzA hzB hzC hspl hrs _ S scratch hsc Heap avail (by dsimp only; ecancel) hguard hgrow (by dsimp only; omega)
      hmax hgs hmm) ?_
    rintro st ⟨e1, e2, e3, e4, e5, e6, e7, e8', e9, z, t, u, scr, spl', tail, av', hz, ht, hu, hscr, hspl', htail,
      hav', Hm⟩
    refine ⟨e1, e2, by dsimp only at e3 ⊢; omega, e5, e6, e7, e8', e9, ?_⟩
    apply sep_true
    rw [cpw_out _ rcx pre _ _ hpre he8 hroot hL]
    ecancel

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
theorem cpo_marshal_reject_cover (k : Nat) (hk : CpMarshalO.IsInfixAt Host.prog k) (hf : LabelsFresh CpMarshalO k)
    (cst e8 cC ctl pre spare : List UInt8) (hcst : cst.length = 8) (he8 : e8.length = 8) (hcC : cC.length = 8)
    (hctl : ctl.length = 32)
    (p : BitVec 64) (rl e0 e1 : UInt64) (hrl : rl ≠ 32)
    (s : MachineData) (ra guard : UInt64) (hpre : pre.length = s.regs.rcx.toNat)
    (hspare : pre.length + spare.length = s.regs.rdi.toNat)
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
      ⋆ Eq ((pre ++ spare).At s.regs.rbx.toBitVec)
      ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At E2e.Data.e2eErrBytesLength_addr)
      ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrBytesLength" + 8).toBitVec) ⋆ Heap avail ⋆ R)
    (hguard : guard.toNat + 24 < s.regs.rsp.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63)
    (hbud : 4 * s.regs.rcx.toNat + 8736 ≤ avail) (hmax : avail ≤ maxAlloc)
    (hgs : GrowsliceC Heap E2e.Data.e2eU8Type_addr 1 S) (hmm : MemmoveC S) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0
        ∧ st.data.regs.rcx = 0 ∧ st.data.regs.rdi = e0 ∧ st.data.regs.rsi = e1
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ blk : BitVec 64, (Eq (pre.At blk) ⋆ Eq (e8.At (blk + s.regs.rcx.toBitVec))
          ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At E2e.Data.e2eErrBytesLength_addr)
          ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrBytesLength" + 8).toBitVec) ⋆ R
          ⋆ fun _ => True) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hguard hcap63 hbud hpre hspare ⊢
  have := rcx.toNat_lt_size; have := rdi.toNat_lt_size; simp only [UInt64.size] at *
  by_cases c1 : rcx.toNat + 40 ≤ rdi.toNat
  · have htl : 8 ≤ spare.length := by omega
    rw [cpw_split8 rbx.toBitVec rcx pre spare hpre htl (by omega)] at h_mem
    refine eventually_mono (cpo_marshal_reject_main k hk hf cst e8 cC ctl pre (spare.take 8) hcst he8 hcC hctl
      (by simp only [List.length_take]; omega) p rl e0 e1 hrl _ ra guard fp s1 s2 s3 t40 t30 hfp h1 h2 h3 ht40 ht30 _
      (by dsimp only; ecancel) hguard c1 hcap63) ?_
    rintro st ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, t, u, ht, hu, Hm⟩
    refine ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, rbx.toBitVec, ?_⟩
    apply sep_true
    ecancel
  · have hgrow : rdi.toNat < rcx.toNat + 40 := by omega
    rw [cpw_pre rbx.toBitVec rcx pre spare hpre (by omega)] at h_mem
    have hn := nextSliceCap_le (rcx.toNat + 40) rdi.toNat (by omega)
    refine eventually_mono (cpo_marshal_reject_grow_main k hk hf cst e8 cC ctl pre spare hcst he8 hcC hctl p rl e0 e1
      hrl _ ra guard hpre hspare fp s1 s2 s3 l16 l24 t40 t30 zA zB zC spl rslot hfp h1 h2 h3 hl16 hl24 ht40 ht30
      hzA hzB hzC hspl hrs _ S scratch hsc Heap avail (by dsimp only; ecancel) hguard hgrow (by dsimp only; omega)
      hmax hgs hmm) ?_
    rintro st ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, np, nc, z, t, u, scr, spl', tail, av', hnc, hub, hz, ht, hu, hscr,
      hspl', htail, hav', Hm⟩
    refine ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, np, ?_⟩
    apply sep_true
    ecancel

end E2e.OptR1
