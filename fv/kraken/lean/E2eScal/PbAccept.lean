import E2eScal.Compose
import E2eScal.Gen4H6PbDec
import E2eScal.E1Accept
import E2eScal.H6Stmt

/-!
# `(*v1alpha1.PowBlock).UnmarshalSSZ`, accept path from the GENERATED `p2dec --gen4` chains (hold-out, full-proof type)

Hand-written AFTER the raw generator output (`Gen4H6PbDec.lean`, `p2dec --gen4`, exit 0,
3/3 walker-covered) was committed. Statement = the pre-committed hand statement `E2eScal.H6.pb_accept_stmt`
(`H6Stmt.lean`, unchanged). `--gen4 --compose` refuses by design, so every field composition is HAND text
(`pb_gg_*_field`) over the GENERATED theorems, used as emitted:
* head 0–12: `dechead_seg` (`Compose.lean`, frame `0x20`, size 96);
* BlockHash 13–46: generated segment (offset-0 form) + generated tail steps 37, 38, 45, 46;
* ParentHash 47–82: generated segment + generated tail steps 73, 74, 81, 82;
* TotalDifficulty 83–118: generated segment + generated tail steps 109, 110, 117, 118;
* epilogue 119–123: `decepi_seg` (`Compose.lean`).
-/

open Fk E2eScal.H6Code E2eScal
variable [Host]

namespace E2eScal.H6

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
/-- `BlockHash`: the WHOLE byte field 13–46 (generated segment, then the generated tail steps 37, 38, 45, 46). -/
theorem pb_gg_BlockHash_field (k : Nat) (hk : PbUnmarshal.IsInfixAt Host.prog k) (hf : LabelsFresh PbUnmarshal k) :
    ∀
    (sp rcv bf aR aB aS aRet aLo aP aL aC : BitVec 64) (St : Nat)
    (hR : sp + (48 : Int64).toBitVec = aR) (hB' : sp + (56 : Int64).toBitVec = aB) (hS : sp + (24 : Int64).toBitVec = aS)
    (hRet : sp - 8 = aRet) (hLo : sp - 8 - BitVec.ofNat 64 St = aLo)
    (hP : rcv + (0 : Int64).toBitVec = aP) (hL : rcv + (8 : Int64).toBitVec = aL) (hC : rcv + (16 : Int64).toBitVec = aC)
    (rbp0 r140 : UInt64) (root : List UInt8) (hroot : root.length = 32)
    (spl rslot lo lS vP vL vC : List UInt8)
    (hspl : spl.length = 24) (hrs : rslot.length = 8) (hlo : lo.length = St) (hlS : lS.length = 8)
    (hvP : vP.length = 8) (hvL : vL.length = 8) (hvC : vC.length = 8)
    (R : DataMem → Prop) (Heap : Nat → DataMem → Prop) (avail : Nat) (hav : 32 ≤ avail)
    (s : MachineData) (hrsp : s.regs.rsp = { toBitVec := sp }) (hrbp : s.regs.rbp = rbp0)
    (hr14 : s.regs.r14 = r140)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 rcv.toInt).At aR) ⋆ Eq ((Int.toBytes 8 bf.toInt).At aB)
      ⋆ Eq (spl.At sp) ⋆ Eq (rslot.At aRet) ⋆ Eq (lo.At aLo) ⋆ Eq (lS.At aS)
      ⋆ Heap avail
      ⋆ Eq (vP.At aP) ⋆ Eq (vL.At aL) ⋆ Eq (vC.At aC)
      ⋆ Eq (root.At bf)
      ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R)
    (hms : MakesliceC Heap E2e.Data.e2eU8Type_addr 1 St) (hmm : MemmoveC St),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 47) ∧ st.data.regs.rsp = { toBitVec := sp }
        ∧ st.data.regs.rbp = rbp0 ∧ st.data.regs.r14 = r140 ∧
        ∃ (p : BitVec 64) (spl' lo' : List UInt8), spl'.length = 24 ∧ lo'.length = St
          ∧ st.data.regs.get64 Reg64.rdx = rcv ∧
        (Eq ((Int.toBytes 8 rcv.toInt).At aR) ⋆ Eq ((Int.toBytes 8 bf.toInt).At aB)
          ⋆ Eq (spl'.At sp)
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 31 + 1)).toBitVec.toInt).At aRet)
          ⋆ Eq (lo'.At aLo)
          ⋆ Eq ((Int.toBytes 8 p.toInt).At aS)
          ⋆ Heap (avail - 32)
          ⋆ Eq ((Int.toBytes 8 p.toInt).At aP) ⋆ Eq ((Int.toBytes 8 32).At aL)
          ⋆ Eq ((Int.toBytes 8 32).At aC) ⋆ Eq (root.At p)
          ⋆ Eq (root.At bf)
          ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf (k + 13)⟩ := by
  intro sp rcv bf aR aB aS aRet aLo aP aL aC St hR hB' hS hRet hLo hP hL hC rbp0 r140 root hroot spl rslot lo lS vP vL vC hspl hrs hlo hlS hvP hvL hvC R Heap avail hav s hrsp hrbp hr14 h_mem hms hmm
  refine eventually_trans _ _ _ _ (Gen.pb_g4dec_BlockHash_seg k hk hf sp rcv bf aR aB aS aRet aLo aP aL aC St hR hB' hS hRet hLo hP hL hC rbp0 r140 root hroot spl rslot lo lS vP vL vC hspl hrs hlo hlS hvP hvL hvC R Heap avail hav s hrsp hrbp hr14 h_mem hms hmm) ?_
  rintro ⟨d, pc⟩ ⟨hpc, hrsp', hrbp', hr14', p, spl', lo', hspl', hlo', hrY, Hm⟩
  dsimp only at hpc hrsp' hrbp' hr14' hrY Hm
  subst hpc
  obtain ⟨⟨rax1, rbx1, rcx1, rdx1, rsi1, rdi1, rsp1, rbp1, r81, r91, r101, r111, r121, r131, r141, r151⟩, zmms1, flags1, mem1⟩ := d
  simp only at hrsp' hrbp' hr14' hrY Hm
  subst hrsp' hrbp' hr14'
  apply Gen.pb_g4dec_s37 k hk hf sp aS p hS _ _ _ (by rfl) (by ecancel)
  kn
  apply Gen.pb_g4dec_s38 k hk hf
  apply Gen.pb_g4dec_s45 k hk hf
  apply Gen.pb_g4dec_s46 k hk hf rcv aP hP (Int.toBytes 8 p.toInt) (Int.toBytes_length 8 _) _ _ _ (by exact hrY) (by ecancel)
  intro m' H
  kn
  simp only [Reg64s.get64] at H
  apply Eventually.done
  refine ⟨rfl, rfl, rfl, rfl, p, spl', lo', hspl', hlo', hrY, ?_⟩
  dsimp only
  ecancel

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
/-- `ParentHash`: the WHOLE byte field 47–82 (generated segment, then the generated tail steps 73, 74, 81, 82). -/
theorem pb_gg_ParentHash_field (k : Nat) (hk : PbUnmarshal.IsInfixAt Host.prog k) (hf : LabelsFresh PbUnmarshal k) :
    ∀
    (sp rcv bf aR aB aS aRet aLo aP aL aC aSrc : BitVec 64) (St : Nat)
    (hR : sp + (48 : Int64).toBitVec = aR) (hB' : sp + (56 : Int64).toBitVec = aB) (hS : sp + (24 : Int64).toBitVec = aS)
    (hRet : sp - 8 = aRet) (hLo : sp - 8 - BitVec.ofNat 64 St = aLo)
    (hP : rcv + (24 : Int64).toBitVec = aP) (hL : rcv + (32 : Int64).toBitVec = aL) (hC : rcv + (40 : Int64).toBitVec = aC)
    (hSrc : bf + (32 : Int64).toBitVec = aSrc)
    (rbp0 r140 : UInt64) (root : List UInt8) (hroot : root.length = 32)
    (spl rslot lo lS vP vL vC : List UInt8)
    (hspl : spl.length = 24) (hrs : rslot.length = 8) (hlo : lo.length = St) (hlS : lS.length = 8)
    (hvP : vP.length = 8) (hvL : vL.length = 8) (hvC : vC.length = 8)
    (R : DataMem → Prop) (Heap : Nat → DataMem → Prop) (avail : Nat) (hav : 32 ≤ avail)
    (s : MachineData) (hrsp : s.regs.rsp = { toBitVec := sp }) (hrbp : s.regs.rbp = rbp0)
    (hr14 : s.regs.r14 = r140)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 rcv.toInt).At aR) ⋆ Eq ((Int.toBytes 8 bf.toInt).At aB)
      ⋆ Eq (spl.At sp) ⋆ Eq (rslot.At aRet) ⋆ Eq (lo.At aLo) ⋆ Eq (lS.At aS)
      ⋆ Heap avail
      ⋆ Eq (vP.At aP) ⋆ Eq (vL.At aL) ⋆ Eq (vC.At aC)
      ⋆ Eq (root.At aSrc)
      ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R)
    (hms : MakesliceC Heap E2e.Data.e2eU8Type_addr 1 St) (hmm : MemmoveC St),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 83) ∧ st.data.regs.rsp = { toBitVec := sp }
        ∧ st.data.regs.rbp = rbp0 ∧ st.data.regs.r14 = r140 ∧
        ∃ (p : BitVec 64) (spl' lo' : List UInt8), spl'.length = 24 ∧ lo'.length = St
          ∧ st.data.regs.get64 Reg64.rdx = rcv ∧
        (Eq ((Int.toBytes 8 rcv.toInt).At aR) ⋆ Eq ((Int.toBytes 8 bf.toInt).At aB)
          ⋆ Eq (spl'.At sp)
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 67 + 1)).toBitVec.toInt).At aRet)
          ⋆ Eq (lo'.At aLo)
          ⋆ Eq ((Int.toBytes 8 p.toInt).At aS)
          ⋆ Heap (avail - 32)
          ⋆ Eq ((Int.toBytes 8 p.toInt).At aP) ⋆ Eq ((Int.toBytes 8 32).At aL)
          ⋆ Eq ((Int.toBytes 8 32).At aC) ⋆ Eq (root.At p)
          ⋆ Eq (root.At aSrc)
          ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf (k + 47)⟩ := by
  intro sp rcv bf aR aB aS aRet aLo aP aL aC aSrc St hR hB' hS hRet hLo hP hL hC hSrc rbp0 r140 root hroot spl rslot lo lS vP vL vC hspl hrs hlo hlS hvP hvL hvC R Heap avail hav s hrsp hrbp hr14 h_mem hms hmm
  refine eventually_trans _ _ _ _ (Gen.pb_g4dec_ParentHash_seg k hk hf sp rcv bf aR aB aS aRet aLo aP aL aC aSrc St hR hB' hS hRet hLo hP hL hC hSrc rbp0 r140 root hroot spl rslot lo lS vP vL vC hspl hrs hlo hlS hvP hvL hvC R Heap avail hav s hrsp hrbp hr14 h_mem hms hmm) ?_
  rintro ⟨d, pc⟩ ⟨hpc, hrsp', hrbp', hr14', p, spl', lo', hspl', hlo', hrY, Hm⟩
  dsimp only at hpc hrsp' hrbp' hr14' hrY Hm
  subst hpc
  obtain ⟨⟨rax1, rbx1, rcx1, rdx1, rsi1, rdi1, rsp1, rbp1, r81, r91, r101, r111, r121, r131, r141, r151⟩, zmms1, flags1, mem1⟩ := d
  simp only at hrsp' hrbp' hr14' hrY Hm
  subst hrsp' hrbp' hr14'
  apply Gen.pb_g4dec_s73 k hk hf sp aS p hS _ _ _ (by rfl) (by ecancel)
  kn
  apply Gen.pb_g4dec_s74 k hk hf
  apply Gen.pb_g4dec_s81 k hk hf
  apply Gen.pb_g4dec_s82 k hk hf rcv aP hP (Int.toBytes 8 p.toInt) (Int.toBytes_length 8 _) _ _ _ (by exact hrY) (by ecancel)
  intro m' H
  kn
  simp only [Reg64s.get64] at H
  apply Eventually.done
  refine ⟨rfl, rfl, rfl, rfl, p, spl', lo', hspl', hlo', hrY, ?_⟩
  dsimp only
  ecancel

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
/-- `TotalDifficulty`: the WHOLE byte field 83–118 (generated segment, then the generated tail steps 109, 110, 117, 118). -/
theorem pb_gg_TotalDifficulty_field (k : Nat) (hk : PbUnmarshal.IsInfixAt Host.prog k) (hf : LabelsFresh PbUnmarshal k) :
    ∀
    (sp rcv bf aR aB aS aRet aLo aP aL aC aSrc : BitVec 64) (St : Nat)
    (hR : sp + (48 : Int64).toBitVec = aR) (hB' : sp + (56 : Int64).toBitVec = aB) (hS : sp + (24 : Int64).toBitVec = aS)
    (hRet : sp - 8 = aRet) (hLo : sp - 8 - BitVec.ofNat 64 St = aLo)
    (hP : rcv + (48 : Int64).toBitVec = aP) (hL : rcv + (56 : Int64).toBitVec = aL) (hC : rcv + (64 : Int64).toBitVec = aC)
    (hSrc : bf + (64 : Int64).toBitVec = aSrc)
    (rbp0 r140 : UInt64) (root : List UInt8) (hroot : root.length = 32)
    (spl rslot lo lS vP vL vC : List UInt8)
    (hspl : spl.length = 24) (hrs : rslot.length = 8) (hlo : lo.length = St) (hlS : lS.length = 8)
    (hvP : vP.length = 8) (hvL : vL.length = 8) (hvC : vC.length = 8)
    (R : DataMem → Prop) (Heap : Nat → DataMem → Prop) (avail : Nat) (hav : 32 ≤ avail)
    (s : MachineData) (hrsp : s.regs.rsp = { toBitVec := sp }) (hrbp : s.regs.rbp = rbp0)
    (hr14 : s.regs.r14 = r140)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 rcv.toInt).At aR) ⋆ Eq ((Int.toBytes 8 bf.toInt).At aB)
      ⋆ Eq (spl.At sp) ⋆ Eq (rslot.At aRet) ⋆ Eq (lo.At aLo) ⋆ Eq (lS.At aS)
      ⋆ Heap avail
      ⋆ Eq (vP.At aP) ⋆ Eq (vL.At aL) ⋆ Eq (vC.At aC)
      ⋆ Eq (root.At aSrc)
      ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R)
    (hms : MakesliceC Heap E2e.Data.e2eU8Type_addr 1 St) (hmm : MemmoveC St),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 119) ∧ st.data.regs.rsp = { toBitVec := sp }
        ∧ st.data.regs.rbp = rbp0 ∧ st.data.regs.r14 = r140 ∧
        ∃ (p : BitVec 64) (spl' lo' : List UInt8), spl'.length = 24 ∧ lo'.length = St
          ∧ st.data.regs.get64 Reg64.rdx = rcv ∧
        (Eq ((Int.toBytes 8 rcv.toInt).At aR) ⋆ Eq ((Int.toBytes 8 bf.toInt).At aB)
          ⋆ Eq (spl'.At sp)
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 103 + 1)).toBitVec.toInt).At aRet)
          ⋆ Eq (lo'.At aLo)
          ⋆ Eq ((Int.toBytes 8 p.toInt).At aS)
          ⋆ Heap (avail - 32)
          ⋆ Eq ((Int.toBytes 8 p.toInt).At aP) ⋆ Eq ((Int.toBytes 8 32).At aL)
          ⋆ Eq ((Int.toBytes 8 32).At aC) ⋆ Eq (root.At p)
          ⋆ Eq (root.At aSrc)
          ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf (k + 83)⟩ := by
  intro sp rcv bf aR aB aS aRet aLo aP aL aC aSrc St hR hB' hS hRet hLo hP hL hC hSrc rbp0 r140 root hroot spl rslot lo lS vP vL vC hspl hrs hlo hlS hvP hvL hvC R Heap avail hav s hrsp hrbp hr14 h_mem hms hmm
  refine eventually_trans _ _ _ _ (Gen.pb_g4dec_TotalDifficulty_seg k hk hf sp rcv bf aR aB aS aRet aLo aP aL aC aSrc St hR hB' hS hRet hLo hP hL hC hSrc rbp0 r140 root hroot spl rslot lo lS vP vL vC hspl hrs hlo hlS hvP hvL hvC R Heap avail hav s hrsp hrbp hr14 h_mem hms hmm) ?_
  rintro ⟨d, pc⟩ ⟨hpc, hrsp', hrbp', hr14', p, spl', lo', hspl', hlo', hrY, Hm⟩
  dsimp only at hpc hrsp' hrbp' hr14' hrY Hm
  subst hpc
  obtain ⟨⟨rax1, rbx1, rcx1, rdx1, rsi1, rdi1, rsp1, rbp1, r81, r91, r101, r111, r121, r131, r141, r151⟩, zmms1, flags1, mem1⟩ := d
  simp only at hrsp' hrbp' hr14' hrY Hm
  subst hrsp' hrbp' hr14'
  apply Gen.pb_g4dec_s109 k hk hf sp aS p hS _ _ _ (by rfl) (by ecancel)
  kn
  apply Gen.pb_g4dec_s110 k hk hf
  apply Gen.pb_g4dec_s117 k hk hf
  apply Gen.pb_g4dec_s118 k hk hf rcv aP hP (Int.toBytes 8 p.toInt) (Int.toBytes_length 8 _) _ _ _ (by exact hrY) (by ecancel)
  intro m' H
  kn
  simp only [Reg64s.get64] at H
  apply Eventually.done
  refine ⟨rfl, rfl, rfl, rfl, p, spl', lo', hspl', hlo', hrY, ?_⟩
  dsimp only
  ecancel

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
/-- **Accept path of the real `(*v1alpha1.PowBlock).UnmarshalSSZ` (Go 1.26.10) from the generated `p2dec --gen4` chains**;
statement = the hand statement `pb_accept_stmt` (unchanged). -/
theorem pb_e2e_accept_g4gen : pb_accept_stmt := by
  intro k hk hf bh ph td hbh hph htd s ra guard
    fp s1 s2 spl l18 rslot lo aP1 aL1 aC1 aP2 aL2 aC2 aP3 aL3 aC3
    hfp h1 h2 hspl hl18 hrs haP1 haL1 haC1 haP2 haL2 haC2 haP3 haL3 haC3
    R S hlo Heap avail h_mem hguard hlen hav hms hmm
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hguard hlen ⊢
  have hrsp_lt : rsp.toNat < 2 ^ 64 := rsp.toNat_lt_size
  have hH := E2eScal.infix_sub (q := E2eScal.decHead "github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PowBlock.UnmarshalSSZ" "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PowBlock.UnmarshalSSZ_0" "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PowBlock.UnmarshalSSZ_224" "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PowBlock.UnmarshalSSZ_210" 96) 0 hk
    (by simp only [PbUnmarshal, E2eScal.decHead, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero])
  have hE := E2eScal.infix_sub (q := E2eScal.decEpi) 119 hk
    (by simp only [PbUnmarshal, E2eScal.decEpi, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero])
  -- head: entry → directive 13
  refine eventually_trans _ _ _ _ (E2eScal.dechead_seg _ _ _ _ 96 (k + 0) hH _ ra guard fp s1 s2 hfp h1 h2 _
    (by dsimp only; ecancel) hguard (by rw [hlen]; rfl)) ?_
  rintro ⟨d1, pc1⟩ ⟨hpc1, hrsp1, hrbp1, hr141, hrax1, hrbx1, Hm1⟩
  dsimp only at hpc1 hrsp1 hrbp1 hr141 hrax1 hrbx1 Hm1
  subst hpc1
  -- BlockHash: 13 → 47 (hand field composition: generated segment + generated tail steps)
  refine eventually_trans _ _ _ _ (pb_gg_BlockHash_field k hk hf
    (rsp.toBitVec - 40) rax.toBitVec rbx.toBitVec
    (rsp.toBitVec + 8) (rsp.toBitVec + 16) (rsp.toBitVec - 16) (rsp.toBitVec - 48)
    (rsp.toBitVec - 48 - BitVec.ofNat 64 S) rax.toBitVec (rax.toBitVec + 8) (rax.toBitVec + 16) S
    (by simp only [Int64.toBitVec_ofNat]; bv_omega) (by simp only [Int64.toBitVec_ofNat]; bv_omega)
    (by simp only [Int64.toBitVec_ofNat]; bv_omega) (by bv_omega) (E2eScal.E1.e1_lo _ _)
    (by simp only [Int64.toBitVec_ofNat]; bv_omega) (by simp only [Int64.toBitVec_ofNat])
    (by simp only [Int64.toBitVec_ofNat])
    (rsp - 8) r14 bh hbh spl rslot lo l18 aP1 aL1 aC1 hspl hrs hlo hl18 haP1 haL1 haC1
    _ Heap avail (by omega) d1
    (by rw [hrsp1]; first | rfl | (apply UInt64.toBitVec_inj.mp; simp))
    (by rw [hrbp1]) hr141
    (by ecancel) hms hmm) ?_
  rintro ⟨d2, pc2⟩ ⟨hpc2, hrsp2, hrbp2, hr142, p1, spl1, lo1, hspl1, hlo1, hrdx2, Hm2⟩
  dsimp only at hpc2 hrsp2 hrbp2 hr142 hrdx2 Hm2
  subst hpc2
  -- ParentHash: 47 → 83
  refine eventually_trans _ _ _ _ (pb_gg_ParentHash_field k hk hf
    (rsp.toBitVec - 40) rax.toBitVec rbx.toBitVec
    (rsp.toBitVec + 8) (rsp.toBitVec + 16) (rsp.toBitVec - 16) (rsp.toBitVec - 48)
    (rsp.toBitVec - 48 - BitVec.ofNat 64 S) (rax.toBitVec + 24) (rax.toBitVec + 32) (rax.toBitVec + 40)
    (rbx.toBitVec + 32) S
    (by simp only [Int64.toBitVec_ofNat]; bv_omega) (by simp only [Int64.toBitVec_ofNat]; bv_omega)
    (by simp only [Int64.toBitVec_ofNat]; bv_omega) (by bv_omega) (E2eScal.E1.e1_lo _ _)
    (by simp only [Int64.toBitVec_ofNat]) (by simp only [Int64.toBitVec_ofNat])
    (by simp only [Int64.toBitVec_ofNat]) (by simp only [Int64.toBitVec_ofNat])
    (rsp - 8) r14 ph hph spl1 (Int.toBytes 8 (Host.addrOf (k + 31 + 1)).toBitVec.toInt) lo1 (Int.toBytes 8 p1.toInt)
    aP2 aL2 aC2 hspl1 (Int.toBytes_length 8 _) hlo1 (Int.toBytes_length 8 _) haP2 haL2 haC2
    _ Heap (avail - 32) (by omega) d2 hrsp2 hrbp2 hr142 (by ecancel) hms hmm) ?_
  rintro ⟨d3, pc3⟩ ⟨hpc3, hrsp3, hrbp3, hr143, p2, spl2, lo2, hspl2, hlo2, hrdx3, Hm3⟩
  dsimp only at hpc3 hrsp3 hrbp3 hr143 hrdx3 Hm3
  subst hpc3
  -- TotalDifficulty: 83 → 119
  refine eventually_trans _ _ _ _ (pb_gg_TotalDifficulty_field k hk hf
    (rsp.toBitVec - 40) rax.toBitVec rbx.toBitVec
    (rsp.toBitVec + 8) (rsp.toBitVec + 16) (rsp.toBitVec - 16) (rsp.toBitVec - 48)
    (rsp.toBitVec - 48 - BitVec.ofNat 64 S) (rax.toBitVec + 48) (rax.toBitVec + 56) (rax.toBitVec + 64)
    (rbx.toBitVec + 64) S
    (by simp only [Int64.toBitVec_ofNat]; bv_omega) (by simp only [Int64.toBitVec_ofNat]; bv_omega)
    (by simp only [Int64.toBitVec_ofNat]; bv_omega) (by bv_omega) (E2eScal.E1.e1_lo _ _)
    (by simp only [Int64.toBitVec_ofNat]) (by simp only [Int64.toBitVec_ofNat])
    (by simp only [Int64.toBitVec_ofNat]) (by simp only [Int64.toBitVec_ofNat])
    (rsp - 8) r14 td htd spl2 (Int.toBytes 8 (Host.addrOf (k + 67 + 1)).toBitVec.toInt) lo2 (Int.toBytes 8 p2.toInt)
    aP3 aL3 aC3 hspl2 (Int.toBytes_length 8 _) hlo2 (Int.toBytes_length 8 _) haP3 haL3 haC3
    _ Heap (avail - 32 - 32) (by omega) d3 hrsp3 hrbp3 hr143 (by ecancel) hms hmm) ?_
  rintro ⟨d4, pc4⟩ ⟨hpc4, hrsp4, hrbp4, hr144, p3, spl3, lo3, hspl3, hlo3, hrdx4, Hm4⟩
  dsimp only at hpc4 hrsp4 hrbp4 hr144 hrdx4 Hm4
  subst hpc4
  -- epilogue 119–123
  refine eventually_trans _ _ _ _ (E2eScal.decepi_seg (k + 119) hE (rsp.toBitVec - 40) (rsp.toBitVec - 8) rsp.toBitVec
    (by bv_omega) (by bv_omega) rbp ra r14 _ d4 hrsp4 hr144 (by ecancel)) ?_
  rintro ⟨d5, pc5⟩ ⟨hpc5, hrax5, hrbx5, hrsp5, hrbp5, hr145, Hm5⟩
  dsimp only at hpc5 hrax5 hrbx5 hrsp5 hrbp5 hr145 Hm5
  apply Eventually.done
  rw [show k + 103 + 1 = k + 104 from rfl, show avail - 32 - 32 - 32 = avail - 96 by omega] at Hm5
  refine ⟨hpc5, hrax5, hrbx5, ?_, hrbp5, hr145, p1, p2, p3, spl3, lo3, hspl3, hlo3, ?_⟩
  · dsimp only; rw [hrsp5]; apply UInt64.toBitVec_inj.mp
    simp only [UInt64.toBitVec_add, UInt64.toBitVec_ofNat]; bv_omega
  · dsimp only; ecancel

end E2eScal.H6
