import E2eScal.PcAccept
import E2eScal.Gen4PcDec
import E2eScal.H5Stmt

/-!
# `(*v1alpha1.PendingConsolidation).UnmarshalSSZ`, accept path from the GENERATED `p2dec --gen4` chains

`pc_e2e_accept_g4gen : H5.pc_accept_stmt` (the pre-committed hand statement, unchanged). Both fields are HAND field
compositions (`pc_gg_*_field`; no kind exists for a field composition) over the GENERATED theorems of
`Gen4PcDec.lean` (`p2dec --gen4`, raw output): SourceIndex = generated steps 15, 16 + call block; TargetIndex =
generated steps 48–54 + the call WINDOW 55–58 with the `nop` after the `callq`. Hand text that remains: the two field
compositions, `pc_head`, `pc_epi` (`PcAccept.lean`) and the glue. In-sample (development data); no transfer claim.
-/

open Fk E2e E2eScal.H5Code E2eScal.BhCode E2eScal
variable [Host]

namespace E2eScal.H5

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- `SourceIndex`: the WHOLE call field 15–47 (generated steps 15, 16 and the generated call block 17–19, label 47). -/
theorem pc_gg_SourceIndex_field (k : Nat) (hk : PcUnmarshal.IsInfixAt Host.prog k) (hf : LabelsFresh PcUnmarshal k) :
    ∀ (hC : U64CalleeAcc "github.com_OffchainLabs_prysm_v7_consensus_types_primitives.ValidatorIndex.UnmarshalSSZ")
    (sp rcv bf aRet aFp aS2 : BitVec 64)
    (hRet : sp - 8 = aRet) (hFp : sp - 16 = aFp) (hS2 : sp + 8 = aS2)
    (rbp0 r140 guard : UInt64) (e8 rslot fp s2 c0 : List UInt8)
    (he8 : e8.length = 8) (hrs : rslot.length = 8) (hfp : fp.length = 8) (hs2 : s2.length = 8)
    (hc0 : c0.length = 8) (hguard : guard.toNat < aRet.toNat)
    (F : DataMem → Prop)
    (s : MachineData) (hrsp : s.regs.rsp = { toBitVec := sp }) (hrbp : s.regs.rbp = rbp0)
    (hr14 : s.regs.r14 = r140) (hrax : s.regs.rax.toBitVec = rcv) (hrbx : s.regs.rbx.toBitVec = bf)
    (h_mem : s.dmem =⋆ Eq (rslot.At aRet) ⋆ Eq (fp.At aFp) ⋆ Eq (s2.At aS2)
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (r140.toBitVec + 16))
      ⋆ Eq (e8.At bf) ⋆ Eq (c0.At (rcv + 8)) ⋆ F),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 47 + 1) ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0
        ∧ st.data.regs.rsp = { toBitVec := sp } ∧ st.data.regs.rbp = rbp0 ∧ st.data.regs.r14 = r140 ∧
        (Eq ((Int.toBytes 8 (Host.addrOf (k + 17 + 1)).toBitVec.toInt).At aRet)
          ⋆ Eq ((Int.toBytes 8 rbp0.toBitVec.toInt).At aFp) ⋆ Eq ((Int.toBytes 8 bf.toInt).At aS2)
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (r140.toBitVec + 16))
          ⋆ Eq (e8.At bf) ⋆ Eq (e8.At (rcv + 8)) ⋆ F) st.data.dmem)
      ⟨s, Host.addrOf (k + 15)⟩ := by
  intro hC sp rcv bf aRet aFp aS2 hRet hFp hS2 rbp0 r140 guard e8 rslot fp s2 c0 he8 hrs hfp hs2 hc0
    hguard F s hrsp hrbp hr14 hrax hrbx h_mem
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at hrsp hrbp hr14 hrax hrbx h_mem ⊢
  subst rsp rbp r14 hrax hrbx
  apply Gen.pc_g4dec_s15 k hk hf
  intro fl1; kn
  apply Gen.pc_g4dec_s16 k hk hf
  kn
  refine eventually_trans _ _ _ _ (Gen.pc_g4dec_SourceIndex_call k hk hf hC sp (rax.toBitVec + 8) rbx.toBitVec aRet aFp aS2 hRet hFp hS2 rbp0 r140 guard e8 rslot
    fp s2 c0 he8 hrs hfp hs2 hc0 hguard _ _ (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by first | rfl | decide)
    (by ecancel)) ?_
  rintro ⟨d, pc⟩ ⟨hpc, hrax', hrbx', hrsp', hrbp', hr14', Hm⟩
  dsimp only at hpc hrax' hrbx' hrsp' hrbp' hr14' Hm
  apply Eventually.done
  refine ⟨hpc, hrax', hrbx', hrsp', hrbp', hr14', ?_⟩
  dsimp only
  ecancel

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- `TargetIndex` (callee decoder field, Go offset 16, SSZ offset 8): the WHOLE call field 48–85, composed from the
step theorems of its set-up and the call-block theorem (worked example of the `p2dec --gen4` emission recipe). The entry
conditions of the call block (rax = `rcv + 16`, rbx = `bf + 8`, rcx = 8) are closed by `rfl` on the state
that the steps computed. -/
theorem pc_gg_TargetIndex_field (k : Nat) (hk : PcUnmarshal.IsInfixAt Host.prog k) (hf : LabelsFresh PcUnmarshal k) :
    ∀ (hC : U64CalleeAcc "github.com_OffchainLabs_prysm_v7_consensus_types_primitives.ValidatorIndex.UnmarshalSSZ")
    (sp rcv bf aRet aFp aS2 aB aD aR : BitVec 64)
    (hRet : sp - 8 = aRet) (hFp : sp - 16 = aFp) (hS2 : sp + 8 = aS2)
    (hB : sp + (96 : Int64).toBitVec = aB) (hD : sp + (112 : Int64).toBitVec = aD) (hR : sp + (88 : Int64).toBitVec = aR)
    (rbp0 r140 guard : UInt64) (e8 rslot fp s2 c0 vD : List UInt8)
    (he8 : e8.length = 8) (hrs : rslot.length = 8) (hfp : fp.length = 8) (hs2 : s2.length = 8)
    (hc0 : c0.length = 8) (hvD : vD.length = 8) (hguard : guard.toNat < aRet.toNat)
    (F : DataMem → Prop)
    (s : MachineData) (hrsp : s.regs.rsp = { toBitVec := sp }) (hrbp : s.regs.rbp = rbp0)
    (hr14 : s.regs.r14 = r140)
    (h_mem : s.dmem =⋆ Eq (rslot.At aRet) ⋆ Eq (fp.At aFp) ⋆ Eq (s2.At aS2)
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (r140.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 bf.toInt).At aB) ⋆ Eq (vD.At aD) ⋆ Eq ((Int.toBytes 8 rcv.toInt).At aR)
      ⋆ Eq (e8.At (bf + 8)) ⋆ Eq (c0.At (rcv + 16)) ⋆ F),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 85 + 1) ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0
        ∧ st.data.regs.rsp = { toBitVec := sp } ∧ st.data.regs.rbp = rbp0 ∧ st.data.regs.r14 = r140 ∧
        (Eq ((Int.toBytes 8 (Host.addrOf (k + 55 + 1)).toBitVec.toInt).At aRet)
          ⋆ Eq ((Int.toBytes 8 rbp0.toBitVec.toInt).At aFp) ⋆ Eq ((Int.toBytes 8 (bf + 8).toInt).At aS2)
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (r140.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 bf.toInt).At aB) ⋆ Eq (vD.At aD) ⋆ Eq ((Int.toBytes 8 rcv.toInt).At aR)
          ⋆ Eq (e8.At (bf + 8)) ⋆ Eq (e8.At (rcv + 16)) ⋆ F) st.data.dmem)
      ⟨s, Host.addrOf (k + 48)⟩ := by
  intro hC sp rcv bf aRet aFp aS2 aB aD aR hRet hFp hS2 hB hD hR rbp0 r140 guard e8 rslot fp s2 c0 vD he8 hrs hfp hs2 hc0 hvD
    hguard F s hrsp hrbp hr14 h_mem
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at hrsp hrbp hr14 h_mem ⊢
  subst rsp rbp r14
  apply Gen.pc_g4dec_s48 k hk hf sp aB bf hB _ _ _ (by rfl) (by ecancel)
  kn
  apply Gen.pc_g4dec_s49 k hk hf
  intro fl1; kn
  apply Gen.pc_g4dec_s50 k hk hf sp aD hD vD hvD _ _ _ (by rfl) (by ecancel)
  kn
  apply Gen.pc_g4dec_s51 k hk hf
  intro fl2; kn
  apply Gen.pc_g4dec_s52 k hk hf sp aR rcv hR _ _ _ (by rfl) (by ecancel)
  kn
  apply Gen.pc_g4dec_s53 k hk hf
  intro fl3; kn
  apply Gen.pc_g4dec_s54 k hk hf
  kn
  refine eventually_trans _ _ _ _ (Gen.pc_g4dec_TargetIndex_call k hk hf hC sp (rcv + 16) (bf + 8) aRet aFp aS2 hRet hFp hS2 rbp0 r140 guard e8 rslot
    fp s2 c0 he8 hrs hfp hs2 hc0 hguard _ _ (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by first | rfl | decide)
    (by ecancel)) ?_
  rintro ⟨d, pc⟩ ⟨hpc, hrax', hrbx', hrsp', hrbp', hr14', Hm⟩
  dsimp only at hpc hrax' hrbx' hrsp' hrbp' hr14' Hm
  apply Eventually.done
  refine ⟨hpc, hrax', hrbx', hrsp', hrbp', hr14', ?_⟩
  dsimp only
  ecancel

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
/-- **Accept path of the real `(*v1alpha1.PendingConsolidation).UnmarshalSSZ` (Go 1.26.10) from the generated `p2dec --gen4`
chains**; statement = the hand statement `pc_accept_stmt` (unchanged). -/
theorem pc_e2e_accept_g4gen : pc_accept_stmt := by
  intro k hk hf kV hkV hfV in0 in1 hin0 hin1 s ra guard
    fp s1 s2 s4 sp1 rslot lo ast a8 a16 hfp h1 h2 h4 hsp1 hrs hlo hast ha8 ha16 R h_mem hguard hlen
  have hvi : U64CalleeAcc viLabel := vi_uacc_holds kV hkV hfV
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hguard hlen ⊢
  have hg : guard.toNat < (rsp.toBitVec - 88).toNat := E2eScal.H4.pwa_guard _ _ hguard
  -- head: entry → directive 15
  refine eventually_trans _ _ _ _ (pc_head k hk _ ra guard fp s1 s2 s4 ast hfp h1 h2 h4 hast _
    (by dsimp only; ecancel) (Nat.lt_of_le_of_lt (Nat.le_add_right _ 88) hguard) hlen) ?_
  rintro ⟨d1, pc1⟩ ⟨hpc1, hrsp1, hrbp1, hr141, hrax1, hrbx1, Hm1⟩
  dsimp only at hpc1 hrsp1 hrbp1 hr141 hrax1 hrbx1 Hm1
  subst hpc1
  -- SourceIndex: 15 → 48 (hand field composition over the generated steps 15, 16 and the generated call block)
  refine eventually_trans _ _ _ _ (pc_gg_SourceIndex_field k hk hf hvi
    (rsp.toBitVec - 80) rax.toBitVec rbx.toBitVec (rsp.toBitVec - 88) (rsp.toBitVec - 96) (rsp.toBitVec - 72)
    (by bv_omega) (by bv_omega) (by bv_omega)
    { toBitVec := rsp.toBitVec - 8 } r14 guard in0 rslot lo sp1 a8 hin0 hrs hlo hsp1 ha8 hg _ d1
    hrsp1 hrbp1 hr141 (by rw [hrax1]) (by rw [hrbx1]) (by ecancel)) ?_
  rintro ⟨d3, pc3⟩ ⟨hpc3, hrax3, hrbx3, hrsp3, hrbp3, hr143, Hm3⟩
  dsimp only at hpc3 hrax3 hrbx3 hrsp3 hrbp3 hr143 Hm3
  subst hpc3
  -- TargetIndex: 48 → 86 (hand field composition: generated steps 48–54 + generated call window with the nop)
  refine eventually_trans _ _ _ _ (pc_gg_TargetIndex_field k hk hf hvi
    (rsp.toBitVec - 80) rax.toBitVec rbx.toBitVec (rsp.toBitVec - 88) (rsp.toBitVec - 96) (rsp.toBitVec - 72)
    (rsp.toBitVec + 16) (rsp.toBitVec + 32) (rsp.toBitVec + 8)
    (by bv_omega) (by bv_omega) (by bv_omega)
    (by simp only [Int64.toBitVec_ofNat]; bv_omega) (by simp only [Int64.toBitVec_ofNat]; bv_omega)
    (by simp only [Int64.toBitVec_ofNat]; bv_omega)
    { toBitVec := rsp.toBitVec - 8 } r14 guard in1
    (Int.toBytes 8 (Host.addrOf (k + 17 + 1)).toBitVec.toInt) (Int.toBytes 8 (rsp.toBitVec - 8).toInt)
    (Int.toBytes 8 rbx.toBitVec.toInt) a16 (Int.toBytes 8 rdi.toBitVec.toInt)
    hin1 (Int.toBytes_length 8 _) (Int.toBytes_length 8 _) (Int.toBytes_length 8 _) ha16 (Int.toBytes_length 8 _)
    hg _ d3 hrsp3 hrbp3 hr143 (by ecancel)) ?_
  rintro ⟨d5, pc5⟩ ⟨hpc5, hrax5, hrbx5, hrsp5, hrbp5, hr145, Hm5⟩
  dsimp only at hpc5 hrax5 hrbx5 hrsp5 hrbp5 hr145 Hm5
  subst hpc5
  -- epilogue 86–88
  refine eventually_trans _ _ _ _ (pc_epi k hk (rsp.toBitVec - 80) (rsp.toBitVec - 8) rsp.toBitVec
    (by bv_omega) (by bv_omega) rbp ra _ d5 hrsp5 (by ecancel)) ?_
  rintro ⟨d6, pc6⟩ ⟨hpc6, hrax6, hrbx6, hrsp6, hrbp6, hr146, hmem6⟩
  dsimp only at hpc6 hrax6 hrbx6 hrsp6 hrbp6 hr146 hmem6
  apply Eventually.done
  rw [show k + 55 + 1 = k + 56 from rfl] at Hm5
  refine ⟨hpc6, hrax6.trans hrax5, hrbx6.trans hrbx5, ?_, hrbp6, hr146.trans hr145,
    Int.toBytes 8 (rbx.toBitVec + 8).toInt, Int.toBytes 8 (rsp.toBitVec - 8).toInt,
    Int.toBytes_length 8 _, Int.toBytes_length 8 _, ?_⟩
  · dsimp only; rw [hrsp6]; apply UInt64.toBitVec_inj.mp
    simp only [UInt64.toBitVec_add, UInt64.toBitVec_ofNat]; bv_omega
  · dsimp only; rw [hmem6]; ecancel

end E2eScal.H5
