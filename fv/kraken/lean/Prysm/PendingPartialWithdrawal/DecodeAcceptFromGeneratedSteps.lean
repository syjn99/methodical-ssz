import Prysm.PendingPartialWithdrawal.DecodeAccept
import Prysm.PendingPartialWithdrawal.GeneratedDecodeSteps

/-!
# PendingPartialWithdrawal accept path from the GENERATED `p2dec --gen4` chains

`Decode.accept_from_generated_steps : Decode.accept_statement` (the hand statement, `Prysm/Deposit_Data/Statements.lean`, unchanged). HAND field
compositions over the GENERATED theorems of `Prysm/PendingPartialWithdrawal/GeneratedDecodeSteps.lean` (`p2dec --gen4`, raw output): Index = generated steps 15,
16 + call block; Amount and WithdrawableEpoch = generated steps 48–58 (the uint64 read 54–55 inside the call set-up)
+ the generated call block 59–61. Hand text that remains: the field compositions, `Decode.head` / `Decode.epi`
(`Prysm/PendingPartialWithdrawal/DecodeAccept.lean`, frame `0x48`) and the glue. In-sample (development data); no transfer claim.
-/

open Machine Runtime Prysm.PendingPartialWithdrawal.Code Codec
variable [Host]

namespace Prysm.PendingPartialWithdrawal

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- `Index`: the WHOLE call field 15–47 (generated steps 15, 16 and the generated call block 17–19, label 47). -/
theorem Decode.from_generated_steps_Index_field (k : Nat) (hk : unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh unmarshalSSZ k) :
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
  apply Decode.generated_step_s15 k hk hf
  intro fl1; kn
  apply Decode.generated_step_s16 k hk hf
  kn
  refine eventually_trans _ _ _ _ (Decode.generated_step_Index_call k hk hf hC sp (rax.toBitVec + 8) rbx.toBitVec aRet aFp aS2 hRet hFp hS2 rbp0 r140 guard e8 rslot
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
/-- `Amount` and `WithdrawableEpoch`: the two fields 48–88 (the uint64 read of Amount, 54–55, lies inside the set-up
of WithdrawableEpoch): generated steps 48–58 and the generated call block 59–61, label 88. -/
theorem Decode.from_generated_steps_Amount_WithdrawableEpoch_fields (k : Nat) (hk : unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh unmarshalSSZ k) :
    ∀ (hC : U64CalleeAcc "github.com_OffchainLabs_prysm_v7_consensus_types_primitives.Epoch.UnmarshalSSZ")
    (sp rcv bf aRet aFp aS2 aB aD aR : BitVec 64)
    (hRet : sp - 8 = aRet) (hFp : sp - 16 = aFp) (hS2 : sp + 8 = aS2)
    (hB : sp + (96 : Int64).toBitVec = aB) (hD : sp + (112 : Int64).toBitVec = aD) (hR : sp + (88 : Int64).toBitVec = aR)
    (rbp0 r140 guard : UInt64) (e8 rslot fp s2 c0 vD v vF : List UInt8)
    (he8 : e8.length = 8) (hrs : rslot.length = 8) (hfp : fp.length = 8) (hs2 : s2.length = 8)
    (hc0 : c0.length = 8) (hvD : vD.length = 8) (hv : v.length = 8) (hvF : vF.length = 8)
    (hguard : guard.toNat < aRet.toNat)
    (F : DataMem → Prop)
    (s : MachineData) (hrsp : s.regs.rsp = { toBitVec := sp }) (hrbp : s.regs.rbp = rbp0)
    (hr14 : s.regs.r14 = r140)
    (h_mem : s.dmem =⋆ Eq (rslot.At aRet) ⋆ Eq (fp.At aFp) ⋆ Eq (s2.At aS2)
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (r140.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 bf.toInt).At aB) ⋆ Eq (vD.At aD) ⋆ Eq ((Int.toBytes 8 rcv.toInt).At aR)
      ⋆ Eq (v.At (bf + 8)) ⋆ Eq (vF.At (rcv + 16))
      ⋆ Eq (e8.At (bf + 16)) ⋆ Eq (c0.At (rcv + 24)) ⋆ F),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 88 + 1) ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0
        ∧ st.data.regs.rsp = { toBitVec := sp } ∧ st.data.regs.rbp = rbp0 ∧ st.data.regs.r14 = r140 ∧
        (Eq ((Int.toBytes 8 (Host.addrOf (k + 59 + 1)).toBitVec.toInt).At aRet)
          ⋆ Eq ((Int.toBytes 8 rbp0.toBitVec.toInt).At aFp) ⋆ Eq ((Int.toBytes 8 (bf + 16).toInt).At aS2)
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (r140.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 bf.toInt).At aB) ⋆ Eq (vD.At aD) ⋆ Eq ((Int.toBytes 8 rcv.toInt).At aR)
          ⋆ Eq (v.At (bf + 8)) ⋆ Eq (v.At (rcv + 16))
          ⋆ Eq (e8.At (bf + 16)) ⋆ Eq (e8.At (rcv + 24)) ⋆ F) st.data.dmem)
      ⟨s, Host.addrOf (k + 48)⟩ := by
  intro hC sp rcv bf aRet aFp aS2 aB aD aR hRet hFp hS2 hB hD hR rbp0 r140 guard e8 rslot fp s2 c0 vD v vF
    he8 hrs hfp hs2 hc0 hvD hv hvF hguard F s hrsp hrbp hr14 h_mem
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at hrsp hrbp hr14 h_mem ⊢
  subst rsp rbp r14
  apply Decode.generated_step_s48 k hk hf sp aB bf hB _ _ _ (by rfl) (by ecancel)
  kn
  apply Decode.generated_step_s49 k hk hf
  kn
  apply Decode.generated_step_s50 k hk hf sp aD hD vD hvD _ _ _ (by rfl) (by ecancel)
  kn
  apply Decode.generated_step_s51 k hk hf
  intro fl1; kn
  apply Decode.generated_step_s52 k hk hf sp aR rcv hR _ _ _ (by rfl) (by ecancel)
  kn
  apply Decode.generated_step_s53 k hk hf
  kn
  apply Decode.generated_step_s54 k hk hf bf (bf + 8) (by simp only [Int64.toBitVec_ofNat]) v hv _ _ _ (by rfl) (by ecancel)
  kn
  apply Decode.generated_step_s55 k hk hf rcv (rcv + 16) (by simp only [Int64.toBitVec_ofNat]) vF hvF _ _ _ (by rfl) (by ecancel)
  intro m' H
  kn
  simp only [Reg64s.get64, toBytes_ofInt_ofBytes 64 8 rfl v hv] at H
  apply Decode.generated_step_s56 k hk hf
  kn
  apply Decode.generated_step_s57 k hk hf
  kn
  apply Decode.generated_step_s58 k hk hf
  kn
  refine eventually_trans _ _ _ _ (Decode.generated_step_WithdrawableEpoch_call k hk hf hC sp (rcv + 24) (bf + 16) aRet aFp aS2 hRet hFp hS2 rbp0 r140
    guard e8 rslot fp s2 c0 he8 hrs hfp hs2 hc0 hguard _ _ (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
    (by first | rfl | decide) (by ecancel)) ?_
  rintro ⟨d, pc⟩ ⟨hpc, hrax', hrbx', hrsp', hrbp', hr14', Hm⟩
  dsimp only at hpc hrax' hrbx' hrsp' hrbp' hr14' Hm
  apply Eventually.done
  refine ⟨hpc, hrax', hrbx', hrsp', hrbp', hr14', ?_⟩
  dsimp only
  ecancel

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Accept path of `(*v1alpha1.PendingPartialWithdrawal).UnmarshalSSZ` from the GENERATED `p2dec --gen4` chains;
statement = the hand statement `Decode.accept_statement` (unchanged). -/
theorem Decode.accept_from_generated_steps : Decode.accept_statement := by
  intro k hk hf kV hkV hfV kE hkE hfE in0 in1 in2 hin0 hin1 hin2 s ra guard
    fp s1 s2 s4 sp1 rslot lo ast a8 a16 a24 hfp h1 h2 h4 hsp1 hrs hlo hast ha8 ha16 ha24 R h_mem hguard hlen
  have hvi : U64CalleeAcc Prysm.ValidatorIndex.Code.unmarshalLabel := Prysm.ValidatorIndex.Decode.accept_function_spec_holds kV hkV hfV
  have hep : U64CalleeAcc Prysm.Epoch.Code.unmarshalSSZLabel := Prysm.Epoch.Decode.accept_function_spec_holds kE hkE hfE
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hguard hlen ⊢
  have hg : guard.toNat < (rsp.toBitVec - 88).toNat := Decode.accept_guard _ _ hguard
  -- head: entry → directive 15
  refine eventually_trans _ _ _ _ (Decode.head k hk _ ra guard fp s1 s2 s4 ast hfp h1 h2 h4 hast _
    (by dsimp only; ecancel) (Nat.lt_of_le_of_lt (Nat.le_add_right _ 88) hguard) hlen) ?_
  rintro ⟨d1, pc1⟩ ⟨hpc1, hrsp1, hrbp1, hr141, hrax1, hrbx1, Hm1⟩
  dsimp only at hpc1 hrsp1 hrbp1 hr141 hrax1 hrbx1 Hm1
  subst hpc1
  -- Index: 15 → 48 (hand field composition over the generated steps 15, 16 and the generated call block)
  refine eventually_trans _ _ _ _ (Decode.from_generated_steps_Index_field k hk hf hvi
    (rsp.toBitVec - 80) rax.toBitVec rbx.toBitVec (rsp.toBitVec - 88) (rsp.toBitVec - 96) (rsp.toBitVec - 72)
    (by bv_omega) (by bv_omega) (by bv_omega)
    { toBitVec := rsp.toBitVec - 8 } r14 guard in0 rslot lo sp1 a8 hin0 hrs hlo hsp1 ha8 hg _ d1
    hrsp1 hrbp1 hr141 (by rw [hrax1]) (by rw [hrbx1]) (by ecancel)) ?_
  rintro ⟨d3, pc3⟩ ⟨hpc3, hrax3, hrbx3, hrsp3, hrbp3, hr143, Hm3⟩
  dsimp only at hpc3 hrax3 hrbx3 hrsp3 hrbp3 hr143 Hm3
  subst hpc3
  -- Amount and WithdrawableEpoch: 48 → 89 (hand composition: generated steps 48–58 + generated call block)
  refine eventually_trans _ _ _ _ (Decode.from_generated_steps_Amount_WithdrawableEpoch_fields k hk hf hep
    (rsp.toBitVec - 80) rax.toBitVec rbx.toBitVec (rsp.toBitVec - 88) (rsp.toBitVec - 96) (rsp.toBitVec - 72)
    (rsp.toBitVec + 16) (rsp.toBitVec + 32) (rsp.toBitVec + 8)
    (by bv_omega) (by bv_omega) (by bv_omega)
    (by simp only [Int64.toBitVec_ofNat]; bv_omega) (by simp only [Int64.toBitVec_ofNat]; bv_omega)
    (by simp only [Int64.toBitVec_ofNat]; bv_omega)
    { toBitVec := rsp.toBitVec - 8 } r14 guard in2
    (Int.toBytes 8 (Host.addrOf (k + 17 + 1)).toBitVec.toInt) (Int.toBytes 8 (rsp.toBitVec - 8).toInt)
    (Int.toBytes 8 rbx.toBitVec.toInt) a24 (Int.toBytes 8 rdi.toBitVec.toInt) in1 a16
    hin2 (Int.toBytes_length 8 _) (Int.toBytes_length 8 _) (Int.toBytes_length 8 _) ha24 (Int.toBytes_length 8 _)
    hin1 ha16 hg _ d3 hrsp3 hrbp3 hr143 (by ecancel)) ?_
  rintro ⟨d7, pc7⟩ ⟨hpc7, hrax7, hrbx7, hrsp7, hrbp7, hr147, Hm7⟩
  dsimp only at hpc7 hrax7 hrbx7 hrsp7 hrbp7 hr147 Hm7
  subst hpc7
  -- epilogue 89–91
  refine eventually_trans _ _ _ _ (Decode.epi k hk (rsp.toBitVec - 80) (rsp.toBitVec - 8) rsp.toBitVec
    (by bv_omega) (by bv_omega) rbp ra _ d7 hrsp7 (by ecancel)) ?_
  rintro ⟨d8, pc8⟩ ⟨hpc8, hrax8, hrbx8, hrsp8, hrbp8, hr148, hmem8⟩
  dsimp only at hpc8 hrax8 hrbx8 hrsp8 hrbp8 hr148 hmem8
  apply Eventually.done
  rw [show k + 59 + 1 = k + 60 from rfl] at Hm7
  refine ⟨hpc8, hrax8.trans hrax7, hrbx8.trans hrbx7, ?_, hrbp8, hr148.trans hr147,
    Int.toBytes 8 (rbx.toBitVec + 16).toInt, Int.toBytes 8 (rsp.toBitVec - 8).toInt,
    Int.toBytes_length 8 _, Int.toBytes_length 8 _, ?_⟩
  · dsimp only; rw [hrsp8]; apply UInt64.toBitVec_inj.mp
    simp only [UInt64.toBitVec_add, UInt64.toBitVec_ofNat]; bv_omega
  · dsimp only; rw [hmem8]; ecancel

end Prysm.PendingPartialWithdrawal
