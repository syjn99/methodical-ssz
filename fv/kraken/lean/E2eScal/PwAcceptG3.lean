import E2eScal.PwAccept
import E2eScal.Gen3PwDec

/-!
# PendingPartialWithdrawal accept path from the GENERATED `p2dec --gen3` segments (reuse demonstration)

Hand composition (not generator output): the chain of `PwAccept.lean` with every lemma instance replaced by
the generated theorem of `Gen3PwDec.lean` (`p2dec --gen3`, raw output) whose declared type is that instance
(its `_kind`): `pw_g3dec_Index_arg` / `_call`, `pw_g3dec_WithdrawableEpoch_arg1`, `pw_g3dec_Amount_seg`,
`pw_g3dec_WithdrawableEpoch_arg2` / `_call`. The code facts come from the generated theorems; head
(`pw_head`, 0–14) and epilogue (`pw_epi`, 89–91) stay hand steps of `PwAccept.lean` (frame `0x48`). The
statement is the hand statement `pw_accept_stmt` (`H4Stmt.lean`, unchanged). In-sample (development data).
-/

open Machine Runtime TestTarget E2e E2eScal.H4Code E2eScal.BhCode E2eScal Codec
variable [Host]

namespace E2eScal.H4

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Accept path of `(*v1alpha1.PendingPartialWithdrawal).UnmarshalSSZ` from the GENERATED `p2dec --gen3` segments;
statement = the hand statement `pw_accept_stmt` (unchanged). -/
theorem pw_e2e_accept_main_g3 : pw_accept_stmt := by
  intro k hk hf kV hkV hfV kE hkE hfE in0 in1 in2 hin0 hin1 hin2 s ra guard
    fp s1 s2 s4 sp1 rslot lo ast a8 a16 a24 hfp h1 h2 h4 hsp1 hrs hlo hast ha8 ha16 ha24 R h_mem hguard hlen
  have hvi : U64CalleeAcc viLabel := vi_uacc_holds kV hkV hfV
  have hep : U64CalleeAcc E2e.Code.epLabel := ep_uacc_holds kE hkE hfE
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hguard hlen ⊢
  have hg : guard.toNat < (rsp.toBitVec - 88).toNat := pwa_guard _ _ hguard
  -- head: entry → directive 15
  refine eventually_trans _ _ _ _ (pw_head k hk _ ra guard fp s1 s2 s4 ast hfp h1 h2 h4 hast _
    (by dsimp only; ecancel) (Nat.lt_of_le_of_lt (Nat.le_add_right _ 88) hguard) hlen) ?_
  rintro ⟨d1, pc1⟩ ⟨hpc1, hrsp1, hrbp1, hr141, hrax1, hrbx1, Hm1⟩
  dsimp only at hpc1 hrsp1 hrbp1 hr141 hrax1 hrbx1 Hm1
  subst hpc1
  -- Index: set-up 15–16
  refine eventually_trans _ _ _ _ (Gen.pw_g3dec_Index_arg k hk hf rax.toBitVec (rax.toBitVec + 8)
    (by simp only [Int64.toBitVec_ofNat]) d1 (by rw [hrax1])) ?_
  rintro ⟨d2, pc2⟩ ⟨hpc2, hrsp2, hrbp2, hr142, hrbx2, hrax2, hrcx2, hmem2⟩
  dsimp only at hpc2 hrsp2 hrbp2 hr142 hrbx2 hrax2 hrcx2 hmem2
  subst hpc2
  -- Index: call block 17–19, label 47
  refine eventually_trans _ _ _ _ (Gen.pw_g3dec_Index_call k hk hf hvi
    (rsp.toBitVec - 80) (rax.toBitVec + 8) rbx.toBitVec (rsp.toBitVec - 88) (rsp.toBitVec - 96) (rsp.toBitVec - 72)
    (by bv_omega) (by bv_omega) (by bv_omega)
    { toBitVec := rsp.toBitVec - 8 } r14 guard in0 rslot lo sp1 a8 hin0 hrs hlo hsp1 ha8 hg _ d2
    (hrsp2.trans hrsp1) (hrbp2.trans hrbp1) (hr142.trans hr141) hrax2 (by rw [hrbx2, hrbx1]) hrcx2
    (by rw [hmem2]; ecancel)) ?_
  rintro ⟨d3, pc3⟩ ⟨hpc3, hrax3, hrbx3, hrsp3, hrbp3, hr143, Hm3⟩
  dsimp only at hpc3 hrax3 hrbx3 hrsp3 hrbp3 hr143 Hm3
  subst hpc3
  -- WithdrawableEpoch: set-up, first part 48–53
  refine eventually_trans _ _ _ _ (Gen.pw_g3dec_WithdrawableEpoch_arg1 k hk hf
    (rsp.toBitVec - 80) rax.toBitVec rbx.toBitVec (rsp.toBitVec + 16) (rsp.toBitVec + 32) (rsp.toBitVec + 8)
    (rbx.toBitVec + 16) (rax.toBitVec + 24)
    (by simp only [Int64.toBitVec_ofNat]; bv_omega) (by simp only [Int64.toBitVec_ofNat]; bv_omega)
    (by simp only [Int64.toBitVec_ofNat]; bv_omega) (by simp only [Int64.toBitVec_ofNat])
    (by simp only [Int64.toBitVec_ofNat])
    (Int.toBytes 8 rdi.toBitVec.toInt) (Int.toBytes_length 8 _) _ d3 hrsp3 (by ecancel)) ?_
  rintro ⟨d4, pc4⟩ ⟨hpc4, hrsp4, hrbp4, hr144, hrbx4, hrdx4, hrax4, hrsi4, hmem4⟩
  dsimp only at hpc4 hrsp4 hrbp4 hr144 hrbx4 hrdx4 hrax4 hrsi4 hmem4
  subst hpc4
  -- Amount: 54–55
  refine eventually_trans _ _ _ _ (Gen.pw_g3dec_Amount_seg k hk hf
    rbx.toBitVec rax.toBitVec (rbx.toBitVec + 8) (rax.toBitVec + 16)
    (by simp only [Int64.toBitVec_ofNat]) (by simp only [Int64.toBitVec_ofNat])
    in1 a16 hin1 ha16 _ d4 hrbx4 hrax4 (by rw [hmem4]; ecancel)) ?_
  rintro ⟨d5, pc5⟩ ⟨hpc5, hrsp5, hrbp5, hr145, hrax5, hrbx5, hreg5, Hm5⟩
  dsimp only at hpc5 hrsp5 hrbp5 hr145 hrax5 hrbx5 hreg5 Hm5
  subst hpc5
  have hrsi5 : d5.regs.rsi.toBitVec = rax.toBitVec + 24 := (hreg5 Reg64.rsi (by decide)).trans hrsi4
  have hrdx5 : d5.regs.rdx.toBitVec = rbx.toBitVec + 16 := (hreg5 Reg64.rdx (by decide)).trans hrdx4
  -- WithdrawableEpoch: set-up, second part 56–58
  refine eventually_trans _ _ _ _ (Gen.pw_g3dec_WithdrawableEpoch_arg2 k hk hf d5) ?_
  rintro ⟨d6, pc6⟩ ⟨hpc6, hrsp6, hrbp6, hr146, hrax6, hrbx6, hrcx6, hmem6⟩
  dsimp only at hpc6 hrsp6 hrbp6 hr146 hrax6 hrbx6 hrcx6 hmem6
  subst hpc6
  -- WithdrawableEpoch: call block 59–61, label 88
  refine eventually_trans _ _ _ _ (Gen.pw_g3dec_WithdrawableEpoch_call k hk hf hep
    (rsp.toBitVec - 80) (rax.toBitVec + 24) (rbx.toBitVec + 16) (rsp.toBitVec - 88) (rsp.toBitVec - 96)
    (rsp.toBitVec - 72) (by bv_omega) (by bv_omega) (by bv_omega)
    { toBitVec := rsp.toBitVec - 8 } r14 guard in2
    (Int.toBytes 8 (Host.addrOf (k + 17 + 1)).toBitVec.toInt) (Int.toBytes 8 (rsp.toBitVec - 8).toInt)
    (Int.toBytes 8 rbx.toBitVec.toInt) a24
    hin2 (Int.toBytes_length 8 _) (Int.toBytes_length 8 _) (Int.toBytes_length 8 _) ha24 hg _ d6
    (hrsp6.trans (hrsp5.trans (hrsp4.trans hrsp3))) (hrbp6.trans (hrbp5.trans (hrbp4.trans hrbp3)))
    (hr146.trans (hr145.trans (hr144.trans hr143)))
    (by rw [hrax6]; exact hrsi5) (by rw [hrbx6]; exact hrdx5) hrcx6
    (by rw [hmem6]; ecancel)) ?_
  rintro ⟨d7, pc7⟩ ⟨hpc7, hrax7, hrbx7, hrsp7, hrbp7, hr147, Hm7⟩
  dsimp only at hpc7 hrax7 hrbx7 hrsp7 hrbp7 hr147 Hm7
  subst hpc7
  -- epilogue 89–91
  refine eventually_trans _ _ _ _ (pw_epi k hk (rsp.toBitVec - 80) (rsp.toBitVec - 8) rsp.toBitVec
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

/-- Same declared type as the lemma unit's hand proof. -/
theorem pw_e2e_accept_main_g3_type : ∀ (h : Host),
    type_of% (@pw_e2e_accept_main_g3 h) = type_of% (@pw_e2e_accept_main h) := by
  intro h; with_reducible rfl

end E2eScal.H4
