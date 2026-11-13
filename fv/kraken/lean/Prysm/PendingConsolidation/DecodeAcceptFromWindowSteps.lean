import Prysm.PendingConsolidation.DecodeAccept
import Prysm.SyncCommitteeMessage.DecodeStepExamples

/-!
# `(*v1alpha1.PendingConsolidation).UnmarshalSSZ`, accept path, re-derived with the window and step mechanisms

`Decode.accept_from_window_steps : Decode.accept_statement` (the pre-committed hand statement, `Prysm/SyncCommitteeMessage/Statements.lean`, unchanged). The text of
`Prysm/PendingConsolidation/DecodeAccept.lean` with the field that the frozen generator missed taken from the window and step mechanisms:

* TargetIndex 48–85: `Decode.example_step_TargetIndex_field` (seven step theorems, then the call-block WINDOW
  `callq; nop; test; je`) instead of a hand-applied `call_argument_reload_segment` and the hand lemma `call_decode_nop_segment`.
Unchanged: `Decode.head`, `Decode.epilogue` (hand, `Prysm/PendingConsolidation/DecodeAccept.lean`), the generated SourceIndex theorems
(`Prysm/PendingConsolidation/GeneratedDecodeCallSegmentsPartial.lean`). `Prysm/PendingConsolidation/DecodeAccept.lean` is imported for `Decode.head` / `Decode.epilogue` only; `Prysm/SyncCommitteeMessage/DecodeAcceptDependencyCheck.lean` checks by
program that this proof does not reach `call_decode_nop_segment`, `bytes32_decode_segment_rax` or `Prysm.SyncCommitteeMessage.Decode.validator_index_argument`.
In-sample (the type is development data since the frozen generator ran on it); no transfer claim.
-/

open Machine Runtime Prysm.PendingConsolidation.Code Codec
variable [Host]

namespace Prysm.PendingConsolidation

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
/-- **Accept path of the real `(*v1alpha1.PendingConsolidation).UnmarshalSSZ` (Go 1.26.10), re-derived with the
window and step mechanisms**; statement = the hand statement `Decode.accept_statement` (unchanged). -/
theorem Decode.accept_from_window_steps : Decode.accept_statement := by
  intro k hk hf kV hkV hfV in0 in1 hin0 hin1 s ra guard
    fp s1 s2 s4 sp1 rslot lo ast a8 a16 hfp h1 h2 h4 hsp1 hrs hlo hast ha8 ha16 R h_mem hguard hlen
  have hvi : Uint64CalleeAccept Prysm.ValidatorIndex.Code.unmarshalLabel := Prysm.ValidatorIndex.Decode.accept_function_spec_holds kV hkV hfV
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hguard hlen ⊢
  have hg : guard.toNat < (rsp.toBitVec - 88).toNat := Prysm.PendingPartialWithdrawal.Decode.accept_guard _ _ hguard
  -- head: entry → directive 15
  refine eventually_trans _ _ _ _ (Decode.head k hk _ ra guard fp s1 s2 s4 ast hfp h1 h2 h4 hast _
    (by dsimp only; ecancel) (Nat.lt_of_le_of_lt (Nat.le_add_right _ 88) hguard) hlen) ?_
  rintro ⟨d1, pc1⟩ ⟨hpc1, hrsp1, hrbp1, hr141, hrax1, hrbx1, Hm1⟩
  dsimp only at hpc1 hrsp1 hrbp1 hr141 hrax1 hrbx1 Hm1
  subst hpc1
  -- SourceIndex: set-up 15–16 (generated)
  refine eventually_trans _ _ _ _ (Decode.generated_call_SourceIndex_argument k hk hf rax.toBitVec (rax.toBitVec + 8)
    (by simp only [Int64.toBitVec_ofNat]) d1 (by rw [hrax1])) ?_
  rintro ⟨d2, pc2⟩ ⟨hpc2, hrsp2, hrbp2, hr142, hrbx2, hrax2, hrcx2, hmem2⟩
  dsimp only at hpc2 hrsp2 hrbp2 hr142 hrbx2 hrax2 hrcx2 hmem2
  subst hpc2
  -- SourceIndex: call block 17–19, label 47 (generated, hC discharged by Prysm.ValidatorIndex.Decode.accept_function_spec_holds)
  refine eventually_trans _ _ _ _ (Decode.generated_call_SourceIndex_call k hk hf hvi
    (rsp.toBitVec - 80) (rax.toBitVec + 8) rbx.toBitVec (rsp.toBitVec - 88) (rsp.toBitVec - 96) (rsp.toBitVec - 72)
    (by bv_omega) (by bv_omega) (by bv_omega)
    { toBitVec := rsp.toBitVec - 8 } r14 guard in0 rslot lo sp1 a8 hin0 hrs hlo hsp1 ha8 hg _ d2
    (hrsp2.trans hrsp1) (hrbp2.trans hrbp1) (hr142.trans hr141) hrax2 (by rw [hrbx2, hrbx1]) hrcx2
    (by rw [hmem2]; ecancel)) ?_
  rintro ⟨d3, pc3⟩ ⟨hpc3, hrax3, hrbx3, hrsp3, hrbp3, hr143, Hm3⟩
  dsimp only at hpc3 hrax3 hrbx3 hrsp3 hrbp3 hr143 Hm3
  subst hpc3
  -- TargetIndex: 48 → 86 (worked call field: seven steps and the call-block window with the nop)
  refine eventually_trans _ _ _ _ (Prysm.PendingConsolidation.Decode.example_step_TargetIndex_field k hk hf hvi
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
  refine eventually_trans _ _ _ _ (Decode.epilogue k hk (rsp.toBitVec - 80) (rsp.toBitVec - 8) rsp.toBitVec
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

end Prysm.PendingConsolidation
