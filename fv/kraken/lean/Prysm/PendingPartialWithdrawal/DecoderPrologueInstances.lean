import Codec.DecoderPrologue
import Prysm.PendingConsolidation.DecodeAccept
import Prysm.SyncCommitteeMessage.DecodeSegments
import Prysm.PendingPartialWithdrawal.DecodeAccept
import Prysm.BeaconBlockHeader.DecodeHeadFromCallSegments

/-!
# The per-type hand head / epilogue / spill lemmas are instances of the frame-parametric mechanism: the `PendingPartialWithdrawal` part

The declarations of the other types of this group are in `Prysm/SyncCommitteeMessage/DecoderPrologueInstances.lean`.
-/

open Machine Runtime

open Codec
namespace Prysm.PendingPartialWithdrawal

open Codec

variable [Host]

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- `Prysm.PendingPartialWithdrawal.Decode.head` (PendingPartialWithdrawal head, frame `0x48`, size 24) from `decode_prologue_segment`, the spills as `step_store` steps and `step_nil_check`. -/
theorem Decode.head_inst : type_of% (@Prysm.PendingPartialWithdrawal.Decode.head ‹Host›) := by
  intro k hk s ra guard fp s1 s2 s4 ast hfp h1 h2 h4 hast R h_mem hguard hlen
  have hcs : Eq (ast.At s.regs.rax.toBitVec) =
      Eq ((ast.take 1).At s.regs.rax.toBitVec) ⋆ Eq ((ast.drop 1).At (s.regs.rax.toBitVec + 1)) := by
    conv => lhs; rw [← List.take_append_drop 1 ast]
    exact at_app _ _ (by rw [List.length_take, hast]; rfl) (by simp [hast])
  rw [hcs] at h_mem
  refine eventually_trans _ _ _ _ (decode_prologue_segment _ _ _ _ 72 96 24 _ k (k + 11) (window_infix_at hk 0 11) (by rfl) (by rfl)
    s ra guard (s.regs.rsp.toBitVec - 80) (s.regs.rsp.toBitVec + 16)
    (by simp only [Int64.toBitVec_ofNat]; bv_omega) (by simp only [Int64.toBitVec_ofNat]; bv_omega)
    fp s2 hfp h2 _ (by ecancel) hguard (by rw [hlen]; rfl)) ?_
  rintro ⟨d1, pc1⟩ ⟨hpc1, hrsp1, hrbp1, hreg1, Hm1⟩
  dsimp only at hpc1 hrsp1 hrbp1 hreg1 Hm1
  subst hpc1
  have hrax1 := UInt64.toBitVec_inj.mp (hreg1 Reg64.rax (by decide) (by decide))
  have hrbx1 := UInt64.toBitVec_inj.mp (hreg1 Reg64.rbx (by decide) (by decide))
  have hrdi1 := UInt64.toBitVec_inj.mp (hreg1 Reg64.rdi (by decide) (by decide))
  have hr141 := UInt64.toBitVec_inj.mp (hreg1 Reg64.r14 (by decide) (by decide))
  clear hreg1
  obtain ⟨⟨rax1, rbx1, rcx1, rdx1, rsi1, rdi1, rsp1, rbp1, r81, r91, r101, r111, r121, r131, r141, r151⟩, zmms1, flags1, mem1⟩ := d1
  simp only at hrsp1 hrbp1 hrax1 hrbx1 hrdi1 hr141 Hm1
  subst hrsp1 hrbp1 hrax1 hrbx1 hrdi1 hr141
  apply step_store Reg64.rax Reg64.rsp 88 _ (k + 11) (k + 12) (window_infix_at hk 11 1) (by rfl) (by rfl)
    (s.regs.rsp.toBitVec - 80) (s.regs.rsp.toBitVec + 8) (by simp only [Int64.toBitVec_ofNat]; bv_omega)
    s1 h1 _ _ _ (by rfl) (by ecancel)
  intro m1 H1; normalize_registers; simp only [Reg64s.get64] at H1
  apply step_store Reg64.rdi Reg64.rsp 112 _ (k + 12) (k + 13) (window_infix_at hk 12 1) (by rfl) (by rfl)
    (s.regs.rsp.toBitVec - 80) (s.regs.rsp.toBitVec + 32) (by simp only [Int64.toBitVec_ofNat]; bv_omega)
    s4 h4 _ _ _ (by rfl) (by ecancel)
  intro m2 H2; normalize_registers; simp only [Reg64s.get64] at H2
  apply step_store Reg64.rbx Reg64.rsp 96 _ (k + 13) (k + 14) (window_infix_at hk 13 1) (by rfl) (by rfl)
    (s.regs.rsp.toBitVec - 80) (s.regs.rsp.toBitVec + 16) (by simp only [Int64.toBitVec_ofNat]; bv_omega)
    (Int.toBytes 8 s.regs.rbx.toBitVec.toInt) (Int.toBytes_length 8 _) _ _ _ (by rfl) (by ecancel)
  intro m3 H3; normalize_registers; simp only [Reg64s.get64] at H3
  apply step_nil_check Reg64.rax _ (k + 14) (k + 15) (window_infix_at hk 14 1) (by rfl) (by rfl)
    s.regs.rax.toBitVec (ast.take 1) (by simp [hast]) _ _ _ (by rfl) (by ecancel)
  intro fl; normalize_registers
  apply Eventually.done
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  dsimp only
  rw [hcs]; simp only [Std.ExtHashMap.sep_assoc]; ecancel

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- `Prysm.PendingPartialWithdrawal.Decode.epilogue` (PendingPartialWithdrawal epilogue, frame `0x48`) from `step_add_immediate` and `decode_return_segment`. -/
theorem Decode.epilogue_inst : type_of% (@Prysm.PendingPartialWithdrawal.Decode.epilogue ‹Host›) := by
  intro k hk sp aFp aRa hFp hRa fp0 ra R s hrsp h_mem
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at hrsp h_mem ⊢
  subst rsp hFp hRa
  apply step_add_immediate Reg64.rsp 72 _ (k + 89) (k + 90) (window_infix_at hk 89 1) (by rfl) (by rfl)
  intro fl; normalize_registers
  refine eventually_trans _ _ _ _ (decode_return_segment _ (k + 90) (window_infix_at hk 90 2) (by rfl) (sp + 72) (sp + 80) (by bv_omega)
    fp0 ra R _ (by rfl) (by ecancel)) ?_
  rintro ⟨d, pc⟩ ⟨hpc, hrsp', hrbp', hreg, hmem⟩
  dsimp only at hpc hrsp' hrbp' hreg hmem
  apply Eventually.done
  refine ⟨hpc, ?_, ?_, ?_, hrbp', ?_, hmem⟩
  · exact UInt64.toBitVec_inj.mp (hreg Reg64.rax (by decide) (by decide))
  · exact UInt64.toBitVec_inj.mp (hreg Reg64.rbx (by decide) (by decide))
  · rw [hrsp']; exact congrArg UInt64.ofBitVec (by bv_omega)
  · exact UInt64.toBitVec_inj.mp (hreg Reg64.r14 (by decide) (by decide))

end Prysm.PendingPartialWithdrawal
