import Codec.DecoderPrologue
import Prysm.PendingConsolidation.DecodeAccept
import Prysm.SyncCommitteeMessage.DecodeSegments
import Prysm.PendingPartialWithdrawal.DecodeAccept
import Prysm.BeaconBlockHeader.DecodeHeadFromCallSegments

/-!
# The per-type hand head / epilogue / spill lemmas are instances of the frame-parametric mechanism

Each theorem has the TYPE of a per-type hand lemma (`type_of%`: the committed statement) and is proved from
`decpro_seg`, `decret_seg`, `kstep_nilchk` (`HeadN.lean`) and the step lemmas (`StepK.lean`) only:
heads `Decode.head0`, `Prysm.PendingConsolidation.Decode.head`, `Prysm.PendingPartialWithdrawal.Decode.head`, `Prysm.BeaconBlockHeader.Decode.head0` (frames `0x60`, `0x48`, `0x48`, `0x60`; three
spill orders); epilogues `Prysm.PendingConsolidation.Decode.epi`, `Prysm.PendingPartialWithdrawal.Decode.epi`; nil-error spills `Decode.spill2`, `Prysm.BeaconBlockHeader.Decode.spill2`.
The proof texts were produced by a scratch script from the `.S` files (directive index = line − 1); the only
per-type data are `F`, `dB`, `sz`, the spill order and the directive indices.
-/

open Machine Runtime TestTarget

open Codec
namespace Prysm.SyncCommitteeMessage

open Codec

variable [Host]

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- `Decode.head0` (SyncCommitteeMessage head, frame `0x60`, size 144) from `decpro_seg`, the spills as `kstep_st` steps and `kstep_nilchk`. -/
theorem Decode.head0_inst : type_of% (@Decode.head0 ‹Host›) := by
  intro k hk s ra guard fp s1 s2 s4 ast hfp h1 h2 h4 hast R h_mem hguard hlen
  have hcs : Eq (ast.At s.regs.rax.toBitVec) =
      Eq ((ast.take 1).At s.regs.rax.toBitVec) ⋆ Eq ((ast.drop 1).At (s.regs.rax.toBitVec + 1)) := by
    conv => lhs; rw [← List.take_append_drop 1 ast]
    exact at_app _ _ (by rw [List.length_take, hast]; rfl) (by simp [hast])
  rw [hcs] at h_mem
  refine eventually_trans _ _ _ _ (decpro_seg _ _ _ _ 96 120 144 _ k (k + 11) (win hk 0 11) (by rfl) (by rfl)
    s ra guard (s.regs.rsp.toBitVec - 104) (s.regs.rsp.toBitVec + 16)
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
  apply kstep_st Reg64.rax Reg64.rsp 112 _ (k + 11) (k + 12) (win hk 11 1) (by rfl) (by rfl)
    (s.regs.rsp.toBitVec - 104) (s.regs.rsp.toBitVec + 8) (by simp only [Int64.toBitVec_ofNat]; bv_omega)
    s1 h1 _ _ _ (by rfl) (by ecancel)
  intro m1 H1; kn; simp only [Reg64s.get64] at H1
  apply kstep_st Reg64.rdi Reg64.rsp 136 _ (k + 12) (k + 13) (win hk 12 1) (by rfl) (by rfl)
    (s.regs.rsp.toBitVec - 104) (s.regs.rsp.toBitVec + 32) (by simp only [Int64.toBitVec_ofNat]; bv_omega)
    s4 h4 _ _ _ (by rfl) (by ecancel)
  intro m2 H2; kn; simp only [Reg64s.get64] at H2
  apply kstep_st Reg64.rbx Reg64.rsp 120 _ (k + 13) (k + 14) (win hk 13 1) (by rfl) (by rfl)
    (s.regs.rsp.toBitVec - 104) (s.regs.rsp.toBitVec + 16) (by simp only [Int64.toBitVec_ofNat]; bv_omega)
    (Int.toBytes 8 s.regs.rbx.toBitVec.toInt) (Int.toBytes_length 8 _) _ _ _ (by rfl) (by ecancel)
  intro m3 H3; kn; simp only [Reg64s.get64] at H3
  apply kstep_nilchk Reg64.rax _ (k + 14) (k + 15) (win hk 14 1) (by rfl) (by rfl)
    s.regs.rax.toBitVec (ast.take 1) (by simp [hast]) _ _ _ (by rfl) (by ecancel)
  intro fl; kn
  apply Eventually.done
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  dsimp only
  rw [hcs]; simp only [Std.ExtHashMap.sep_assoc]; ecancel

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- `Prysm.PendingConsolidation.Decode.head` (PendingConsolidation head, frame `0x48`, size 16) from `decpro_seg`, the spills as `kstep_st` steps and `kstep_nilchk`. -/
theorem _root_.Prysm.PendingConsolidation.Decode.head_inst : type_of% (@Prysm.PendingConsolidation.Decode.head ‹Host›) := by
  intro k hk s ra guard fp s1 s2 s4 ast hfp h1 h2 h4 hast R h_mem hguard hlen
  have hcs : Eq (ast.At s.regs.rax.toBitVec) =
      Eq ((ast.take 1).At s.regs.rax.toBitVec) ⋆ Eq ((ast.drop 1).At (s.regs.rax.toBitVec + 1)) := by
    conv => lhs; rw [← List.take_append_drop 1 ast]
    exact at_app _ _ (by rw [List.length_take, hast]; rfl) (by simp [hast])
  rw [hcs] at h_mem
  refine eventually_trans _ _ _ _ (decpro_seg _ _ _ _ 72 96 16 _ k (k + 11) (win hk 0 11) (by rfl) (by rfl)
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
  apply kstep_st Reg64.rax Reg64.rsp 88 _ (k + 11) (k + 12) (win hk 11 1) (by rfl) (by rfl)
    (s.regs.rsp.toBitVec - 80) (s.regs.rsp.toBitVec + 8) (by simp only [Int64.toBitVec_ofNat]; bv_omega)
    s1 h1 _ _ _ (by rfl) (by ecancel)
  intro m1 H1; kn; simp only [Reg64s.get64] at H1
  apply kstep_st Reg64.rbx Reg64.rsp 96 _ (k + 12) (k + 13) (win hk 12 1) (by rfl) (by rfl)
    (s.regs.rsp.toBitVec - 80) (s.regs.rsp.toBitVec + 16) (by simp only [Int64.toBitVec_ofNat]; bv_omega)
    (Int.toBytes 8 s.regs.rbx.toBitVec.toInt) (Int.toBytes_length 8 _) _ _ _ (by rfl) (by ecancel)
  intro m2 H2; kn; simp only [Reg64s.get64] at H2
  apply kstep_st Reg64.rdi Reg64.rsp 112 _ (k + 13) (k + 14) (win hk 13 1) (by rfl) (by rfl)
    (s.regs.rsp.toBitVec - 80) (s.regs.rsp.toBitVec + 32) (by simp only [Int64.toBitVec_ofNat]; bv_omega)
    s4 h4 _ _ _ (by rfl) (by ecancel)
  intro m3 H3; kn; simp only [Reg64s.get64] at H3
  apply kstep_nilchk Reg64.rax _ (k + 14) (k + 15) (win hk 14 1) (by rfl) (by rfl)
    s.regs.rax.toBitVec (ast.take 1) (by simp [hast]) _ _ _ (by rfl) (by ecancel)
  intro fl; kn
  apply Eventually.done
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  dsimp only
  rw [hcs]; simp only [Std.ExtHashMap.sep_assoc]; ecancel

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- `Prysm.PendingPartialWithdrawal.Decode.head` (PendingPartialWithdrawal head, frame `0x48`, size 24) from `decpro_seg`, the spills as `kstep_st` steps and `kstep_nilchk`. -/
theorem _root_.Prysm.PendingPartialWithdrawal.Decode.head_inst : type_of% (@Prysm.PendingPartialWithdrawal.Decode.head ‹Host›) := by
  intro k hk s ra guard fp s1 s2 s4 ast hfp h1 h2 h4 hast R h_mem hguard hlen
  have hcs : Eq (ast.At s.regs.rax.toBitVec) =
      Eq ((ast.take 1).At s.regs.rax.toBitVec) ⋆ Eq ((ast.drop 1).At (s.regs.rax.toBitVec + 1)) := by
    conv => lhs; rw [← List.take_append_drop 1 ast]
    exact at_app _ _ (by rw [List.length_take, hast]; rfl) (by simp [hast])
  rw [hcs] at h_mem
  refine eventually_trans _ _ _ _ (decpro_seg _ _ _ _ 72 96 24 _ k (k + 11) (win hk 0 11) (by rfl) (by rfl)
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
  apply kstep_st Reg64.rax Reg64.rsp 88 _ (k + 11) (k + 12) (win hk 11 1) (by rfl) (by rfl)
    (s.regs.rsp.toBitVec - 80) (s.regs.rsp.toBitVec + 8) (by simp only [Int64.toBitVec_ofNat]; bv_omega)
    s1 h1 _ _ _ (by rfl) (by ecancel)
  intro m1 H1; kn; simp only [Reg64s.get64] at H1
  apply kstep_st Reg64.rdi Reg64.rsp 112 _ (k + 12) (k + 13) (win hk 12 1) (by rfl) (by rfl)
    (s.regs.rsp.toBitVec - 80) (s.regs.rsp.toBitVec + 32) (by simp only [Int64.toBitVec_ofNat]; bv_omega)
    s4 h4 _ _ _ (by rfl) (by ecancel)
  intro m2 H2; kn; simp only [Reg64s.get64] at H2
  apply kstep_st Reg64.rbx Reg64.rsp 96 _ (k + 13) (k + 14) (win hk 13 1) (by rfl) (by rfl)
    (s.regs.rsp.toBitVec - 80) (s.regs.rsp.toBitVec + 16) (by simp only [Int64.toBitVec_ofNat]; bv_omega)
    (Int.toBytes 8 s.regs.rbx.toBitVec.toInt) (Int.toBytes_length 8 _) _ _ _ (by rfl) (by ecancel)
  intro m3 H3; kn; simp only [Reg64s.get64] at H3
  apply kstep_nilchk Reg64.rax _ (k + 14) (k + 15) (win hk 14 1) (by rfl) (by rfl)
    s.regs.rax.toBitVec (ast.take 1) (by simp [hast]) _ _ _ (by rfl) (by ecancel)
  intro fl; kn
  apply Eventually.done
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  dsimp only
  rw [hcs]; simp only [Std.ExtHashMap.sep_assoc]; ecancel

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- `Prysm.BeaconBlockHeader.Decode.head0` (BeaconBlockHeader head, frame `0x60`, size 112) from `decpro_seg`, the spills as `kstep_st` steps and `kstep_nilchk`. -/
theorem _root_.Prysm.BeaconBlockHeader.Decode.head0_inst : type_of% (@Prysm.BeaconBlockHeader.Decode.head0 ‹Host›) := by
  intro k hk s ra guard fp s1 s2 s4 ast hfp h1 h2 h4 hast R h_mem hguard hlen
  have hcs : Eq (ast.At s.regs.rax.toBitVec) =
      Eq ((ast.take 1).At s.regs.rax.toBitVec) ⋆ Eq ((ast.drop 1).At (s.regs.rax.toBitVec + 1)) := by
    conv => lhs; rw [← List.take_append_drop 1 ast]
    exact at_app _ _ (by rw [List.length_take, hast]; rfl) (by simp [hast])
  rw [hcs] at h_mem
  refine eventually_trans _ _ _ _ (decpro_seg _ _ _ _ 96 120 112 _ k (k + 11) (win hk 0 11) (by rfl) (by rfl)
    s ra guard (s.regs.rsp.toBitVec - 104) (s.regs.rsp.toBitVec + 16)
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
  apply kstep_st Reg64.rax Reg64.rsp 112 _ (k + 11) (k + 12) (win hk 11 1) (by rfl) (by rfl)
    (s.regs.rsp.toBitVec - 104) (s.regs.rsp.toBitVec + 8) (by simp only [Int64.toBitVec_ofNat]; bv_omega)
    s1 h1 _ _ _ (by rfl) (by ecancel)
  intro m1 H1; kn; simp only [Reg64s.get64] at H1
  apply kstep_st Reg64.rdi Reg64.rsp 136 _ (k + 12) (k + 13) (win hk 12 1) (by rfl) (by rfl)
    (s.regs.rsp.toBitVec - 104) (s.regs.rsp.toBitVec + 32) (by simp only [Int64.toBitVec_ofNat]; bv_omega)
    s4 h4 _ _ _ (by rfl) (by ecancel)
  intro m2 H2; kn; simp only [Reg64s.get64] at H2
  apply kstep_st Reg64.rbx Reg64.rsp 120 _ (k + 13) (k + 14) (win hk 13 1) (by rfl) (by rfl)
    (s.regs.rsp.toBitVec - 104) (s.regs.rsp.toBitVec + 16) (by simp only [Int64.toBitVec_ofNat]; bv_omega)
    (Int.toBytes 8 s.regs.rbx.toBitVec.toInt) (Int.toBytes_length 8 _) _ _ _ (by rfl) (by ecancel)
  intro m3 H3; kn; simp only [Reg64s.get64] at H3
  apply kstep_nilchk Reg64.rax _ (k + 14) (k + 15) (win hk 14 1) (by rfl) (by rfl)
    s.regs.rax.toBitVec (ast.take 1) (by simp [hast]) _ _ _ (by rfl) (by ecancel)
  intro fl; kn
  apply Eventually.done
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  dsimp only
  rw [hcs]; simp only [Std.ExtHashMap.sep_assoc]; ecancel

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- `Prysm.PendingConsolidation.Decode.epi` (PendingConsolidation epilogue, frame `0x48`) from `kstep_add` and `decret_seg`. -/
theorem _root_.Prysm.PendingConsolidation.Decode.epi_inst : type_of% (@Prysm.PendingConsolidation.Decode.epi ‹Host›) := by
  intro k hk sp aFp aRa hFp hRa fp0 ra R s hrsp h_mem
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at hrsp h_mem ⊢
  subst rsp hFp hRa
  apply kstep_add Reg64.rsp 72 _ (k + 86) (k + 87) (win hk 86 1) (by rfl) (by rfl)
  intro fl; kn
  refine eventually_trans _ _ _ _ (decret_seg _ (k + 87) (win hk 87 2) (by rfl) (sp + 72) (sp + 80) (by bv_omega)
    fp0 ra R _ (by rfl) (by ecancel)) ?_
  rintro ⟨d, pc⟩ ⟨hpc, hrsp', hrbp', hreg, hmem⟩
  dsimp only at hpc hrsp' hrbp' hreg hmem
  apply Eventually.done
  refine ⟨hpc, ?_, ?_, ?_, hrbp', ?_, hmem⟩
  · exact UInt64.toBitVec_inj.mp (hreg Reg64.rax (by decide) (by decide))
  · exact UInt64.toBitVec_inj.mp (hreg Reg64.rbx (by decide) (by decide))
  · rw [hrsp']; exact congrArg UInt64.ofBitVec (by bv_omega)
  · exact UInt64.toBitVec_inj.mp (hreg Reg64.r14 (by decide) (by decide))

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- `Prysm.PendingPartialWithdrawal.Decode.epi` (PendingPartialWithdrawal epilogue, frame `0x48`) from `kstep_add` and `decret_seg`. -/
theorem _root_.Prysm.PendingPartialWithdrawal.Decode.epi_inst : type_of% (@Prysm.PendingPartialWithdrawal.Decode.epi ‹Host›) := by
  intro k hk sp aFp aRa hFp hRa fp0 ra R s hrsp h_mem
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at hrsp h_mem ⊢
  subst rsp hFp hRa
  apply kstep_add Reg64.rsp 72 _ (k + 89) (k + 90) (win hk 89 1) (by rfl) (by rfl)
  intro fl; kn
  refine eventually_trans _ _ _ _ (decret_seg _ (k + 90) (win hk 90 2) (by rfl) (sp + 72) (sp + 80) (by bv_omega)
    fp0 ra R _ (by rfl) (by ecancel)) ?_
  rintro ⟨d, pc⟩ ⟨hpc, hrsp', hrbp', hreg, hmem⟩
  dsimp only at hpc hrsp' hrbp' hreg hmem
  apply Eventually.done
  refine ⟨hpc, ?_, ?_, ?_, hrbp', ?_, hmem⟩
  · exact UInt64.toBitVec_inj.mp (hreg Reg64.rax (by decide) (by decide))
  · exact UInt64.toBitVec_inj.mp (hreg Reg64.rbx (by decide) (by decide))
  · rw [hrsp']; exact congrArg UInt64.ofBitVec (by bv_omega)
  · exact UInt64.toBitVec_inj.mp (hreg Reg64.r14 (by decide) (by decide))

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- `Decode.spill2` (SyncCommitteeMessage nil-error spills 118–119) from two `kstep_st` steps. -/
theorem Decode.spill2_inst : type_of% (@Decode.spill2 ‹Host›) := by
  intro k hk sp a28 a30 h28 h30 s28 s30 hs28 hs30 R s hrsp h_mem
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at hrsp h_mem ⊢
  subst rsp h28 h30
  apply kstep_st Reg64.rbx Reg64.rsp 48 _ (k + 118) (k + 119) (win hk 118 1) (by rfl) (by rfl)
    sp (sp + 48) (by simp only [Int64.toBitVec_ofNat]) s30 hs30 _ _ _ (by rfl) (by ecancel)
  intro m1 H1; kn; simp only [Reg64s.get64] at H1
  apply kstep_st Reg64.rax Reg64.rsp 40 _ (k + 119) (k + 120) (win hk 119 1) (by rfl) (by rfl)
    sp (sp + 40) (by simp only [Int64.toBitVec_ofNat]) s28 hs28 _ _ _ (by rfl) (by ecancel)
  intro m2 H2; kn; simp only [Reg64s.get64] at H2
  apply Eventually.done
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  dsimp only
  ecancel

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- `Prysm.BeaconBlockHeader.Decode.spill2` (BeaconBlockHeader nil-error spills 86–87) from two `kstep_st` steps. -/
theorem _root_.Prysm.BeaconBlockHeader.Decode.spill2_inst : type_of% (@Prysm.BeaconBlockHeader.Decode.spill2 ‹Host›) := by
  intro k hk sp a28 a30 h28 h30 s28 s30 hs28 hs30 R s hrsp h_mem
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at hrsp h_mem ⊢
  subst rsp h28 h30
  apply kstep_st Reg64.rbx Reg64.rsp 48 _ (k + 86) (k + 87) (win hk 86 1) (by rfl) (by rfl)
    sp (sp + 48) (by simp only [Int64.toBitVec_ofNat]) s30 hs30 _ _ _ (by rfl) (by ecancel)
  intro m1 H1; kn; simp only [Reg64s.get64] at H1
  apply kstep_st Reg64.rax Reg64.rsp 40 _ (k + 87) (k + 88) (win hk 87 1) (by rfl) (by rfl)
    sp (sp + 40) (by simp only [Int64.toBitVec_ofNat]) s28 hs28 _ _ _ (by rfl) (by ecancel)
  intro m2 H2; kn; simp only [Reg64s.get64] at H2
  apply Eventually.done
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  dsimp only
  ecancel

end Prysm.SyncCommitteeMessage
