import Prysm.BlobIdentifier.DecodeRejectSizeKindInstances
import Prysm.PendingDeposit.GeneratedDecodeSteps

/-!
# Worked examples: size-reject theorems in generated style

`Decode.example_reject`: PendingDeposit (frame `0x40`), with the declared type of the committed hand theorem
`Decode.reject_size`. `Prysm.VoluntaryExit.Decode.example_reject`: VoluntaryExit (frame `0x48`), no hand theorem; statement =
`decRejectKindN Prysm.VoluntaryExit.Code.unmarshalSSZ 16` (`_kind` line). Both are one application of `decrej_seg`; the generator reads
`F`, `dB`, `sz` and the directive indices of `lerr:`, `add`, `pop` from the `.S` file.
-/

open Machine Runtime Prysm.PendingDeposit.Code
variable [Host]

open Codec
namespace Prysm.PendingDeposit

set_option maxRecDepth 100000 in
/-- PendingDeposit: the committed size-reject statement, re-derived from `decrej_seg` (frame `0x40`). -/
theorem Decode.example_reject : type_of% (@Prysm.PendingDeposit.Decode.reject_size ‹Host›) := by
  intro k hk hf s ra guard e0 e1 fp s2 hfp h2 R h_mem hguard hlen
  have hl := Machine.label_at' hk hf (j := 164)
    (by simp only [unmarshalSSZ, List.getElem?_cons_succ, List.getElem?_cons_zero]; rfl)
    (by simp only [unmarshalSSZ, List.take_succ_cons, List.take_zero, List.contains_cons, List.contains_nil]; decide)
  exact decrej_seg _ _ _ _ 64 88 192 _ k (win hk 0 11) (by rfl) (by decide)
    _ (k + 164) (k + 167) (win hk 164 3) (by rfl) (by rfl) hl
    _ (k + 168) (win hk 167 1) (by rfl) (by rfl) _ (win hk 168 2) (by rfl)
    s ra guard e0 e1 fp s2 hfp h2 R h_mem hguard (fun h => hlen (h.trans (by rfl)))

set_option maxRecDepth 100000 in
/-- VoluntaryExit: size reject (frame `0x48`, size 16); statement = the kind instance. -/
theorem _root_.Prysm.VoluntaryExit.Decode.example_reject : ∀ (k : Nat) (hk : Prysm.VoluntaryExit.Code.unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh Prysm.VoluntaryExit.Code.unmarshalSSZ k)
    (s : MachineData) (ra guard e0 e1 : UInt64) (fp s2 : List UInt8) (hfp : fp.length = 8) (h2 : s2.length = 8)
    (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At ElfData.CheckpointAndEpoch.e2eErrSize_addr)
      ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrSize" + 8).toBitVec) ⋆ R)
    (hguard : guard.toNat < s.regs.rsp.toNat) (hlen : s.regs.rcx ≠ 16),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = e0 ∧ st.data.regs.rbx = e1
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14
        ∧ (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At ElfData.CheckpointAndEpoch.e2eErrSize_addr)
          ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrSize" + 8).toBitVec) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  intro k hk hf s ra guard e0 e1 fp s2 hfp h2 R h_mem hguard hlen
  have hl := Machine.label_at' hk hf (j := 89)
    (by simp only [Prysm.VoluntaryExit.Code.unmarshalSSZ, List.getElem?_cons_succ, List.getElem?_cons_zero]; rfl)
    (by simp only [Prysm.VoluntaryExit.Code.unmarshalSSZ, List.take_succ_cons, List.take_zero, List.contains_cons, List.contains_nil]; decide)
  exact decrej_seg _ _ _ _ 72 96 16 _ k (win hk 0 11) (by rfl) (by decide)
    _ (k + 89) (k + 92) (win hk 89 3) (by rfl) (by rfl) hl
    _ (k + 93) (win hk 92 1) (by rfl) (by rfl) _ (win hk 93 2) (by rfl)
    s ra guard e0 e1 fp s2 hfp h2 R h_mem hguard (fun h => hlen (h.trans (by rfl)))
theorem _root_.Prysm.VoluntaryExit.Decode.example_reject_kind : ∀ (h : Host), type_of% (@Prysm.VoluntaryExit.Decode.example_reject h)
    = @Codec.decRejectKindN h Prysm.VoluntaryExit.Code.unmarshalSSZ 16 := by
  intro h; with_reducible rfl

theorem Decode.example_reject_kind : ∀ (h : Host), type_of% (@Decode.example_reject h)
    = @Codec.decRejectKindN h unmarshalSSZ 192 := by
  intro h; with_reducible rfl

end Prysm.PendingDeposit
