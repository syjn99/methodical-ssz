import Prysm.BlobIdentifier.DecodeRejectSizeKindInstances
import Prysm.PendingDeposit.GeneratedDecodeSteps

/-!
# Worked examples: size-reject theorems in generated style: the `VoluntaryExit` part

It holds the size-reject theorem of `VoluntaryExit` (frame `0x48`, size 16) and its kind line. The declarations of the other types of this group are in `Prysm/PendingDeposit/DecodeRejectSizeExample.lean`.
-/

open Machine Runtime Prysm.PendingDeposit.Code
variable [Host]

open Codec
namespace Prysm.VoluntaryExit

set_option maxRecDepth 100000 in
/-- VoluntaryExit: size reject (frame `0x48`, size 16); statement = the kind instance. -/
theorem _root_.Prysm.VoluntaryExit.Decode.example_reject : ∀ (k : Nat) (hk : Prysm.VoluntaryExit.Code.unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh Prysm.VoluntaryExit.Code.unmarshalSSZ k)
    (s : MachineData) (ra guard e0 e1 : UInt64) (fp s2 : List UInt8) (hfp : fp.length = 8) (h2 : s2.length = 8)
    (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At ElfData.PrysmTarget.sszErrSize_addr)
      ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrSize" + 8).toBitVec) ⋆ R)
    (hguard : guard.toNat < s.regs.rsp.toNat) (hlen : s.regs.rcx ≠ 16),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = e0 ∧ st.data.regs.rbx = e1
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14
        ∧ (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At ElfData.PrysmTarget.sszErrSize_addr)
          ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrSize" + 8).toBitVec) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  intro k hk hf s ra guard e0 e1 fp s2 hfp h2 R h_mem hguard hlen
  have hl := Machine.label_at' hk hf (j := 89)
    (by simp only [Prysm.VoluntaryExit.Code.unmarshalSSZ, List.getElem?_cons_succ, List.getElem?_cons_zero]; rfl)
    (by simp only [Prysm.VoluntaryExit.Code.unmarshalSSZ, List.take_succ_cons, List.take_zero, List.contains_cons, List.contains_nil]; decide)
  exact dec_reject_seg _ _ _ _ 72 96 16 _ k (window_infix_at hk 0 11) (by rfl) (by decide)
    _ (k + 89) (k + 92) (window_infix_at hk 89 3) (by rfl) (by rfl) hl
    _ (k + 93) (window_infix_at hk 92 1) (by rfl) (by rfl) _ (window_infix_at hk 93 2) (by rfl)
    s ra guard e0 e1 fp s2 hfp h2 R h_mem hguard (fun h => hlen (h.trans (by rfl)))
theorem _root_.Prysm.VoluntaryExit.Decode.example_reject_kind : ∀ (h : Host), type_of% (@Prysm.VoluntaryExit.Decode.example_reject h)
    = @Codec.decRejectKindAnyFrame h Prysm.VoluntaryExit.Code.unmarshalSSZ 16 := by
  intro h; with_reducible rfl

end Prysm.VoluntaryExit
