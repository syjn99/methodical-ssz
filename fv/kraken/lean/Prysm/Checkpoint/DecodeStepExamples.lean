import Codec.Kind.WindowSteps
import Codec.Kind.FixedBytesDecodeWindow
import Codec.CalleeDecodeWindow
import Prysm.SyncCommitteeMessage.Code
import Prysm.Deposit_Data.Code
import Prysm.BeaconBlockHeader.Code
import Prysm.Checkpoint.Code

/-!
# Example instances of the window and step mechanisms on the development sites: the `Checkpoint` part

It holds the steps and the call block of `Checkpoint.Epoch` (`decoder --call-segments` first-field set-up form with pad). The declarations of the other types of this group are in `Prysm/SyncCommitteeMessage/DecodeStepExamples.lean`.
-/

open Machine Runtime Prysm.Checkpoint.Code
variable [Host]

open Codec
namespace Prysm.Checkpoint

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Directive 14 `add $0x8,%rax`: stepAddKind. -/
theorem _root_.Prysm.Checkpoint.Decode.example_step_directive_14 (k : Nat) (hk : unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh unmarshalSSZ k) :
    ∀
    (final : MachineState → Prop) (s : MachineData)
    (hk' : ∀ fl : StatusFlags, Eventually (step1 Host.exe) final
      ⟨{ regs := s.regs.set64 Reg64.rax (s.regs.get64 Reg64.rax + (8 : Int64).toBitVec), zmms := s.zmms, status := fl, dmem := s.dmem },
        Host.addrOf (k + 15)⟩),
    Eventually (step1 Host.exe) final ⟨s, Host.addrOf (k + 14)⟩ := by
  have hq := Codec.window_infix_at hk 14 1
  have he : Codec.eraseNop ((unmarshalSSZ.drop 14).take 1) = [Codec.instrAddImmediate Reg64.rax 8] := by rfl
  have hend : k + 14 + ((unmarshalSSZ.drop 14).take 1).length = k + 15 := by rfl
  with_reducible exact Codec.step_add_immediate Reg64.rax 8 _ (k + 14) (k + 15) hq he hend
theorem _root_.Prysm.Checkpoint.Decode.example_step_directive_14_kind : ∀ (h : Host), type_of% (@Prysm.Checkpoint.Decode.example_step_directive_14 h) = @Codec.stepAddKind h unmarshalSSZ Reg64.rax 8 14 15 := by
  intro h; with_reducible rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Directive 15 `mov $0x8,%ecx`: stepMoveImmediateKind. -/
theorem _root_.Prysm.Checkpoint.Decode.example_step_directive_15 (k : Nat) (hk : unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh unmarshalSSZ k) :
    ∀
    (final : MachineState → Prop) (s : MachineData)
    (hk' : Eventually (step1 Host.exe) final ⟨Codec.setRegister s Reg64.rcx (BitVec.zeroExtend 64 (BitVec.truncate 32 (8 : Int64).toBitVec)), Host.addrOf (k + 16)⟩),
    Eventually (step1 Host.exe) final ⟨s, Host.addrOf (k + 15)⟩ := by
  have hq := Codec.window_infix_at hk 15 1
  have he : Codec.eraseNop ((unmarshalSSZ.drop 15).take 1) = [Codec.instrMoveImmediate32 Reg64.rcx 8] := by rfl
  have hend : k + 15 + ((unmarshalSSZ.drop 15).take 1).length = k + 16 := by rfl
  with_reducible exact Codec.step_move_immediate Reg64.rcx 8 _ (k + 15) (k + 16) hq he hend
theorem _root_.Prysm.Checkpoint.Decode.example_step_directive_15_kind : ∀ (h : Host), type_of% (@Prysm.Checkpoint.Decode.example_step_directive_15 h) = @Codec.stepMoveImmediateKind h unmarshalSSZ Reg64.rcx 8 15 16 := by
  intro h; with_reducible rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- `Epoch`: call block over the window 16–19 (`nop; callq; test; je`), `callq` at 17, continuation label at 47. -/
theorem _root_.Prysm.Checkpoint.Decode.example_step_Epoch_call (k : Nat) (hk : unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh unmarshalSSZ k) :
    ∀ (hC : U64CalleeAccept "github.com_OffchainLabs_prysm_v7_consensus_types_primitives.Epoch.UnmarshalSSZ")
    (sp dst src aRet aFp aS2 : BitVec 64)
    (hRet : sp - 8 = aRet) (hFp : sp - 16 = aFp) (hS2 : sp + 8 = aS2)
    (rbp0 r140 guard : UInt64) (e8 rslot fp s2 c0 : List UInt8)
    (he8 : e8.length = 8) (hrs : rslot.length = 8) (hfp : fp.length = 8) (hs2 : s2.length = 8)
    (hc0 : c0.length = 8) (hguard : guard.toNat < aRet.toNat)
    (F : DataMem → Prop)
    (s : MachineData) (hrsp : s.regs.rsp = { toBitVec := sp }) (hrbp : s.regs.rbp = rbp0)
    (hr14 : s.regs.r14 = r140) (hrax : s.regs.rax.toBitVec = dst) (hrbx : s.regs.rbx.toBitVec = src)
    (hrcx : s.regs.rcx = 8)
    (h_mem : s.dmem =⋆ Eq (rslot.At aRet) ⋆ Eq (fp.At aFp) ⋆ Eq (s2.At aS2)
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (r140.toBitVec + 16))
      ⋆ Eq (e8.At src) ⋆ Eq (c0.At dst) ⋆ F),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 47 + 1) ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0
        ∧ st.data.regs.rsp = { toBitVec := sp } ∧ st.data.regs.rbp = rbp0 ∧ st.data.regs.r14 = r140 ∧
        (Eq ((Int.toBytes 8 (Host.addrOf (k + 17 + 1)).toBitVec.toInt).At aRet)
          ⋆ Eq ((Int.toBytes 8 rbp0.toBitVec.toInt).At aFp) ⋆ Eq ((Int.toBytes 8 src.toInt).At aS2)
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (r140.toBitVec + 16))
          ⋆ Eq (e8.At src) ⋆ Eq (e8.At dst) ⋆ F) st.data.dmem)
      ⟨s, Host.addrOf (k + 16)⟩ := by
  have hq := Codec.window_infix_at hk 16 4
  have he : Codec.eraseNop ((unmarshalSSZ.drop 16).take 4) = Codec.callDec "github.com_OffchainLabs_prysm_v7_consensus_types_primitives.Epoch.UnmarshalSSZ" "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Checkpoint.UnmarshalSSZ_b4" := by rfl
  have hjc : k + 16 + Codec.nonNopIndex ((unmarshalSSZ.drop 16).take 4) 0 = k + 17 := by rfl
  have hB := Codec.infix_sub (q := Codec.callDecContinuationLabel "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Checkpoint.UnmarshalSSZ_b4") 47 hk
    (by simp only [unmarshalSSZ, Codec.callDecContinuationLabel, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero])
  have hl := Machine.label_at' hk hf (j := 47)
    (by simp only [unmarshalSSZ, List.getElem?_cons_succ, List.getElem?_cons_zero]; rfl)
    (by simp only [unmarshalSSZ, List.take_succ_cons, List.take_zero, List.contains_cons, List.contains_nil]; decide)
  with_reducible exact Codec.calldec_seg_window _ _ _ (k + 16) (k + 17) (k + 47) hq he hjc hB hl
theorem _root_.Prysm.Checkpoint.Decode.example_step_Epoch_call_kind : ∀ (h : Host), type_of% (@Prysm.Checkpoint.Decode.example_step_Epoch_call h) = @Codec.callDecSegKindWindow h unmarshalSSZ "github.com_OffchainLabs_prysm_v7_consensus_types_primitives.Epoch.UnmarshalSSZ" "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Checkpoint.UnmarshalSSZ_b4" 16 17 47 := by
  intro h; with_reducible rfl

end Prysm.Checkpoint
