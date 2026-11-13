import Codec.Kind.CalleeDecode
import Codec.FixedBytesDecodePadding
import Prysm.Deposit_Data.Code
import Prysm.BeaconBlockHeader.Code
import Prysm.AttestationData.Code
import Prysm.Checkpoint.Code

/-!
# Hand-written example instances of the `decoder --call-segments` lemmas on the development sites: the `Checkpoint` part

It holds the argument set-up and the call block of `Checkpoint.Epoch`. The declarations of the other types of this group are in `Prysm/PendingPartialWithdrawal/DecodeCallSegmentExamples.lean`.
-/

open Machine Runtime
variable [Host]

open Codec
namespace Prysm.Checkpoint

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- `Epoch` (callee decoder field, Go offset 8): argument set-up, first-field form, directives 14–16 (padding `nop`). -/
theorem _root_.Prysm.Checkpoint.Decode.example_call_Epoch_arg (k : Nat) (hk : Prysm.Checkpoint.Code.unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh Prysm.Checkpoint.Code.unmarshalSSZ k) :
    ∀
    (rcv aF : BitVec 64) (hF : rcv + (8 : Int64).toBitVec = aF)
    (s : MachineData) (hrax : s.regs.rax.toBitVec = rcv),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 14 + 2 + padLen true) ∧ st.data.regs.rsp = s.regs.rsp
        ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14 ∧ st.data.regs.rbx = s.regs.rbx
        ∧ st.data.regs.rax.toBitVec = aF ∧ st.data.regs.rcx = 8 ∧ st.data.dmem = s.dmem)
      ⟨s, Host.addrOf (k + 14)⟩ := by
  have hA := Codec.infix_sub (q := Codec.callArgFirst true 8) 14 hk
    (by simp only [Prysm.Checkpoint.Code.unmarshalSSZ, Codec.callArgFirst, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero])
  with_reducible exact Codec.callarg_first_seg true _ (k + 14) hA
theorem _root_.Prysm.Checkpoint.Decode.example_call_Epoch_arg_kind : ∀ (h : Host), type_of% (@Prysm.Checkpoint.Decode.example_call_Epoch_arg h) = @Codec.callArgFirstKind h Prysm.Checkpoint.Code.unmarshalSSZ true 8 14 := by
  intro h; with_reducible rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- `Epoch`: call block of the callee decoder, directives 17–19, continuation label at 47. -/
theorem _root_.Prysm.Checkpoint.Decode.example_call_Epoch_call (k : Nat) (hk : Prysm.Checkpoint.Code.unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh Prysm.Checkpoint.Code.unmarshalSSZ k) :
    ∀ (hC : U64CalleeAcc "github.com_OffchainLabs_prysm_v7_consensus_types_primitives.Epoch.UnmarshalSSZ")
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
      ⟨s, Host.addrOf (k + 17)⟩ := by
  have hA := Codec.infix_sub (q := Codec.callDec "github.com_OffchainLabs_prysm_v7_consensus_types_primitives.Epoch.UnmarshalSSZ" "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Checkpoint.UnmarshalSSZ_b4") 17 hk
    (by simp only [Prysm.Checkpoint.Code.unmarshalSSZ, Codec.callDec, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero])
  have hB := Codec.infix_sub (q := Codec.callDecL "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Checkpoint.UnmarshalSSZ_b4") 47 hk
    (by simp only [Prysm.Checkpoint.Code.unmarshalSSZ, Codec.callDecL, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero])
  have hl := Machine.label_at' hk hf (j := 47)
    (by simp only [Prysm.Checkpoint.Code.unmarshalSSZ, List.getElem?_cons_succ, List.getElem?_cons_zero]; rfl)
    (by simp only [Prysm.Checkpoint.Code.unmarshalSSZ, List.take_succ_cons, List.take_zero, List.contains_cons, List.contains_nil]; decide)
  with_reducible exact Codec.calldec_seg _ _ (k + 17) (k + 47) hA hB hl
theorem _root_.Prysm.Checkpoint.Decode.example_call_Epoch_call_kind : ∀ (h : Host), type_of% (@Prysm.Checkpoint.Decode.example_call_Epoch_call h) = @Codec.callDecSegKind h Prysm.Checkpoint.Code.unmarshalSSZ "github.com_OffchainLabs_prysm_v7_consensus_types_primitives.Epoch.UnmarshalSSZ" "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Checkpoint.UnmarshalSSZ_b4" 17 47 := by
  intro h; with_reducible rfl

end Prysm.Checkpoint
