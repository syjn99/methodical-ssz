import Codec.Kind.CalleeDecode
import Codec.FixedBytesDecodePadding
import Prysm.Deposit_Data.Code
import Prysm.BeaconBlockHeader.Code
import Prysm.AttestationData.Code
import Prysm.Checkpoint.Code

/-!
# Hand-written example instances of the `p2dec --gen3` lemmas on the development sites: the `AttestationData` part

It holds the argument set-ups and call blocks of `AttestationData.Slot` and `AttestationData.CommitteeIndex`. The declarations of the other types of this group are in `Prysm/PendingPartialWithdrawal/DecodeCallSegmentExamples.lean`.
-/

open Machine Runtime
variable [Host]

open Codec
namespace Prysm.AttestationData

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- `Slot` (callee decoder field, Go offset 8): argument set-up, first-field form, directives 15–16. -/
theorem _root_.Prysm.AttestationData.Decode.example_call_Slot_arg (k : Nat) (hk : Prysm.AttestationData.Code.unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh Prysm.AttestationData.Code.unmarshalSSZ k) :
    ∀
    (rcv aF : BitVec 64) (hF : rcv + (8 : Int64).toBitVec = aF)
    (s : MachineData) (hrax : s.regs.rax.toBitVec = rcv),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 15 + 2 + padLen false) ∧ st.data.regs.rsp = s.regs.rsp
        ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14 ∧ st.data.regs.rbx = s.regs.rbx
        ∧ st.data.regs.rax.toBitVec = aF ∧ st.data.regs.rcx = 8 ∧ st.data.dmem = s.dmem)
      ⟨s, Host.addrOf (k + 15)⟩ := by
  have hA := Codec.infix_sub (q := Codec.callArgFirst false 8) 15 hk
    (by simp only [Prysm.AttestationData.Code.unmarshalSSZ, Codec.callArgFirst, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero])
  with_reducible exact Codec.callarg_first_seg false _ (k + 15) hA
theorem _root_.Prysm.AttestationData.Decode.example_call_Slot_arg_kind : ∀ (h : Host), type_of% (@Prysm.AttestationData.Decode.example_call_Slot_arg h) = @Codec.callArgFirstKind h Prysm.AttestationData.Code.unmarshalSSZ false 8 15 := by
  intro h; with_reducible rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- `Slot`: call block of the callee decoder, directives 17–19, continuation label at 47. -/
theorem _root_.Prysm.AttestationData.Decode.example_call_Slot_call (k : Nat) (hk : Prysm.AttestationData.Code.unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh Prysm.AttestationData.Code.unmarshalSSZ k) :
    ∀ (hC : U64CalleeAcc "github.com_OffchainLabs_prysm_v7_consensus_types_primitives.Slot.UnmarshalSSZ")
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
  have hA := Codec.infix_sub (q := Codec.callDec "github.com_OffchainLabs_prysm_v7_consensus_types_primitives.Slot.UnmarshalSSZ" "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttestationData.UnmarshalSSZ_c7") 17 hk
    (by simp only [Prysm.AttestationData.Code.unmarshalSSZ, Codec.callDec, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero])
  have hB := Codec.infix_sub (q := Codec.callDecL "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttestationData.UnmarshalSSZ_c7") 47 hk
    (by simp only [Prysm.AttestationData.Code.unmarshalSSZ, Codec.callDecL, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero])
  have hl := Machine.label_at' hk hf (j := 47)
    (by simp only [Prysm.AttestationData.Code.unmarshalSSZ, List.getElem?_cons_succ, List.getElem?_cons_zero]; rfl)
    (by simp only [Prysm.AttestationData.Code.unmarshalSSZ, List.take_succ_cons, List.take_zero, List.contains_cons, List.contains_nil]; decide)
  with_reducible exact Codec.calldec_seg _ _ (k + 17) (k + 47) hA hB hl
theorem _root_.Prysm.AttestationData.Decode.example_call_Slot_call_kind : ∀ (h : Host), type_of% (@Prysm.AttestationData.Decode.example_call_Slot_call h) = @Codec.callDecSegKind h Prysm.AttestationData.Code.unmarshalSSZ "github.com_OffchainLabs_prysm_v7_consensus_types_primitives.Slot.UnmarshalSSZ" "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttestationData.UnmarshalSSZ_c7" 17 47 := by
  intro h; with_reducible rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- `CommitteeIndex` (callee decoder field, SSZ offset 8, Go offset 16): argument set-up by reload, directives 48–54. -/
theorem _root_.Prysm.AttestationData.Decode.example_call_CommitteeIndex_arg (k : Nat) (hk : Prysm.AttestationData.Code.unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh Prysm.AttestationData.Code.unmarshalSSZ k) :
    ∀
    (sp rcv bf aB aD aR aSrc aF : BitVec 64)
    (hB' : sp + (136 : Int64).toBitVec = aB) (hD : sp + (152 : Int64).toBitVec = aD) (hR : sp + (128 : Int64).toBitVec = aR)
    (hSrc : bf + (8 : Int64).toBitVec = aSrc) (hF : rcv + (16 : Int64).toBitVec = aF)
    (vD : List UInt8) (hvD : vD.length = 8) (R : DataMem → Prop)
    (s : MachineData) (hrsp : s.regs.rsp = { toBitVec := sp })
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 bf.toInt).At aB) ⋆ Eq (vD.At aD)
      ⋆ Eq ((Int.toBytes 8 rcv.toInt).At aR) ⋆ R),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 48 + 7 + padLen false) ∧ st.data.regs.rsp = s.regs.rsp
        ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14
        ∧ st.data.regs.rbx.toBitVec = aSrc ∧ st.data.regs.rax.toBitVec = aF ∧ st.data.regs.rcx = 8
        ∧ st.data.dmem = s.dmem)
      ⟨s, Host.addrOf (k + 48)⟩ := by
  have hA := Codec.infix_sub (q := Codec.callArgReload false 136 8 152 (-8) 128 16) 48 hk
    (by simp only [Prysm.AttestationData.Code.unmarshalSSZ, Codec.callArgReload, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero])
  with_reducible exact Codec.callarg_reload_seg false _ _ _ _ _ _ (k + 48) hA
theorem _root_.Prysm.AttestationData.Decode.example_call_CommitteeIndex_arg_kind : ∀ (h : Host), type_of% (@Prysm.AttestationData.Decode.example_call_CommitteeIndex_arg h) = @Codec.callArgReloadKind h Prysm.AttestationData.Code.unmarshalSSZ false 136 8 152 (-8) 128 16 48 := by
  intro h; with_reducible rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- `CommitteeIndex`: call block of the callee decoder, directives 55–57, continuation label at 85. -/
theorem _root_.Prysm.AttestationData.Decode.example_call_CommitteeIndex_call (k : Nat) (hk : Prysm.AttestationData.Code.unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh Prysm.AttestationData.Code.unmarshalSSZ k) :
    ∀ (hC : U64CalleeAcc "github.com_OffchainLabs_prysm_v7_consensus_types_primitives.CommitteeIndex.UnmarshalSSZ")
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
      (fun st => st.pc = Host.addrOf (k + 85 + 1) ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0
        ∧ st.data.regs.rsp = { toBitVec := sp } ∧ st.data.regs.rbp = rbp0 ∧ st.data.regs.r14 = r140 ∧
        (Eq ((Int.toBytes 8 (Host.addrOf (k + 55 + 1)).toBitVec.toInt).At aRet)
          ⋆ Eq ((Int.toBytes 8 rbp0.toBitVec.toInt).At aFp) ⋆ Eq ((Int.toBytes 8 src.toInt).At aS2)
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (r140.toBitVec + 16))
          ⋆ Eq (e8.At src) ⋆ Eq (e8.At dst) ⋆ F) st.data.dmem)
      ⟨s, Host.addrOf (k + 55)⟩ := by
  have hA := Codec.infix_sub (q := Codec.callDec "github.com_OffchainLabs_prysm_v7_consensus_types_primitives.CommitteeIndex.UnmarshalSSZ" "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttestationData.UnmarshalSSZ_167") 55 hk
    (by simp only [Prysm.AttestationData.Code.unmarshalSSZ, Codec.callDec, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero])
  have hB := Codec.infix_sub (q := Codec.callDecL "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttestationData.UnmarshalSSZ_167") 85 hk
    (by simp only [Prysm.AttestationData.Code.unmarshalSSZ, Codec.callDecL, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero])
  have hl := Machine.label_at' hk hf (j := 85)
    (by simp only [Prysm.AttestationData.Code.unmarshalSSZ, List.getElem?_cons_succ, List.getElem?_cons_zero]; rfl)
    (by simp only [Prysm.AttestationData.Code.unmarshalSSZ, List.take_succ_cons, List.take_zero, List.contains_cons, List.contains_nil]; decide)
  with_reducible exact Codec.calldec_seg _ _ (k + 55) (k + 85) hA hB hl
theorem _root_.Prysm.AttestationData.Decode.example_call_CommitteeIndex_call_kind : ∀ (h : Host), type_of% (@Prysm.AttestationData.Decode.example_call_CommitteeIndex_call h) = @Codec.callDecSegKind h Prysm.AttestationData.Code.unmarshalSSZ "github.com_OffchainLabs_prysm_v7_consensus_types_primitives.CommitteeIndex.UnmarshalSSZ" "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttestationData.UnmarshalSSZ_167" 55 85 := by
  intro h; with_reducible rfl

end Prysm.AttestationData
