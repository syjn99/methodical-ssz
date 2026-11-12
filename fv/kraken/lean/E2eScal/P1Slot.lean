import Codec.Uint64Decoder
import Prysm.Slot.DecodeAccept

/-!
# In-sample check of the uint64 decoder pattern: the Slot decoder accept path from `u64dec_accept`

`sl_unmarshal_accept_main_s` has the statement of `Prysm.Slot.Decode.accept`
(`Prysm/Slot/DecodeAccept.lean`) word for word; its proof only instantiates `Codec.u64dec_accept`
(labels of the Slot `.S`, frame size 0x48, spill displacement 0x60, head block at k,
tail block at k + 43). `sl_same_stmt` checks that the two statements are the same
proposition (proof irrelevance: `rfl` succeeds only if the types are definitionally equal).
The hand theorem stays in the tree, unchanged.
-/

open Machine TestTarget Prysm.AttestationData.Code
variable [Host]

open Codec
namespace E2eScal

set_option maxRecDepth 100000 in
theorem sl_unmarshal_accept_main_s (k : Nat) (hk : slotUnmarshalSSZ.IsInfixAt Host.prog k)
    (hf : LabelsFresh slotUnmarshalSSZ k)
    (e8 : List UInt8) (he8 : e8.length = 8)
    (s : MachineData) (ra guard : UInt64) (fp s2 c0 : List UInt8)
    (hfp : fp.length = 8) (h2 : s2.length = 8) (hc0 : c0.length = 8) (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq (e8.At s.regs.rbx.toBitVec) ⋆ Eq (c0.At s.regs.rax.toBitVec) ⋆ R)
    (hguard : guard.toNat < s.regs.rsp.toNat) (hlen : s.regs.rcx = 8) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14
        ∧ (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (e8.At s.regs.rbx.toBitVec) ⋆ Eq (e8.At s.regs.rax.toBitVec) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  have hA := infix_sub (q := u64DecHead
    "github.com_OffchainLabs_prysm_v7_consensus_types_primitives.Slot.UnmarshalSSZ"
    "L_github.com_OffchainLabs_prysm_v7_consensus_types_primitives.Slot.UnmarshalSSZ_0"
    "L_github.com_OffchainLabs_prysm_v7_consensus_types_primitives.Slot.UnmarshalSSZ_cc"
    "L_github.com_OffchainLabs_prysm_v7_consensus_types_primitives.Slot.UnmarshalSSZ_bb" 72 96) 0 hk
    (by simp only [slotUnmarshalSSZ, u64DecHead, List.drop_zero, List.length_cons, List.length_nil,
      List.take_succ_cons, List.take_zero])
  have hB := infix_sub (q := u64DecTail
    "L_github.com_OffchainLabs_prysm_v7_consensus_types_primitives.Slot.UnmarshalSSZ_bb" 72) 43 hk
    (by simp only [slotUnmarshalSSZ, u64DecTail, List.drop_succ_cons, List.drop_zero, List.length_cons,
      List.length_nil, List.take_succ_cons, List.take_zero])
  have hl := Machine.label_at' hk hf (j := 43)
    (by simp only [slotUnmarshalSSZ, List.getElem?_cons_succ, List.getElem?_cons_zero]; rfl)
    (by simp only [slotUnmarshalSSZ, List.take_succ_cons, List.take_zero, List.contains_cons, List.contains_nil]; decide)
  exact u64dec_accept _ _ _ _ 72 96 (by decide) k (k + 43) hA hB hl e8 he8 s ra guard fp s2 c0 hfp h2 hc0 R
    h_mem hguard hlen

/-- The in-sample statement is the hand statement (same proposition). -/
theorem sl_same_stmt : @Prysm.Slot.Decode.accept = @sl_unmarshal_accept_main_s := rfl

end E2eScal
