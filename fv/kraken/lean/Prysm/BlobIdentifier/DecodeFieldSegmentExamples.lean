import Codec.Kind.FixedBytesDecode
import Codec.Kind.InlineUint64
import Prysm.Eth1Data.Code
import Prysm.BlobIdentifier.Code

/-!
# Hand-written example instances of the `p2dec --gen2` lemmas on the development sites: the `BlobIdentifier` part

It holds the segment theorems of `BlobIdentifier.BlockRoot` and `BlobIdentifier.Index`. The declarations of the other types of this group are in `Prysm/DepositMessage/DecodeFieldSegmentExamples.lean`.
-/

open Machine Runtime Prysm.DepositMessage.Code
variable [Host]

open Codec
namespace Prysm.BlobIdentifier

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
/-- `BlockRoot` (32 bytes, SSZ offset 0, Go offset 8): decode segment, directives 13–36. -/
theorem _root_.Prysm.BlobIdentifier.Decode.example_field_BlockRoot_seg (k : Nat) (hk : Prysm.BlobIdentifier.Code.unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh Prysm.BlobIdentifier.Code.unmarshalSSZ k) :
    ∀ (sp rcv bf aR aB aS aRet aLo aP aL aC : BitVec 64) (St : Nat)
    (hR : sp + (48 : Int64).toBitVec = aR) (hB' : sp + (56 : Int64).toBitVec = aB)
    (hS : sp + (24 : Int64).toBitVec = aS)
    (hRet : sp - 8 = aRet) (hLo : sp - 8 - BitVec.ofNat 64 St = aLo)
    (hP : rcv + (8 : Int64).toBitVec = aP) (hL : rcv + (16 : Int64).toBitVec = aL)
    (hC : rcv + (24 : Int64).toBitVec = aC)
    (rbp0 r140 : UInt64) (root : List UInt8) (hroot : root.length = 32)
    (spl rslot lo lS vP vL vC : List UInt8)
    (hspl : spl.length = 24) (hrs : rslot.length = 8) (hlo : lo.length = St) (hlS : lS.length = 8)
    (hvP : vP.length = 8) (hvL : vL.length = 8) (hvC : vC.length = 8)
    (R : DataMem → Prop) (Heap : Nat → DataMem → Prop) (avail : Nat) (hav : 32 ≤ avail)
    (s : MachineData) (hrsp : s.regs.rsp = { toBitVec := sp }) (hrbp : s.regs.rbp = rbp0)
    (hr14 : s.regs.r14 = r140)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 rcv.toInt).At aR) ⋆ Eq ((Int.toBytes 8 bf.toInt).At aB)
      ⋆ Eq (spl.At sp) ⋆ Eq (rslot.At aRet) ⋆ Eq (lo.At aLo) ⋆ Eq (lS.At aS)
      ⋆ Heap avail
      ⋆ Eq (vP.At aP) ⋆ Eq (vL.At aL) ⋆ Eq (vC.At aC)
      ⋆ Eq (root.At bf)
      ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R)
    (hms : MakesliceC Heap ElfData.PrysmTarget.e2eU8Type_addr 1 St) (hmm : MemmoveC St),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 26 + 11) ∧ st.data.regs.rsp = { toBitVec := sp }
        ∧ st.data.regs.rbp = rbp0 ∧ st.data.regs.r14 = r140 ∧
        ∃ (p : BitVec 64) (spl' lo' : List UInt8), spl'.length = 24 ∧ lo'.length = St
          ∧ st.data.regs.rdx.toBitVec = rcv ∧
        (Eq ((Int.toBytes 8 rcv.toInt).At aR) ⋆ Eq ((Int.toBytes 8 bf.toInt).At aB)
          ⋆ Eq (spl'.At sp)
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 26 + 5 + 1)).toBitVec.toInt).At aRet)
          ⋆ Eq (lo'.At aLo)
          ⋆ Eq ((Int.toBytes 8 p.toInt).At aS)
          ⋆ Heap (avail - 32)
          ⋆ Eq ((Int.toBytes 8 p.toInt).At aP) ⋆ Eq ((Int.toBytes 8 32).At aL)
          ⋆ Eq ((Int.toBytes 8 32).At aC) ⋆ Eq (root.At p)
          ⋆ Eq (root.At bf)
          ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf (k + 13)⟩ := by
  have hA := Codec.infix_sub (q := Codec.bytesDecHead 32 "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlobIdentifier.UnmarshalSSZ_75" 48 16 24) 13 hk
    (by simp only [Prysm.BlobIdentifier.Code.unmarshalSSZ, Codec.bytesDecHead, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero])
  have hB := Codec.infix_sub (q := Codec.bytesDecMidZ 32 "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlobIdentifier.UnmarshalSSZ_75" "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlobIdentifier.UnmarshalSSZ_b2" 48 56 24 8 16 24) 26 hk
    (by simp only [Prysm.BlobIdentifier.Code.unmarshalSSZ, Codec.bytesDecMidZ, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero])
  have hl := Machine.label_at' hk hf (j := 26)
    (by simp only [Prysm.BlobIdentifier.Code.unmarshalSSZ, List.getElem?_cons_succ, List.getElem?_cons_zero]; rfl)
    (by simp only [Prysm.BlobIdentifier.Code.unmarshalSSZ, List.take_succ_cons, List.take_zero, List.contains_cons, List.contains_nil]; decide)
  with_reducible exact Codec.bytesdec_seg_z 32 (Or.inl rfl) _ _ _ _ _ _ _ _ (k + 13) (k + 26) hA hB hl
theorem _root_.Prysm.BlobIdentifier.Decode.example_field_BlockRoot_seg_kind : ∀ (h : Host), type_of% (@Prysm.BlobIdentifier.Decode.example_field_BlockRoot_seg h) = @Codec.bytesDecSegZKind h 32 Prysm.BlobIdentifier.Code.unmarshalSSZ 13 26 48 56 24 8 16 24 := by
  intro h; with_reducible rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- `Index` (inline uint64, SSZ offset 32, Go offset 32): decode segment, directives 47–49, scratch register rcx. -/
theorem _root_.Prysm.BlobIdentifier.Decode.example_field_Index_seg (k : Nat) (hk : Prysm.BlobIdentifier.Code.unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh Prysm.BlobIdentifier.Code.unmarshalSSZ k) :
    ∀ (sp rcv bf aB aSrc aF : BitVec 64)
    (hB' : sp + (56 : Int64).toBitVec = aB) (hSrc : bf + (32 : Int64).toBitVec = aSrc)
    (hF : rcv + (32 : Int64).toBitVec = aF)
    (rbp0 r140 : UInt64) (v vF : List UInt8) (hv : v.length = 8) (hvF : vF.length = 8)
    (R : DataMem → Prop)
    (s : MachineData) (hrsp : s.regs.rsp = { toBitVec := sp }) (hrbp : s.regs.rbp = rbp0)
    (hr14 : s.regs.r14 = r140) (hrdx : s.regs.rdx.toBitVec = rcv)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 bf.toInt).At aB) ⋆ Eq (v.At aSrc) ⋆ Eq (vF.At aF) ⋆ R),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 47 + 3) ∧ st.data.regs.rsp = { toBitVec := sp }
        ∧ st.data.regs.rbp = rbp0 ∧ st.data.regs.r14 = r140 ∧ st.data.regs.rdx.toBitVec = rcv ∧
        (Eq ((Int.toBytes 8 bf.toInt).At aB) ⋆ Eq (v.At aSrc) ⋆ Eq (v.At aF) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf (k + 47)⟩ := by
  have hA := Codec.infix_sub (q := Codec.u64DecInline Reg64.rcx 56 32 32) 47 hk
    (by simp only [Prysm.BlobIdentifier.Code.unmarshalSSZ, Codec.u64DecInline, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero])
  have hX : Codec.U64InlineReg Reg64.rcx := by decide
  with_reducible exact Codec.u64dec_inline_seg Reg64.rcx hX _ _ _ (k + 47) hA
theorem _root_.Prysm.BlobIdentifier.Decode.example_field_Index_seg_kind : ∀ (h : Host), type_of% (@Prysm.BlobIdentifier.Decode.example_field_Index_seg h) = @Codec.u64DecInlineSegKind h Prysm.BlobIdentifier.Code.unmarshalSSZ 47 56 32 32 := by
  intro h; with_reducible rfl

end Prysm.BlobIdentifier
