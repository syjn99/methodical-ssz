import Codec.Kind.CalleeDecode
import Codec.FixedBytesDecodePadding
import Prysm.Deposit_Data.Code
import Prysm.BeaconBlockHeader.Code
import Prysm.AttestationData.Code
import Prysm.Checkpoint.Code

/-!
# Hand-written example instances of the `decoder --call-segments` lemmas on the development sites: the `Deposit_Data` part

It holds the padded byte segment of `Deposit_Data.WithdrawalCredentials`. The declarations of the other types of this group are in `Prysm/PendingPartialWithdrawal/DecodeCallSegmentExamples.lean`.
-/

open Machine Runtime
variable [Host]

open Codec
namespace Prysm.Deposit_Data

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
/-- `WithdrawalCredentials` (32 bytes, SSZ offset 48, Go offset 32): decode segment with the padding `nop` before `callq runtime.makeslice`, directives 47–72. -/
theorem _root_.Prysm.Deposit_Data.Decode.example_call_WithdrawalCredentials_segment (k : Nat) (hk : Prysm.Deposit_Data.Code.unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh Prysm.Deposit_Data.Code.unmarshalSSZ k) :
    ∀
    (sp rcv bf aR aB aS aRet aLo aP aL aC aSrc : BitVec 64) (St : Nat)
    (hR : sp + (48 : Int64).toBitVec = aR) (hB' : sp + (56 : Int64).toBitVec = aB) (hS : sp + (24 : Int64).toBitVec = aS)
    (hRet : sp - 8 = aRet) (hLo : sp - 8 - BitVec.ofNat 64 St = aLo)
    (hP : rcv + (32 : Int64).toBitVec = aP) (hL : rcv + (40 : Int64).toBitVec = aL) (hC : rcv + (48 : Int64).toBitVec = aC)
    (hSrc : bf + (48 : Int64).toBitVec = aSrc)
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
      ⋆ Eq (root.At aSrc)
      ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R)
    (hms : MakesliceContract Heap ElfData.PrysmTarget.typeUint8_addr 1 St) (hmm : MemmoveContract St),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 61 + 12) ∧ st.data.regs.rsp = { toBitVec := sp }
        ∧ st.data.regs.rbp = rbp0 ∧ st.data.regs.r14 = r140 ∧
        ∃ (p : BitVec 64) (spl' lo' : List UInt8), spl'.length = 24 ∧ lo'.length = St
          ∧ st.data.regs.rdx.toBitVec = rcv ∧
        (Eq ((Int.toBytes 8 rcv.toInt).At aR) ⋆ Eq ((Int.toBytes 8 bf.toInt).At aB)
          ⋆ Eq (spl'.At sp)
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 61 + 6 + 1)).toBitVec.toInt).At aRet)
          ⋆ Eq (lo'.At aLo)
          ⋆ Eq ((Int.toBytes 8 p.toInt).At aS)
          ⋆ Heap (avail - 32)
          ⋆ Eq ((Int.toBytes 8 p.toInt).At aP) ⋆ Eq ((Int.toBytes 8 32).At aL)
          ⋆ Eq ((Int.toBytes 8 32).At aC) ⋆ Eq (root.At p)
          ⋆ Eq (root.At aSrc)
          ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf (k + 47)⟩ := by
  have hA := Codec.infix_sub (q := Codec.bytesDecodeHeadOptionalPadding true 32 "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Deposit_Data.UnmarshalSSZ_113" 48 40 48) 47 hk
    (by simp only [Prysm.Deposit_Data.Code.unmarshalSSZ, Codec.bytesDecodeHeadOptionalPadding, Codec.bytesDecodeHeadPad, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero])
  have hB := Codec.infix_sub (q := Codec.bytesDecodeMiddle 32 "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Deposit_Data.UnmarshalSSZ_113" "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Deposit_Data.UnmarshalSSZ_154" 48 56 24 32 40 48 48) 61 hk
    (by simp only [Prysm.Deposit_Data.Code.unmarshalSSZ, Codec.bytesDecodeMiddle, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero])
  have hl := Machine.label_at' hk hf (j := 61)
    (by simp only [Prysm.Deposit_Data.Code.unmarshalSSZ, List.getElem?_cons_succ, List.getElem?_cons_zero]; rfl)
    (by simp only [Prysm.Deposit_Data.Code.unmarshalSSZ, List.take_succ_cons, List.take_zero, List.contains_cons, List.contains_nil]; decide)
  with_reducible exact Codec.bytes_decode_segment_optional_padding true 32 (Or.inl rfl) _ _ _ _ _ _ _ _ _ (k + 47) (k + 61) hA hB hl
theorem _root_.Prysm.Deposit_Data.Decode.example_call_WithdrawalCredentials_segment_kind : ∀ (h : Host), type_of% (@Prysm.Deposit_Data.Decode.example_call_WithdrawalCredentials_segment h) = @Codec.bytesDecodeSegmentKind h 32 Prysm.Deposit_Data.Code.unmarshalSSZ 47 61 48 56 24 32 40 48 48 := by
  intro h; with_reducible rfl

end Prysm.Deposit_Data
