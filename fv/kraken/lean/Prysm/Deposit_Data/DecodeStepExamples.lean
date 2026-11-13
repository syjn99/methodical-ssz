import Codec.Kind.WindowSteps
import Codec.Kind.FixedBytesDecodeWindow
import Codec.CalleeDecodeWindow
import Prysm.SyncCommitteeMessage.Code
import Prysm.Deposit_Data.Code
import Prysm.BeaconBlockHeader.Code
import Prysm.Checkpoint.Code

/-!
# Example instances of the window and step mechanisms on the development sites: the `Deposit_Data` part

It holds the byte segment of `Deposit_Data.WithdrawalCredentials` over two windows, with a `nop` before `callq runtime.makeslice`. The declarations of the other types of this group are in `Prysm/SyncCommitteeMessage/DecodeStepExamples.lean`.
-/

open Machine Runtime Prysm.Checkpoint.Code
variable [Host]

open Codec
namespace Prysm.Deposit_Data

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
/-- `WithdrawalCredentials` (32-byte vector): decode segment over the windows 47–56 and 61–72; receiver in rdx after makeslice, in rdx after memmove (`callq` at 67); a `nop` is inside the first window. -/
theorem _root_.Prysm.Deposit_Data.Decode.example_step_WithdrawalCredentials_segment (k : Nat) (hk : Prysm.Deposit_Data.Code.unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh Prysm.Deposit_Data.Code.unmarshalSSZ k) :
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
      (fun st => st.pc = Host.addrOf (k + 73) ∧ st.data.regs.rsp = { toBitVec := sp }
        ∧ st.data.regs.rbp = rbp0 ∧ st.data.regs.r14 = r140 ∧
        ∃ (p : BitVec 64) (spl' lo' : List UInt8), spl'.length = 24 ∧ lo'.length = St
          ∧ st.data.regs.get64 Reg64.rdx = rcv ∧
        (Eq ((Int.toBytes 8 rcv.toInt).At aR) ⋆ Eq ((Int.toBytes 8 bf.toInt).At aB)
          ⋆ Eq (spl'.At sp)
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 67 + 1)).toBitVec.toInt).At aRet)
          ⋆ Eq (lo'.At aLo)
          ⋆ Eq ((Int.toBytes 8 p.toInt).At aS)
          ⋆ Heap (avail - 32)
          ⋆ Eq ((Int.toBytes 8 p.toInt).At aP) ⋆ Eq ((Int.toBytes 8 32).At aL)
          ⋆ Eq ((Int.toBytes 8 32).At aC) ⋆ Eq (root.At p)
          ⋆ Eq (root.At aSrc)
          ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf (k + 47)⟩ := by
  have hqA := Codec.window_infix_at hk 47 10
  have heA : Codec.eraseNop ((Prysm.Deposit_Data.Code.unmarshalSSZ.drop 47).take 10) = Codec.bytesDecodeHeadRegister Reg64.rdx 32 "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Deposit_Data.UnmarshalSSZ_113" 48 40 48 := by rfl
  have hqB := Codec.window_infix_at hk 61 12
  have heB : Codec.eraseNop ((Prysm.Deposit_Data.Code.unmarshalSSZ.drop 61).take 12) = Codec.bytesDecodeMiddleRegisters Reg64.rdx Reg64.rdx 32 "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Deposit_Data.UnmarshalSSZ_113" "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Deposit_Data.UnmarshalSSZ_154" 48 56 24 32 40 48 48 := by rfl
  have hjl : k + 61 + Codec.nonNopIndex ((Prysm.Deposit_Data.Code.unmarshalSSZ.drop 61).take 12) 0 = k + 61 := by rfl
  have hl := Machine.label_at' hk hf (j := 61)
    (by simp only [Prysm.Deposit_Data.Code.unmarshalSSZ, List.getElem?_cons_succ, List.getElem?_cons_zero]; rfl)
    (by simp only [Prysm.Deposit_Data.Code.unmarshalSSZ, List.take_succ_cons, List.take_zero, List.contains_cons, List.contains_nil]; decide)
  have hjm : k + 61 + Codec.nonNopIndex ((Prysm.Deposit_Data.Code.unmarshalSSZ.drop 61).take 12) 6 = k + 67 := by rfl
  have hend : k + 61 + ((Prysm.Deposit_Data.Code.unmarshalSSZ.drop 61).take 12).length = k + 73 := by rfl
  with_reducible exact Codec.bytes_decode_segment_window 32 (Or.inl rfl) Reg64.rdx Reg64.rdx (Or.inl rfl) (Or.inr (Or.inr (Or.inl rfl))) _ _ _ _ _ _ _ _ _ _ _ (k + 47) (k + 61) (k + 61) (k + 67) (k + 73) hqA heA hqB heB hjl hl hjm hend
theorem _root_.Prysm.Deposit_Data.Decode.example_step_WithdrawalCredentials_segment_kind : ∀ (h : Host), type_of% (@Prysm.Deposit_Data.Decode.example_step_WithdrawalCredentials_segment h) = @Codec.bytesDecodeSegmentKindWindow h 32 Prysm.Deposit_Data.Code.unmarshalSSZ Reg64.rdx 47 67 73 48 56 24 32 40 48 48 := by
  intro h; with_reducible rfl

end Prysm.Deposit_Data
