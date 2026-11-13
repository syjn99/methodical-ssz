import Codec.Kind.WindowSteps
import Codec.Kind.FixedBytesDecodeWindow
import Codec.CalleeDecodeWindow
import Prysm.SyncCommitteeMessage.Code
import Prysm.Deposit_Data.Code
import Prysm.BeaconBlockHeader.Code
import Prysm.Checkpoint.Code

/-!
# Example instances of the window and step mechanisms on the development sites: the `PendingConsolidation` part

It holds the steps, the call block and the whole call field of `PendingConsolidation.TargetIndex`. The declarations of the other types of this group are in `Prysm/SyncCommitteeMessage/DecodeStepExamples.lean`.
-/

open Machine Runtime Prysm.Checkpoint.Code
variable [Host]

open Codec
namespace Prysm.PendingConsolidation

/-! ## PendingConsolidation.TargetIndex — `nop` after the callee call (missed by the hold-out run): reload set-up as steps, call window, whole field -/

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Directive 48 `mov 0x60(%rsp),%rbx`: stepLoadValueKind. -/
theorem _root_.Prysm.PendingConsolidation.Decode.example_step_s48 (k : Nat) (hk : Prysm.PendingConsolidation.Code.unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh Prysm.PendingConsolidation.Code.unmarshalSSZ k) :
    ∀
    (base a v : BitVec 64) (ha : base + (96 : Int64).toBitVec = a)
    (F : DataMem → Prop)
    (final : MachineState → Prop) (s : MachineData)
    (hb : s.regs.get64 Reg64.rsp = base) (hm : (Eq ((Int.toBytes 8 v.toInt).At a) ⋆ F) s.dmem)
    (hk' : Eventually (step1 Host.exe) final ⟨Codec.setRegister s Reg64.rbx v, Host.addrOf (k + 49)⟩),
    Eventually (step1 Host.exe) final ⟨s, Host.addrOf (k + 48)⟩ := by
  have hq := Codec.window_infix_at hk 48 1
  have he : Codec.eraseNop ((Prysm.PendingConsolidation.Code.unmarshalSSZ.drop 48).take 1) = [Codec.instrLoad Reg64.rbx Reg64.rsp 96] := by rfl
  have hend : k + 48 + ((Prysm.PendingConsolidation.Code.unmarshalSSZ.drop 48).take 1).length = k + 49 := by rfl
  with_reducible exact Codec.step_load_value Reg64.rbx Reg64.rsp 96 _ (k + 48) (k + 49) hq he hend
theorem _root_.Prysm.PendingConsolidation.Decode.example_step_s48_kind : ∀ (h : Host), type_of% (@Prysm.PendingConsolidation.Decode.example_step_s48 h) = @Codec.stepLoadValueKind h Prysm.PendingConsolidation.Code.unmarshalSSZ Reg64.rbx Reg64.rsp 96 48 49 := by
  intro h; with_reducible rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Directive 49 `add $0x8,%rbx`: stepAddKind. -/
theorem _root_.Prysm.PendingConsolidation.Decode.example_step_s49 (k : Nat) (hk : Prysm.PendingConsolidation.Code.unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh Prysm.PendingConsolidation.Code.unmarshalSSZ k) :
    ∀
    (final : MachineState → Prop) (s : MachineData)
    (hk' : ∀ fl : StatusFlags, Eventually (step1 Host.exe) final
      ⟨{ regs := s.regs.set64 Reg64.rbx (s.regs.get64 Reg64.rbx + (8 : Int64).toBitVec), zmms := s.zmms, status := fl, dmem := s.dmem },
        Host.addrOf (k + 50)⟩),
    Eventually (step1 Host.exe) final ⟨s, Host.addrOf (k + 49)⟩ := by
  have hq := Codec.window_infix_at hk 49 1
  have he : Codec.eraseNop ((Prysm.PendingConsolidation.Code.unmarshalSSZ.drop 49).take 1) = [Codec.instrAddImmediate Reg64.rbx 8] := by rfl
  have hend : k + 49 + ((Prysm.PendingConsolidation.Code.unmarshalSSZ.drop 49).take 1).length = k + 50 := by rfl
  with_reducible exact Codec.step_add_immediate Reg64.rbx 8 _ (k + 49) (k + 50) hq he hend
theorem _root_.Prysm.PendingConsolidation.Decode.example_step_s49_kind : ∀ (h : Host), type_of% (@Prysm.PendingConsolidation.Decode.example_step_s49 h) = @Codec.stepAddKind h Prysm.PendingConsolidation.Code.unmarshalSSZ Reg64.rbx 8 49 50 := by
  intro h; with_reducible rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Directive 50 `mov 0x70(%rsp),%rdi`: stepLoadBytesKind. -/
theorem _root_.Prysm.PendingConsolidation.Decode.example_step_s50 (k : Nat) (hk : Prysm.PendingConsolidation.Code.unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh Prysm.PendingConsolidation.Code.unmarshalSSZ k) :
    ∀
    (base a : BitVec 64) (ha : base + (112 : Int64).toBitVec = a) (bs : List UInt8) (hbs : bs.length = 8)
    (F : DataMem → Prop)
    (final : MachineState → Prop) (s : MachineData)
    (hb : s.regs.get64 Reg64.rsp = base) (hm : (Eq (bs.At a) ⋆ F) s.dmem)
    (hk' : Eventually (step1 Host.exe) final ⟨Codec.setRegister s Reg64.rdi (BitVec.ofInt 64 (Int.ofBytes bs)), Host.addrOf (k + 51)⟩),
    Eventually (step1 Host.exe) final ⟨s, Host.addrOf (k + 50)⟩ := by
  have hq := Codec.window_infix_at hk 50 1
  have he : Codec.eraseNop ((Prysm.PendingConsolidation.Code.unmarshalSSZ.drop 50).take 1) = [Codec.instrLoad Reg64.rdi Reg64.rsp 112] := by rfl
  have hend : k + 50 + ((Prysm.PendingConsolidation.Code.unmarshalSSZ.drop 50).take 1).length = k + 51 := by rfl
  with_reducible exact Codec.step_load_bytes Reg64.rdi Reg64.rsp 112 _ (k + 50) (k + 51) hq he hend
theorem _root_.Prysm.PendingConsolidation.Decode.example_step_s50_kind : ∀ (h : Host), type_of% (@Prysm.PendingConsolidation.Decode.example_step_s50 h) = @Codec.stepLoadBytesKind h Prysm.PendingConsolidation.Code.unmarshalSSZ Reg64.rdi Reg64.rsp 112 50 51 := by
  intro h; with_reducible rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Directive 51 `add $-0x8,%rdi`: stepAddKind. -/
theorem _root_.Prysm.PendingConsolidation.Decode.example_step_s51 (k : Nat) (hk : Prysm.PendingConsolidation.Code.unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh Prysm.PendingConsolidation.Code.unmarshalSSZ k) :
    ∀
    (final : MachineState → Prop) (s : MachineData)
    (hk' : ∀ fl : StatusFlags, Eventually (step1 Host.exe) final
      ⟨{ regs := s.regs.set64 Reg64.rdi (s.regs.get64 Reg64.rdi + ((-8) : Int64).toBitVec), zmms := s.zmms, status := fl, dmem := s.dmem },
        Host.addrOf (k + 52)⟩),
    Eventually (step1 Host.exe) final ⟨s, Host.addrOf (k + 51)⟩ := by
  have hq := Codec.window_infix_at hk 51 1
  have he : Codec.eraseNop ((Prysm.PendingConsolidation.Code.unmarshalSSZ.drop 51).take 1) = [Codec.instrAddImmediate Reg64.rdi (-8)] := by rfl
  have hend : k + 51 + ((Prysm.PendingConsolidation.Code.unmarshalSSZ.drop 51).take 1).length = k + 52 := by rfl
  with_reducible exact Codec.step_add_immediate Reg64.rdi (-8) _ (k + 51) (k + 52) hq he hend
theorem _root_.Prysm.PendingConsolidation.Decode.example_step_s51_kind : ∀ (h : Host), type_of% (@Prysm.PendingConsolidation.Decode.example_step_s51 h) = @Codec.stepAddKind h Prysm.PendingConsolidation.Code.unmarshalSSZ Reg64.rdi (-8) 51 52 := by
  intro h; with_reducible rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Directive 52 `mov 0x58(%rsp),%rax`: stepLoadValueKind. -/
theorem _root_.Prysm.PendingConsolidation.Decode.example_step_s52 (k : Nat) (hk : Prysm.PendingConsolidation.Code.unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh Prysm.PendingConsolidation.Code.unmarshalSSZ k) :
    ∀
    (base a v : BitVec 64) (ha : base + (88 : Int64).toBitVec = a)
    (F : DataMem → Prop)
    (final : MachineState → Prop) (s : MachineData)
    (hb : s.regs.get64 Reg64.rsp = base) (hm : (Eq ((Int.toBytes 8 v.toInt).At a) ⋆ F) s.dmem)
    (hk' : Eventually (step1 Host.exe) final ⟨Codec.setRegister s Reg64.rax v, Host.addrOf (k + 53)⟩),
    Eventually (step1 Host.exe) final ⟨s, Host.addrOf (k + 52)⟩ := by
  have hq := Codec.window_infix_at hk 52 1
  have he : Codec.eraseNop ((Prysm.PendingConsolidation.Code.unmarshalSSZ.drop 52).take 1) = [Codec.instrLoad Reg64.rax Reg64.rsp 88] := by rfl
  have hend : k + 52 + ((Prysm.PendingConsolidation.Code.unmarshalSSZ.drop 52).take 1).length = k + 53 := by rfl
  with_reducible exact Codec.step_load_value Reg64.rax Reg64.rsp 88 _ (k + 52) (k + 53) hq he hend
theorem _root_.Prysm.PendingConsolidation.Decode.example_step_s52_kind : ∀ (h : Host), type_of% (@Prysm.PendingConsolidation.Decode.example_step_s52 h) = @Codec.stepLoadValueKind h Prysm.PendingConsolidation.Code.unmarshalSSZ Reg64.rax Reg64.rsp 88 52 53 := by
  intro h; with_reducible rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Directive 53 `add $0x10,%rax`: stepAddKind. -/
theorem _root_.Prysm.PendingConsolidation.Decode.example_step_s53 (k : Nat) (hk : Prysm.PendingConsolidation.Code.unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh Prysm.PendingConsolidation.Code.unmarshalSSZ k) :
    ∀
    (final : MachineState → Prop) (s : MachineData)
    (hk' : ∀ fl : StatusFlags, Eventually (step1 Host.exe) final
      ⟨{ regs := s.regs.set64 Reg64.rax (s.regs.get64 Reg64.rax + (16 : Int64).toBitVec), zmms := s.zmms, status := fl, dmem := s.dmem },
        Host.addrOf (k + 54)⟩),
    Eventually (step1 Host.exe) final ⟨s, Host.addrOf (k + 53)⟩ := by
  have hq := Codec.window_infix_at hk 53 1
  have he : Codec.eraseNop ((Prysm.PendingConsolidation.Code.unmarshalSSZ.drop 53).take 1) = [Codec.instrAddImmediate Reg64.rax 16] := by rfl
  have hend : k + 53 + ((Prysm.PendingConsolidation.Code.unmarshalSSZ.drop 53).take 1).length = k + 54 := by rfl
  with_reducible exact Codec.step_add_immediate Reg64.rax 16 _ (k + 53) (k + 54) hq he hend
theorem _root_.Prysm.PendingConsolidation.Decode.example_step_s53_kind : ∀ (h : Host), type_of% (@Prysm.PendingConsolidation.Decode.example_step_s53 h) = @Codec.stepAddKind h Prysm.PendingConsolidation.Code.unmarshalSSZ Reg64.rax 16 53 54 := by
  intro h; with_reducible rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Directive 54 `mov $0x8,%ecx`: stepMoveImmediateKind. -/
theorem _root_.Prysm.PendingConsolidation.Decode.example_step_s54 (k : Nat) (hk : Prysm.PendingConsolidation.Code.unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh Prysm.PendingConsolidation.Code.unmarshalSSZ k) :
    ∀
    (final : MachineState → Prop) (s : MachineData)
    (hk' : Eventually (step1 Host.exe) final ⟨Codec.setRegister s Reg64.rcx (BitVec.zeroExtend 64 (BitVec.truncate 32 (8 : Int64).toBitVec)), Host.addrOf (k + 55)⟩),
    Eventually (step1 Host.exe) final ⟨s, Host.addrOf (k + 54)⟩ := by
  have hq := Codec.window_infix_at hk 54 1
  have he : Codec.eraseNop ((Prysm.PendingConsolidation.Code.unmarshalSSZ.drop 54).take 1) = [Codec.instrMoveImmediate32 Reg64.rcx 8] := by rfl
  have hend : k + 54 + ((Prysm.PendingConsolidation.Code.unmarshalSSZ.drop 54).take 1).length = k + 55 := by rfl
  with_reducible exact Codec.step_move_immediate Reg64.rcx 8 _ (k + 54) (k + 55) hq he hend
theorem _root_.Prysm.PendingConsolidation.Decode.example_step_s54_kind : ∀ (h : Host), type_of% (@Prysm.PendingConsolidation.Decode.example_step_s54 h) = @Codec.stepMoveImmediateKind h Prysm.PendingConsolidation.Code.unmarshalSSZ Reg64.rcx 8 54 55 := by
  intro h; with_reducible rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- `TargetIndex`: call block over the window 55–58 (`callq; nop; test; je`), `callq` at 55, continuation label at 85. -/
theorem _root_.Prysm.PendingConsolidation.Decode.example_step_TargetIndex_call (k : Nat) (hk : Prysm.PendingConsolidation.Code.unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh Prysm.PendingConsolidation.Code.unmarshalSSZ k) :
    ∀ (hC : U64CalleeAccept "github.com_OffchainLabs_prysm_v7_consensus_types_primitives.ValidatorIndex.UnmarshalSSZ")
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
  have hq := Codec.window_infix_at hk 55 4
  have he : Codec.eraseNop ((Prysm.PendingConsolidation.Code.unmarshalSSZ.drop 55).take 4) = Codec.callDec "github.com_OffchainLabs_prysm_v7_consensus_types_primitives.ValidatorIndex.UnmarshalSSZ" "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingConsolidation.UnmarshalSSZ_14d" := by rfl
  have hjc : k + 55 + Codec.nonNopIndex ((Prysm.PendingConsolidation.Code.unmarshalSSZ.drop 55).take 4) 0 = k + 55 := by rfl
  have hB := Codec.infix_sub (q := Codec.callDecContinuationLabel "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingConsolidation.UnmarshalSSZ_14d") 85 hk
    (by simp only [Prysm.PendingConsolidation.Code.unmarshalSSZ, Codec.callDecContinuationLabel, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero])
  have hl := Machine.label_at' hk hf (j := 85)
    (by simp only [Prysm.PendingConsolidation.Code.unmarshalSSZ, List.getElem?_cons_succ, List.getElem?_cons_zero]; rfl)
    (by simp only [Prysm.PendingConsolidation.Code.unmarshalSSZ, List.take_succ_cons, List.take_zero, List.contains_cons, List.contains_nil]; decide)
  with_reducible exact Codec.calldec_seg_window _ _ _ (k + 55) (k + 55) (k + 85) hq he hjc hB hl
theorem _root_.Prysm.PendingConsolidation.Decode.example_step_TargetIndex_call_kind : ∀ (h : Host), type_of% (@Prysm.PendingConsolidation.Decode.example_step_TargetIndex_call h) = @Codec.callDecSegKindWindow h Prysm.PendingConsolidation.Code.unmarshalSSZ "github.com_OffchainLabs_prysm_v7_consensus_types_primitives.ValidatorIndex.UnmarshalSSZ" "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingConsolidation.UnmarshalSSZ_14d" 55 55 85 := by
  intro h; with_reducible rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- `TargetIndex` (callee decoder field, Go offset 16, SSZ offset 8): the WHOLE call field 48–85, composed from the
step theorems of its set-up and the call-block theorem (worked example of the `decoder --steps` emission recipe). The entry
conditions of the call block (rax = `rcv + 16`, rbx = `bf + 8`, rcx = 8) are closed by `rfl` on the state
that the steps computed. -/
theorem _root_.Prysm.PendingConsolidation.Decode.example_step_TargetIndex_field (k : Nat) (hk : Prysm.PendingConsolidation.Code.unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh Prysm.PendingConsolidation.Code.unmarshalSSZ k) :
    ∀ (hC : U64CalleeAccept "github.com_OffchainLabs_prysm_v7_consensus_types_primitives.ValidatorIndex.UnmarshalSSZ")
    (sp rcv bf aRet aFp aS2 aB aD aR : BitVec 64)
    (hRet : sp - 8 = aRet) (hFp : sp - 16 = aFp) (hS2 : sp + 8 = aS2)
    (hB : sp + (96 : Int64).toBitVec = aB) (hD : sp + (112 : Int64).toBitVec = aD) (hR : sp + (88 : Int64).toBitVec = aR)
    (rbp0 r140 guard : UInt64) (e8 rslot fp s2 c0 vD : List UInt8)
    (he8 : e8.length = 8) (hrs : rslot.length = 8) (hfp : fp.length = 8) (hs2 : s2.length = 8)
    (hc0 : c0.length = 8) (hvD : vD.length = 8) (hguard : guard.toNat < aRet.toNat)
    (F : DataMem → Prop)
    (s : MachineData) (hrsp : s.regs.rsp = { toBitVec := sp }) (hrbp : s.regs.rbp = rbp0)
    (hr14 : s.regs.r14 = r140)
    (h_mem : s.dmem =⋆ Eq (rslot.At aRet) ⋆ Eq (fp.At aFp) ⋆ Eq (s2.At aS2)
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (r140.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 bf.toInt).At aB) ⋆ Eq (vD.At aD) ⋆ Eq ((Int.toBytes 8 rcv.toInt).At aR)
      ⋆ Eq (e8.At (bf + 8)) ⋆ Eq (c0.At (rcv + 16)) ⋆ F),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 85 + 1) ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0
        ∧ st.data.regs.rsp = { toBitVec := sp } ∧ st.data.regs.rbp = rbp0 ∧ st.data.regs.r14 = r140 ∧
        (Eq ((Int.toBytes 8 (Host.addrOf (k + 55 + 1)).toBitVec.toInt).At aRet)
          ⋆ Eq ((Int.toBytes 8 rbp0.toBitVec.toInt).At aFp) ⋆ Eq ((Int.toBytes 8 (bf + 8).toInt).At aS2)
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (r140.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 bf.toInt).At aB) ⋆ Eq (vD.At aD) ⋆ Eq ((Int.toBytes 8 rcv.toInt).At aR)
          ⋆ Eq (e8.At (bf + 8)) ⋆ Eq (e8.At (rcv + 16)) ⋆ F) st.data.dmem)
      ⟨s, Host.addrOf (k + 48)⟩ := by
  intro hC sp rcv bf aRet aFp aS2 aB aD aR hRet hFp hS2 hB hD hR rbp0 r140 guard e8 rslot fp s2 c0 vD he8 hrs hfp hs2 hc0 hvD
    hguard F s hrsp hrbp hr14 h_mem
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at hrsp hrbp hr14 h_mem ⊢
  subst rsp rbp r14
  apply Prysm.PendingConsolidation.Decode.example_step_s48 k hk hf sp aB bf hB _ _ _ (by rfl) (by ecancel)
  normalize_registers
  apply Prysm.PendingConsolidation.Decode.example_step_s49 k hk hf
  intro fl1; normalize_registers
  apply Prysm.PendingConsolidation.Decode.example_step_s50 k hk hf sp aD hD vD hvD _ _ _ (by rfl) (by ecancel)
  normalize_registers
  apply Prysm.PendingConsolidation.Decode.example_step_s51 k hk hf
  intro fl2; normalize_registers
  apply Prysm.PendingConsolidation.Decode.example_step_s52 k hk hf sp aR rcv hR _ _ _ (by rfl) (by ecancel)
  normalize_registers
  apply Prysm.PendingConsolidation.Decode.example_step_s53 k hk hf
  intro fl3; normalize_registers
  apply Prysm.PendingConsolidation.Decode.example_step_s54 k hk hf
  normalize_registers
  refine eventually_trans _ _ _ _ (Prysm.PendingConsolidation.Decode.example_step_TargetIndex_call k hk hf hC sp (rcv + 16) (bf + 8) aRet aFp aS2 hRet hFp hS2 rbp0 r140 guard e8 rslot
    fp s2 c0 he8 hrs hfp hs2 hc0 hguard _ _ (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by first | rfl | decide)
    (by ecancel)) ?_
  rintro ⟨d, pc⟩ ⟨hpc, hrax', hrbx', hrsp', hrbp', hr14', Hm⟩
  dsimp only at hpc hrax' hrbx' hrsp' hrbp' hr14' Hm
  apply Eventually.done
  refine ⟨hpc, hrax', hrbx', hrsp', hrbp', hr14', ?_⟩
  dsimp only
  ecancel

end Prysm.PendingConsolidation
