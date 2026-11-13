import Codec.Kind.WindowSteps
import Codec.Kind.FixedBytesDecodeWindow
import Codec.CalleeDecodeWindow
import Prysm.SyncCommitteeMessage.Code
import Prysm.Deposit_Data.Code
import Prysm.BeaconBlockHeader.Code
import Prysm.Checkpoint.Code

/-!
# Example instances of the window and step mechanisms on the development sites: the `BeaconBlockHeader` part

It holds the steps and the call block of `BeaconBlockHeader.ProposerIndex` (`decoder --call-segments` reload set-up form with pad). The declarations of the other types of this group are in `Prysm/SyncCommitteeMessage/DecodeStepExamples.lean`.
-/

open Machine Runtime Prysm.Checkpoint.Code
variable [Host]

open Codec
namespace Prysm.BeaconBlockHeader

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Directive 47 `mov 0x78(%rsp),%rbx`: stepLoadValueKind. -/
theorem _root_.Prysm.BeaconBlockHeader.Decode.example_step_directive_47 (k : Nat) (hk : Prysm.BeaconBlockHeader.Code.unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh Prysm.BeaconBlockHeader.Code.unmarshalSSZ k) :
    ∀
    (base a v : BitVec 64) (ha : base + (120 : Int64).toBitVec = a)
    (F : DataMem → Prop)
    (final : MachineState → Prop) (s : MachineData)
    (hb : s.regs.get64 Reg64.rsp = base) (hm : (Eq ((Int.toBytes 8 v.toInt).At a) ⋆ F) s.dmem)
    (hk' : Eventually (step1 Host.exe) final ⟨Codec.setRegister s Reg64.rbx v, Host.addrOf (k + 48)⟩),
    Eventually (step1 Host.exe) final ⟨s, Host.addrOf (k + 47)⟩ := by
  have hq := Codec.window_infix_at hk 47 1
  have he : Codec.eraseNop ((Prysm.BeaconBlockHeader.Code.unmarshalSSZ.drop 47).take 1) = [Codec.instrLoad Reg64.rbx Reg64.rsp 120] := by rfl
  have hend : k + 47 + ((Prysm.BeaconBlockHeader.Code.unmarshalSSZ.drop 47).take 1).length = k + 48 := by rfl
  with_reducible exact Codec.step_load_value Reg64.rbx Reg64.rsp 120 _ (k + 47) (k + 48) hq he hend
theorem _root_.Prysm.BeaconBlockHeader.Decode.example_step_directive_47_kind : ∀ (h : Host), type_of% (@Prysm.BeaconBlockHeader.Decode.example_step_directive_47 h) = @Codec.stepLoadValueKind h Prysm.BeaconBlockHeader.Code.unmarshalSSZ Reg64.rbx Reg64.rsp 120 47 48 := by
  intro h; with_reducible rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Directive 48 `add $0x8,%rbx`: stepAddKind. -/
theorem _root_.Prysm.BeaconBlockHeader.Decode.example_step_directive_48 (k : Nat) (hk : Prysm.BeaconBlockHeader.Code.unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh Prysm.BeaconBlockHeader.Code.unmarshalSSZ k) :
    ∀
    (final : MachineState → Prop) (s : MachineData)
    (hk' : ∀ fl : StatusFlags, Eventually (step1 Host.exe) final
      ⟨{ regs := s.regs.set64 Reg64.rbx (s.regs.get64 Reg64.rbx + (8 : Int64).toBitVec), zmms := s.zmms, status := fl, dmem := s.dmem },
        Host.addrOf (k + 49)⟩),
    Eventually (step1 Host.exe) final ⟨s, Host.addrOf (k + 48)⟩ := by
  have hq := Codec.window_infix_at hk 48 1
  have he : Codec.eraseNop ((Prysm.BeaconBlockHeader.Code.unmarshalSSZ.drop 48).take 1) = [Codec.instrAddImmediate Reg64.rbx 8] := by rfl
  have hend : k + 48 + ((Prysm.BeaconBlockHeader.Code.unmarshalSSZ.drop 48).take 1).length = k + 49 := by rfl
  with_reducible exact Codec.step_add_immediate Reg64.rbx 8 _ (k + 48) (k + 49) hq he hend
theorem _root_.Prysm.BeaconBlockHeader.Decode.example_step_directive_48_kind : ∀ (h : Host), type_of% (@Prysm.BeaconBlockHeader.Decode.example_step_directive_48 h) = @Codec.stepAddKind h Prysm.BeaconBlockHeader.Code.unmarshalSSZ Reg64.rbx 8 48 49 := by
  intro h; with_reducible rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Directive 49 `mov 0x88(%rsp),%rdi`: stepLoadBytesKind. -/
theorem _root_.Prysm.BeaconBlockHeader.Decode.example_step_directive_49 (k : Nat) (hk : Prysm.BeaconBlockHeader.Code.unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh Prysm.BeaconBlockHeader.Code.unmarshalSSZ k) :
    ∀
    (base a : BitVec 64) (ha : base + (136 : Int64).toBitVec = a) (bs : List UInt8) (hbs : bs.length = 8)
    (F : DataMem → Prop)
    (final : MachineState → Prop) (s : MachineData)
    (hb : s.regs.get64 Reg64.rsp = base) (hm : (Eq (bs.At a) ⋆ F) s.dmem)
    (hk' : Eventually (step1 Host.exe) final ⟨Codec.setRegister s Reg64.rdi (BitVec.ofInt 64 (Int.ofBytes bs)), Host.addrOf (k + 50)⟩),
    Eventually (step1 Host.exe) final ⟨s, Host.addrOf (k + 49)⟩ := by
  have hq := Codec.window_infix_at hk 49 1
  have he : Codec.eraseNop ((Prysm.BeaconBlockHeader.Code.unmarshalSSZ.drop 49).take 1) = [Codec.instrLoad Reg64.rdi Reg64.rsp 136] := by rfl
  have hend : k + 49 + ((Prysm.BeaconBlockHeader.Code.unmarshalSSZ.drop 49).take 1).length = k + 50 := by rfl
  with_reducible exact Codec.step_load_bytes Reg64.rdi Reg64.rsp 136 _ (k + 49) (k + 50) hq he hend
theorem _root_.Prysm.BeaconBlockHeader.Decode.example_step_directive_49_kind : ∀ (h : Host), type_of% (@Prysm.BeaconBlockHeader.Decode.example_step_directive_49 h) = @Codec.stepLoadBytesKind h Prysm.BeaconBlockHeader.Code.unmarshalSSZ Reg64.rdi Reg64.rsp 136 49 50 := by
  intro h; with_reducible rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Directive 50 `add $-0x8,%rdi`: stepAddKind. -/
theorem _root_.Prysm.BeaconBlockHeader.Decode.example_step_directive_50 (k : Nat) (hk : Prysm.BeaconBlockHeader.Code.unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh Prysm.BeaconBlockHeader.Code.unmarshalSSZ k) :
    ∀
    (final : MachineState → Prop) (s : MachineData)
    (hk' : ∀ fl : StatusFlags, Eventually (step1 Host.exe) final
      ⟨{ regs := s.regs.set64 Reg64.rdi (s.regs.get64 Reg64.rdi + ((-8) : Int64).toBitVec), zmms := s.zmms, status := fl, dmem := s.dmem },
        Host.addrOf (k + 51)⟩),
    Eventually (step1 Host.exe) final ⟨s, Host.addrOf (k + 50)⟩ := by
  have hq := Codec.window_infix_at hk 50 1
  have he : Codec.eraseNop ((Prysm.BeaconBlockHeader.Code.unmarshalSSZ.drop 50).take 1) = [Codec.instrAddImmediate Reg64.rdi (-8)] := by rfl
  have hend : k + 50 + ((Prysm.BeaconBlockHeader.Code.unmarshalSSZ.drop 50).take 1).length = k + 51 := by rfl
  with_reducible exact Codec.step_add_immediate Reg64.rdi (-8) _ (k + 50) (k + 51) hq he hend
theorem _root_.Prysm.BeaconBlockHeader.Decode.example_step_directive_50_kind : ∀ (h : Host), type_of% (@Prysm.BeaconBlockHeader.Decode.example_step_directive_50 h) = @Codec.stepAddKind h Prysm.BeaconBlockHeader.Code.unmarshalSSZ Reg64.rdi (-8) 50 51 := by
  intro h; with_reducible rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Directive 51 `mov 0x70(%rsp),%rax`: stepLoadValueKind. -/
theorem _root_.Prysm.BeaconBlockHeader.Decode.example_step_directive_51 (k : Nat) (hk : Prysm.BeaconBlockHeader.Code.unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh Prysm.BeaconBlockHeader.Code.unmarshalSSZ k) :
    ∀
    (base a v : BitVec 64) (ha : base + (112 : Int64).toBitVec = a)
    (F : DataMem → Prop)
    (final : MachineState → Prop) (s : MachineData)
    (hb : s.regs.get64 Reg64.rsp = base) (hm : (Eq ((Int.toBytes 8 v.toInt).At a) ⋆ F) s.dmem)
    (hk' : Eventually (step1 Host.exe) final ⟨Codec.setRegister s Reg64.rax v, Host.addrOf (k + 52)⟩),
    Eventually (step1 Host.exe) final ⟨s, Host.addrOf (k + 51)⟩ := by
  have hq := Codec.window_infix_at hk 51 1
  have he : Codec.eraseNop ((Prysm.BeaconBlockHeader.Code.unmarshalSSZ.drop 51).take 1) = [Codec.instrLoad Reg64.rax Reg64.rsp 112] := by rfl
  have hend : k + 51 + ((Prysm.BeaconBlockHeader.Code.unmarshalSSZ.drop 51).take 1).length = k + 52 := by rfl
  with_reducible exact Codec.step_load_value Reg64.rax Reg64.rsp 112 _ (k + 51) (k + 52) hq he hend
theorem _root_.Prysm.BeaconBlockHeader.Decode.example_step_directive_51_kind : ∀ (h : Host), type_of% (@Prysm.BeaconBlockHeader.Decode.example_step_directive_51 h) = @Codec.stepLoadValueKind h Prysm.BeaconBlockHeader.Code.unmarshalSSZ Reg64.rax Reg64.rsp 112 51 52 := by
  intro h; with_reducible rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Directive 52 `add $0x10,%rax`: stepAddKind. -/
theorem _root_.Prysm.BeaconBlockHeader.Decode.example_step_directive_52 (k : Nat) (hk : Prysm.BeaconBlockHeader.Code.unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh Prysm.BeaconBlockHeader.Code.unmarshalSSZ k) :
    ∀
    (final : MachineState → Prop) (s : MachineData)
    (hk' : ∀ fl : StatusFlags, Eventually (step1 Host.exe) final
      ⟨{ regs := s.regs.set64 Reg64.rax (s.regs.get64 Reg64.rax + (16 : Int64).toBitVec), zmms := s.zmms, status := fl, dmem := s.dmem },
        Host.addrOf (k + 53)⟩),
    Eventually (step1 Host.exe) final ⟨s, Host.addrOf (k + 52)⟩ := by
  have hq := Codec.window_infix_at hk 52 1
  have he : Codec.eraseNop ((Prysm.BeaconBlockHeader.Code.unmarshalSSZ.drop 52).take 1) = [Codec.instrAddImmediate Reg64.rax 16] := by rfl
  have hend : k + 52 + ((Prysm.BeaconBlockHeader.Code.unmarshalSSZ.drop 52).take 1).length = k + 53 := by rfl
  with_reducible exact Codec.step_add_immediate Reg64.rax 16 _ (k + 52) (k + 53) hq he hend
theorem _root_.Prysm.BeaconBlockHeader.Decode.example_step_directive_52_kind : ∀ (h : Host), type_of% (@Prysm.BeaconBlockHeader.Decode.example_step_directive_52 h) = @Codec.stepAddKind h Prysm.BeaconBlockHeader.Code.unmarshalSSZ Reg64.rax 16 52 53 := by
  intro h; with_reducible rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Directive 53 `mov $0x8,%ecx`: stepMoveImmediateKind. -/
theorem _root_.Prysm.BeaconBlockHeader.Decode.example_step_directive_53 (k : Nat) (hk : Prysm.BeaconBlockHeader.Code.unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh Prysm.BeaconBlockHeader.Code.unmarshalSSZ k) :
    ∀
    (final : MachineState → Prop) (s : MachineData)
    (hk' : Eventually (step1 Host.exe) final ⟨Codec.setRegister s Reg64.rcx (BitVec.zeroExtend 64 (BitVec.truncate 32 (8 : Int64).toBitVec)), Host.addrOf (k + 54)⟩),
    Eventually (step1 Host.exe) final ⟨s, Host.addrOf (k + 53)⟩ := by
  have hq := Codec.window_infix_at hk 53 1
  have he : Codec.eraseNop ((Prysm.BeaconBlockHeader.Code.unmarshalSSZ.drop 53).take 1) = [Codec.instrMoveImmediate32 Reg64.rcx 8] := by rfl
  have hend : k + 53 + ((Prysm.BeaconBlockHeader.Code.unmarshalSSZ.drop 53).take 1).length = k + 54 := by rfl
  with_reducible exact Codec.step_move_immediate Reg64.rcx 8 _ (k + 53) (k + 54) hq he hend
theorem _root_.Prysm.BeaconBlockHeader.Decode.example_step_directive_53_kind : ∀ (h : Host), type_of% (@Prysm.BeaconBlockHeader.Decode.example_step_directive_53 h) = @Codec.stepMoveImmediateKind h Prysm.BeaconBlockHeader.Code.unmarshalSSZ Reg64.rcx 8 53 54 := by
  intro h; with_reducible rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- `ProposerIndex`: call block over the window 54–57 (`nop; callq; test; je`), `callq` at 55, continuation label at 85. -/
theorem _root_.Prysm.BeaconBlockHeader.Decode.example_step_ProposerIndex_call (k : Nat) (hk : Prysm.BeaconBlockHeader.Code.unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh Prysm.BeaconBlockHeader.Code.unmarshalSSZ k) :
    ∀ (hC : Uint64CalleeAccept "github.com_OffchainLabs_prysm_v7_consensus_types_primitives.ValidatorIndex.UnmarshalSSZ")
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
      ⟨s, Host.addrOf (k + 54)⟩ := by
  have hq := Codec.window_infix_at hk 54 4
  have he : Codec.eraseNop ((Prysm.BeaconBlockHeader.Code.unmarshalSSZ.drop 54).take 4) = Codec.callDecode "github.com_OffchainLabs_prysm_v7_consensus_types_primitives.ValidatorIndex.UnmarshalSSZ" "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockHeader.UnmarshalSSZ_154" := by rfl
  have hjc : k + 54 + Codec.nonNopIndex ((Prysm.BeaconBlockHeader.Code.unmarshalSSZ.drop 54).take 4) 0 = k + 55 := by rfl
  have hB := Codec.infix_sub (q := Codec.callDecodeContinuationLabel "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockHeader.UnmarshalSSZ_154") 85 hk
    (by simp only [Prysm.BeaconBlockHeader.Code.unmarshalSSZ, Codec.callDecodeContinuationLabel, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero])
  have hl := Machine.label_at' hk hf (j := 85)
    (by simp only [Prysm.BeaconBlockHeader.Code.unmarshalSSZ, List.getElem?_cons_succ, List.getElem?_cons_zero]; rfl)
    (by simp only [Prysm.BeaconBlockHeader.Code.unmarshalSSZ, List.take_succ_cons, List.take_zero, List.contains_cons, List.contains_nil]; decide)
  with_reducible exact Codec.call_decode_segment_window _ _ _ (k + 54) (k + 55) (k + 85) hq he hjc hB hl
theorem _root_.Prysm.BeaconBlockHeader.Decode.example_step_ProposerIndex_call_kind : ∀ (h : Host), type_of% (@Prysm.BeaconBlockHeader.Decode.example_step_ProposerIndex_call h) = @Codec.callDecodeSegmentKindWindow h Prysm.BeaconBlockHeader.Code.unmarshalSSZ "github.com_OffchainLabs_prysm_v7_consensus_types_primitives.ValidatorIndex.UnmarshalSSZ" "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockHeader.UnmarshalSSZ_154" 54 55 85 := by
  intro h; with_reducible rfl

end Prysm.BeaconBlockHeader
