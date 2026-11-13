import Codec.Kind.WindowSteps
import Codec.Kind.FixedBytesDecodeWindow
import Codec.CalleeDecodeWindow
import Prysm.SyncCommitteeMessage.Code
import Prysm.Deposit_Data.Code
import Prysm.BeaconBlockHeader.Code
import Prysm.Checkpoint.Code

/-!
# Example instances of the window and step mechanisms on the development sites: the `PendingPartialWithdrawal` part

It holds the steps and the call block of `PendingPartialWithdrawal.WithdrawableEpoch` (`decoder --call-segments` `lea` set-up form, interleaved uint64 read). The declarations of the other types of this group are in `Prysm/SyncCommitteeMessage/DecodeStepExamples.lean`.
-/

open Machine Runtime Prysm.Checkpoint.Code
variable [Host]

open Codec
namespace Prysm.PendingPartialWithdrawal

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Directive 48 `mov 0x60(%rsp),%rbx`: stepLdvKind. -/
theorem _root_.Prysm.PendingPartialWithdrawal.Decode.example_step_s48 (k : Nat) (hk : Prysm.PendingPartialWithdrawal.Code.unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh Prysm.PendingPartialWithdrawal.Code.unmarshalSSZ k) :
    ∀
    (base a v : BitVec 64) (ha : base + (96 : Int64).toBitVec = a)
    (F : DataMem → Prop)
    (final : MachineState → Prop) (s : MachineData)
    (hb : s.regs.get64 Reg64.rsp = base) (hm : (Eq ((Int.toBytes 8 v.toInt).At a) ⋆ F) s.dmem)
    (hk' : Eventually (step1 Host.exe) final ⟨Codec.setR s Reg64.rbx v, Host.addrOf (k + 49)⟩),
    Eventually (step1 Host.exe) final ⟨s, Host.addrOf (k + 48)⟩ := by
  have hq := Codec.win hk 48 1
  have he : Codec.eraseNop ((Prysm.PendingPartialWithdrawal.Code.unmarshalSSZ.drop 48).take 1) = [Codec.iLd Reg64.rbx Reg64.rsp 96] := by rfl
  have hend : k + 48 + ((Prysm.PendingPartialWithdrawal.Code.unmarshalSSZ.drop 48).take 1).length = k + 49 := by rfl
  with_reducible exact Codec.kstep_ldv Reg64.rbx Reg64.rsp 96 _ (k + 48) (k + 49) hq he hend
theorem _root_.Prysm.PendingPartialWithdrawal.Decode.example_step_s48_kind : ∀ (h : Host), type_of% (@Prysm.PendingPartialWithdrawal.Decode.example_step_s48 h) = @Codec.stepLdvKind h Prysm.PendingPartialWithdrawal.Code.unmarshalSSZ Reg64.rbx Reg64.rsp 96 48 49 := by
  intro h; with_reducible rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Directive 49 `lea 0x10(%rbx),%rdx`: stepLeaKind. -/
theorem _root_.Prysm.PendingPartialWithdrawal.Decode.example_step_s49 (k : Nat) (hk : Prysm.PendingPartialWithdrawal.Code.unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh Prysm.PendingPartialWithdrawal.Code.unmarshalSSZ k) :
    ∀
    (final : MachineState → Prop) (s : MachineData)
    (hk' : Eventually (step1 Host.exe) final ⟨Codec.setR s Reg64.rdx (s.regs.get64 Reg64.rbx + (16 : Int64).toBitVec), Host.addrOf (k + 50)⟩),
    Eventually (step1 Host.exe) final ⟨s, Host.addrOf (k + 49)⟩ := by
  have hq := Codec.win hk 49 1
  have he : Codec.eraseNop ((Prysm.PendingPartialWithdrawal.Code.unmarshalSSZ.drop 49).take 1) = [Codec.iLea Reg64.rdx Reg64.rbx 16] := by rfl
  have hend : k + 49 + ((Prysm.PendingPartialWithdrawal.Code.unmarshalSSZ.drop 49).take 1).length = k + 50 := by rfl
  with_reducible exact Codec.kstep_lea Reg64.rdx Reg64.rbx 16 _ (k + 49) (k + 50) hq he hend
theorem _root_.Prysm.PendingPartialWithdrawal.Decode.example_step_s49_kind : ∀ (h : Host), type_of% (@Prysm.PendingPartialWithdrawal.Decode.example_step_s49 h) = @Codec.stepLeaKind h Prysm.PendingPartialWithdrawal.Code.unmarshalSSZ Reg64.rdx Reg64.rbx 16 49 50 := by
  intro h; with_reducible rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Directive 50 `mov 0x70(%rsp),%rdi`: stepLdbKind. -/
theorem _root_.Prysm.PendingPartialWithdrawal.Decode.example_step_s50 (k : Nat) (hk : Prysm.PendingPartialWithdrawal.Code.unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh Prysm.PendingPartialWithdrawal.Code.unmarshalSSZ k) :
    ∀
    (base a : BitVec 64) (ha : base + (112 : Int64).toBitVec = a) (bs : List UInt8) (hbs : bs.length = 8)
    (F : DataMem → Prop)
    (final : MachineState → Prop) (s : MachineData)
    (hb : s.regs.get64 Reg64.rsp = base) (hm : (Eq (bs.At a) ⋆ F) s.dmem)
    (hk' : Eventually (step1 Host.exe) final ⟨Codec.setR s Reg64.rdi (BitVec.ofInt 64 (Int.ofBytes bs)), Host.addrOf (k + 51)⟩),
    Eventually (step1 Host.exe) final ⟨s, Host.addrOf (k + 50)⟩ := by
  have hq := Codec.win hk 50 1
  have he : Codec.eraseNop ((Prysm.PendingPartialWithdrawal.Code.unmarshalSSZ.drop 50).take 1) = [Codec.iLd Reg64.rdi Reg64.rsp 112] := by rfl
  have hend : k + 50 + ((Prysm.PendingPartialWithdrawal.Code.unmarshalSSZ.drop 50).take 1).length = k + 51 := by rfl
  with_reducible exact Codec.kstep_ldb Reg64.rdi Reg64.rsp 112 _ (k + 50) (k + 51) hq he hend
theorem _root_.Prysm.PendingPartialWithdrawal.Decode.example_step_s50_kind : ∀ (h : Host), type_of% (@Prysm.PendingPartialWithdrawal.Decode.example_step_s50 h) = @Codec.stepLdbKind h Prysm.PendingPartialWithdrawal.Code.unmarshalSSZ Reg64.rdi Reg64.rsp 112 50 51 := by
  intro h; with_reducible rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Directive 51 `add $-0x10,%rdi`: stepAddKind. -/
theorem _root_.Prysm.PendingPartialWithdrawal.Decode.example_step_s51 (k : Nat) (hk : Prysm.PendingPartialWithdrawal.Code.unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh Prysm.PendingPartialWithdrawal.Code.unmarshalSSZ k) :
    ∀
    (final : MachineState → Prop) (s : MachineData)
    (hk' : ∀ fl : StatusFlags, Eventually (step1 Host.exe) final
      ⟨{ regs := s.regs.set64 Reg64.rdi (s.regs.get64 Reg64.rdi + ((-16) : Int64).toBitVec), zmms := s.zmms, status := fl, dmem := s.dmem },
        Host.addrOf (k + 52)⟩),
    Eventually (step1 Host.exe) final ⟨s, Host.addrOf (k + 51)⟩ := by
  have hq := Codec.win hk 51 1
  have he : Codec.eraseNop ((Prysm.PendingPartialWithdrawal.Code.unmarshalSSZ.drop 51).take 1) = [Codec.iAdd Reg64.rdi (-16)] := by rfl
  have hend : k + 51 + ((Prysm.PendingPartialWithdrawal.Code.unmarshalSSZ.drop 51).take 1).length = k + 52 := by rfl
  with_reducible exact Codec.kstep_add Reg64.rdi (-16) _ (k + 51) (k + 52) hq he hend
theorem _root_.Prysm.PendingPartialWithdrawal.Decode.example_step_s51_kind : ∀ (h : Host), type_of% (@Prysm.PendingPartialWithdrawal.Decode.example_step_s51 h) = @Codec.stepAddKind h Prysm.PendingPartialWithdrawal.Code.unmarshalSSZ Reg64.rdi (-16) 51 52 := by
  intro h; with_reducible rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Directive 52 `mov 0x58(%rsp),%rax`: stepLdvKind. -/
theorem _root_.Prysm.PendingPartialWithdrawal.Decode.example_step_s52 (k : Nat) (hk : Prysm.PendingPartialWithdrawal.Code.unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh Prysm.PendingPartialWithdrawal.Code.unmarshalSSZ k) :
    ∀
    (base a v : BitVec 64) (ha : base + (88 : Int64).toBitVec = a)
    (F : DataMem → Prop)
    (final : MachineState → Prop) (s : MachineData)
    (hb : s.regs.get64 Reg64.rsp = base) (hm : (Eq ((Int.toBytes 8 v.toInt).At a) ⋆ F) s.dmem)
    (hk' : Eventually (step1 Host.exe) final ⟨Codec.setR s Reg64.rax v, Host.addrOf (k + 53)⟩),
    Eventually (step1 Host.exe) final ⟨s, Host.addrOf (k + 52)⟩ := by
  have hq := Codec.win hk 52 1
  have he : Codec.eraseNop ((Prysm.PendingPartialWithdrawal.Code.unmarshalSSZ.drop 52).take 1) = [Codec.iLd Reg64.rax Reg64.rsp 88] := by rfl
  have hend : k + 52 + ((Prysm.PendingPartialWithdrawal.Code.unmarshalSSZ.drop 52).take 1).length = k + 53 := by rfl
  with_reducible exact Codec.kstep_ldv Reg64.rax Reg64.rsp 88 _ (k + 52) (k + 53) hq he hend
theorem _root_.Prysm.PendingPartialWithdrawal.Decode.example_step_s52_kind : ∀ (h : Host), type_of% (@Prysm.PendingPartialWithdrawal.Decode.example_step_s52 h) = @Codec.stepLdvKind h Prysm.PendingPartialWithdrawal.Code.unmarshalSSZ Reg64.rax Reg64.rsp 88 52 53 := by
  intro h; with_reducible rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Directive 53 `lea 0x18(%rax),%rsi`: stepLeaKind. -/
theorem _root_.Prysm.PendingPartialWithdrawal.Decode.example_step_s53 (k : Nat) (hk : Prysm.PendingPartialWithdrawal.Code.unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh Prysm.PendingPartialWithdrawal.Code.unmarshalSSZ k) :
    ∀
    (final : MachineState → Prop) (s : MachineData)
    (hk' : Eventually (step1 Host.exe) final ⟨Codec.setR s Reg64.rsi (s.regs.get64 Reg64.rax + (24 : Int64).toBitVec), Host.addrOf (k + 54)⟩),
    Eventually (step1 Host.exe) final ⟨s, Host.addrOf (k + 53)⟩ := by
  have hq := Codec.win hk 53 1
  have he : Codec.eraseNop ((Prysm.PendingPartialWithdrawal.Code.unmarshalSSZ.drop 53).take 1) = [Codec.iLea Reg64.rsi Reg64.rax 24] := by rfl
  have hend : k + 53 + ((Prysm.PendingPartialWithdrawal.Code.unmarshalSSZ.drop 53).take 1).length = k + 54 := by rfl
  with_reducible exact Codec.kstep_lea Reg64.rsi Reg64.rax 24 _ (k + 53) (k + 54) hq he hend
theorem _root_.Prysm.PendingPartialWithdrawal.Decode.example_step_s53_kind : ∀ (h : Host), type_of% (@Prysm.PendingPartialWithdrawal.Decode.example_step_s53 h) = @Codec.stepLeaKind h Prysm.PendingPartialWithdrawal.Code.unmarshalSSZ Reg64.rsi Reg64.rax 24 53 54 := by
  intro h; with_reducible rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Directive 54 `mov 0x8(%rbx),%r8`: stepLdbKind. -/
theorem _root_.Prysm.PendingPartialWithdrawal.Decode.example_step_s54 (k : Nat) (hk : Prysm.PendingPartialWithdrawal.Code.unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh Prysm.PendingPartialWithdrawal.Code.unmarshalSSZ k) :
    ∀
    (base a : BitVec 64) (ha : base + (8 : Int64).toBitVec = a) (bs : List UInt8) (hbs : bs.length = 8)
    (F : DataMem → Prop)
    (final : MachineState → Prop) (s : MachineData)
    (hb : s.regs.get64 Reg64.rbx = base) (hm : (Eq (bs.At a) ⋆ F) s.dmem)
    (hk' : Eventually (step1 Host.exe) final ⟨Codec.setR s Reg64.r8 (BitVec.ofInt 64 (Int.ofBytes bs)), Host.addrOf (k + 55)⟩),
    Eventually (step1 Host.exe) final ⟨s, Host.addrOf (k + 54)⟩ := by
  have hq := Codec.win hk 54 1
  have he : Codec.eraseNop ((Prysm.PendingPartialWithdrawal.Code.unmarshalSSZ.drop 54).take 1) = [Codec.iLd Reg64.r8 Reg64.rbx 8] := by rfl
  have hend : k + 54 + ((Prysm.PendingPartialWithdrawal.Code.unmarshalSSZ.drop 54).take 1).length = k + 55 := by rfl
  with_reducible exact Codec.kstep_ldb Reg64.r8 Reg64.rbx 8 _ (k + 54) (k + 55) hq he hend
theorem _root_.Prysm.PendingPartialWithdrawal.Decode.example_step_s54_kind : ∀ (h : Host), type_of% (@Prysm.PendingPartialWithdrawal.Decode.example_step_s54 h) = @Codec.stepLdbKind h Prysm.PendingPartialWithdrawal.Code.unmarshalSSZ Reg64.r8 Reg64.rbx 8 54 55 := by
  intro h; with_reducible rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Directive 55 `mov %r8,0x10(%rax)`: stepStKind. -/
theorem _root_.Prysm.PendingPartialWithdrawal.Decode.example_step_s55 (k : Nat) (hk : Prysm.PendingPartialWithdrawal.Code.unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh Prysm.PendingPartialWithdrawal.Code.unmarshalSSZ k) :
    ∀
    (base a : BitVec 64) (ha : base + (16 : Int64).toBitVec = a) (bs : List UInt8) (hbs : bs.length = 8)
    (F : DataMem → Prop)
    (final : MachineState → Prop) (s : MachineData)
    (hb : s.regs.get64 Reg64.rax = base) (hm : (Eq (bs.At a) ⋆ F) s.dmem)
    (hk' : ∀ m' : DataMem, (Eq ((Int.toBytes 8 (@BitVec.toInt 64 (s.regs.get64 Reg64.r8))).At a) ⋆ F) m' →
      Eventually (step1 Host.exe) final ⟨{ s with dmem := m' }, Host.addrOf (k + 56)⟩),
    Eventually (step1 Host.exe) final ⟨s, Host.addrOf (k + 55)⟩ := by
  have hq := Codec.win hk 55 1
  have he : Codec.eraseNop ((Prysm.PendingPartialWithdrawal.Code.unmarshalSSZ.drop 55).take 1) = [Codec.iSt Reg64.r8 Reg64.rax 16] := by rfl
  have hend : k + 55 + ((Prysm.PendingPartialWithdrawal.Code.unmarshalSSZ.drop 55).take 1).length = k + 56 := by rfl
  with_reducible exact Codec.kstep_st Reg64.r8 Reg64.rax 16 _ (k + 55) (k + 56) hq he hend
theorem _root_.Prysm.PendingPartialWithdrawal.Decode.example_step_s55_kind : ∀ (h : Host), type_of% (@Prysm.PendingPartialWithdrawal.Decode.example_step_s55 h) = @Codec.stepStKind h Prysm.PendingPartialWithdrawal.Code.unmarshalSSZ Reg64.r8 Reg64.rax 16 55 56 := by
  intro h; with_reducible rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Directive 56 `mov %rsi,%rax`: stepMovRRKind. -/
theorem _root_.Prysm.PendingPartialWithdrawal.Decode.example_step_s56 (k : Nat) (hk : Prysm.PendingPartialWithdrawal.Code.unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh Prysm.PendingPartialWithdrawal.Code.unmarshalSSZ k) :
    ∀
    (final : MachineState → Prop) (s : MachineData)
    (hk' : Eventually (step1 Host.exe) final ⟨Codec.setR s Reg64.rax (s.regs.get64 Reg64.rsi), Host.addrOf (k + 57)⟩),
    Eventually (step1 Host.exe) final ⟨s, Host.addrOf (k + 56)⟩ := by
  have hq := Codec.win hk 56 1
  have he : Codec.eraseNop ((Prysm.PendingPartialWithdrawal.Code.unmarshalSSZ.drop 56).take 1) = [Codec.iMovRR Reg64.rax Reg64.rsi] := by rfl
  have hend : k + 56 + ((Prysm.PendingPartialWithdrawal.Code.unmarshalSSZ.drop 56).take 1).length = k + 57 := by rfl
  with_reducible exact Codec.kstep_mov_rr Reg64.rax Reg64.rsi _ (k + 56) (k + 57) hq he hend
theorem _root_.Prysm.PendingPartialWithdrawal.Decode.example_step_s56_kind : ∀ (h : Host), type_of% (@Prysm.PendingPartialWithdrawal.Decode.example_step_s56 h) = @Codec.stepMovRRKind h Prysm.PendingPartialWithdrawal.Code.unmarshalSSZ Reg64.rax Reg64.rsi 56 57 := by
  intro h; with_reducible rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Directive 57 `mov %rdx,%rbx`: stepMovRRKind. -/
theorem _root_.Prysm.PendingPartialWithdrawal.Decode.example_step_s57 (k : Nat) (hk : Prysm.PendingPartialWithdrawal.Code.unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh Prysm.PendingPartialWithdrawal.Code.unmarshalSSZ k) :
    ∀
    (final : MachineState → Prop) (s : MachineData)
    (hk' : Eventually (step1 Host.exe) final ⟨Codec.setR s Reg64.rbx (s.regs.get64 Reg64.rdx), Host.addrOf (k + 58)⟩),
    Eventually (step1 Host.exe) final ⟨s, Host.addrOf (k + 57)⟩ := by
  have hq := Codec.win hk 57 1
  have he : Codec.eraseNop ((Prysm.PendingPartialWithdrawal.Code.unmarshalSSZ.drop 57).take 1) = [Codec.iMovRR Reg64.rbx Reg64.rdx] := by rfl
  have hend : k + 57 + ((Prysm.PendingPartialWithdrawal.Code.unmarshalSSZ.drop 57).take 1).length = k + 58 := by rfl
  with_reducible exact Codec.kstep_mov_rr Reg64.rbx Reg64.rdx _ (k + 57) (k + 58) hq he hend
theorem _root_.Prysm.PendingPartialWithdrawal.Decode.example_step_s57_kind : ∀ (h : Host), type_of% (@Prysm.PendingPartialWithdrawal.Decode.example_step_s57 h) = @Codec.stepMovRRKind h Prysm.PendingPartialWithdrawal.Code.unmarshalSSZ Reg64.rbx Reg64.rdx 57 58 := by
  intro h; with_reducible rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Directive 58 `mov $0x8,%ecx`: stepMovIKind. -/
theorem _root_.Prysm.PendingPartialWithdrawal.Decode.example_step_s58 (k : Nat) (hk : Prysm.PendingPartialWithdrawal.Code.unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh Prysm.PendingPartialWithdrawal.Code.unmarshalSSZ k) :
    ∀
    (final : MachineState → Prop) (s : MachineData)
    (hk' : Eventually (step1 Host.exe) final ⟨Codec.setR s Reg64.rcx (BitVec.zeroExtend 64 (BitVec.truncate 32 (8 : Int64).toBitVec)), Host.addrOf (k + 59)⟩),
    Eventually (step1 Host.exe) final ⟨s, Host.addrOf (k + 58)⟩ := by
  have hq := Codec.win hk 58 1
  have he : Codec.eraseNop ((Prysm.PendingPartialWithdrawal.Code.unmarshalSSZ.drop 58).take 1) = [Codec.iMovI Reg64.rcx 8] := by rfl
  have hend : k + 58 + ((Prysm.PendingPartialWithdrawal.Code.unmarshalSSZ.drop 58).take 1).length = k + 59 := by rfl
  with_reducible exact Codec.kstep_movi Reg64.rcx 8 _ (k + 58) (k + 59) hq he hend
theorem _root_.Prysm.PendingPartialWithdrawal.Decode.example_step_s58_kind : ∀ (h : Host), type_of% (@Prysm.PendingPartialWithdrawal.Decode.example_step_s58 h) = @Codec.stepMovIKind h Prysm.PendingPartialWithdrawal.Code.unmarshalSSZ Reg64.rcx 8 58 59 := by
  intro h; with_reducible rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- `WithdrawableEpoch`: call block over the window 59–61 (`callq; test; je`), `callq` at 59, continuation label at 88. -/
theorem _root_.Prysm.PendingPartialWithdrawal.Decode.example_step_WithdrawableEpoch_call (k : Nat) (hk : Prysm.PendingPartialWithdrawal.Code.unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh Prysm.PendingPartialWithdrawal.Code.unmarshalSSZ k) :
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
      (fun st => st.pc = Host.addrOf (k + 88 + 1) ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0
        ∧ st.data.regs.rsp = { toBitVec := sp } ∧ st.data.regs.rbp = rbp0 ∧ st.data.regs.r14 = r140 ∧
        (Eq ((Int.toBytes 8 (Host.addrOf (k + 59 + 1)).toBitVec.toInt).At aRet)
          ⋆ Eq ((Int.toBytes 8 rbp0.toBitVec.toInt).At aFp) ⋆ Eq ((Int.toBytes 8 src.toInt).At aS2)
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (r140.toBitVec + 16))
          ⋆ Eq (e8.At src) ⋆ Eq (e8.At dst) ⋆ F) st.data.dmem)
      ⟨s, Host.addrOf (k + 59)⟩ := by
  have hq := Codec.win hk 59 3
  have he : Codec.eraseNop ((Prysm.PendingPartialWithdrawal.Code.unmarshalSSZ.drop 59).take 3) = Codec.callDec "github.com_OffchainLabs_prysm_v7_consensus_types_primitives.Epoch.UnmarshalSSZ" "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingPartialWithdrawal.UnmarshalSSZ_159" := by rfl
  have hjc : k + 59 + Codec.nopPos ((Prysm.PendingPartialWithdrawal.Code.unmarshalSSZ.drop 59).take 3) 0 = k + 59 := by rfl
  have hB := Codec.infix_sub (q := Codec.callDecL "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingPartialWithdrawal.UnmarshalSSZ_159") 88 hk
    (by simp only [Prysm.PendingPartialWithdrawal.Code.unmarshalSSZ, Codec.callDecL, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero])
  have hl := Machine.label_at' hk hf (j := 88)
    (by simp only [Prysm.PendingPartialWithdrawal.Code.unmarshalSSZ, List.getElem?_cons_succ, List.getElem?_cons_zero]; rfl)
    (by simp only [Prysm.PendingPartialWithdrawal.Code.unmarshalSSZ, List.take_succ_cons, List.take_zero, List.contains_cons, List.contains_nil]; decide)
  with_reducible exact Codec.calldec_seg_w _ _ _ (k + 59) (k + 59) (k + 88) hq he hjc hB hl
theorem _root_.Prysm.PendingPartialWithdrawal.Decode.example_step_WithdrawableEpoch_call_kind : ∀ (h : Host), type_of% (@Prysm.PendingPartialWithdrawal.Decode.example_step_WithdrawableEpoch_call h) = @Codec.callDecSegKindWindow h Prysm.PendingPartialWithdrawal.Code.unmarshalSSZ "github.com_OffchainLabs_prysm_v7_consensus_types_primitives.Epoch.UnmarshalSSZ" "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingPartialWithdrawal.UnmarshalSSZ_159" 59 59 88 := by
  intro h; with_reducible rfl

end Prysm.PendingPartialWithdrawal
