import Codec.Kind.WindowSteps
import Codec.Kind.FixedBytesDecodeWindow
import Codec.CalleeDecodeWindow
import Prysm.SyncCommitteeMessage.Code
import Prysm.Deposit_Data.Code
import Prysm.BeaconBlockHeader.Code
import Prysm.Checkpoint.Code
import Prysm.BeaconBlockHeader.DecodeStepExamples
import Prysm.Checkpoint.DecodeStepExamples
import Prysm.Deposit_Data.DecodeStepExamples
import Prysm.PendingConsolidation.DecodeStepExamples
import Prysm.PendingPartialWithdrawal.DecodeStepExamples

/-!
# Example instances of the window and step mechanisms on the development sites

One theorem and one `_kind` line per emitted unit, in the shape a generated theorem is to have (the idiom of
`Prysm/PendingPartialWithdrawal/DecodeCallSegmentExamples.lean`). Examples for the generator; not generator output (the text was produced by a
scratch script from the `.S` files and the kind texts; directive index = `.S` line − 1). The code constants are written
without their namespaces (`open` below), as in the generated modules, so that the negative suite can swap them.

* a step theorem per set-up directive (`Decode.example_step_s<index>`, kinds of `Codec/Kind/WindowSteps.lean`);
* a call-block theorem per callee field (`…_call`, `callDecodeSegmentKindWindow`); the window starts where the set-up
  steps end, so a padding `nop` before the `callq` (Checkpoint, BeaconBlockHeader) or after it
  (PendingConsolidation) is inside the window;
* a byte-segment theorem (`…_seg`, `bytesDecodeSegmentKindWindow`) over two windows;
* the two fully worked compositions: a whole call field (`Decode.example_step_ValidatorIndex_field`, `Prysm.PendingConsolidation.Decode.example_step_TargetIndex_field`)
  and a whole byte field (`Decode.example_step_BlockRoot_field`). These have no kind: they only apply kinded theorems, and
  their statements are checked by the accept proofs that use them (`Prysm/SyncCommitteeMessage/DecodeAcceptFromWindowSteps.lean`, `Prysm/PendingConsolidation/DecodeAcceptFromWindowSteps.lean`).
The callee specification stays a hypothesis `Uint64CalleeAccept "<callee label>"` of each call-block theorem.
After the split of this module, the declarations of the other types are in `Prysm/BeaconBlockHeader/DecodeStepExamples.lean`, `Prysm/Checkpoint/DecodeStepExamples.lean`, `Prysm/Deposit_Data/DecodeStepExamples.lean`, `Prysm/PendingConsolidation/DecodeStepExamples.lean`, `Prysm/PendingPartialWithdrawal/DecodeStepExamples.lean`.
-/

open Machine Runtime Prysm.Checkpoint.Code
variable [Host]

open Codec
namespace Prysm.SyncCommitteeMessage

/-! ## SyncCommitteeMessage.ValidatorIndex — set-up with the receiver already in rax (missed by the frozen generator): six steps, call block, whole field -/

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Directive 82 `mov 0x78(%rsp),%rbx`: stepLoadValueKind. -/
theorem Decode.example_step_directive_82 (k : Nat) (hk : Code.unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh Code.unmarshalSSZ k) :
    ∀
    (base a v : BitVec 64) (ha : base + (120 : Int64).toBitVec = a)
    (F : DataMem → Prop)
    (final : MachineState → Prop) (s : MachineData)
    (hb : s.regs.get64 Reg64.rsp = base) (hm : (Eq ((Int.toBytes 8 v.toInt).At a) ⋆ F) s.dmem)
    (hk' : Eventually (step1 Host.exe) final ⟨Codec.setRegister s Reg64.rbx v, Host.addrOf (k + 83)⟩),
    Eventually (step1 Host.exe) final ⟨s, Host.addrOf (k + 82)⟩ := by
  have hq := Codec.window_infix_at hk 82 1
  have he : Codec.eraseNop ((Code.unmarshalSSZ.drop 82).take 1) = [Codec.instrLoad Reg64.rbx Reg64.rsp 120] := by rfl
  have hend : k + 82 + ((Code.unmarshalSSZ.drop 82).take 1).length = k + 83 := by rfl
  with_reducible exact Codec.step_load_value Reg64.rbx Reg64.rsp 120 _ (k + 82) (k + 83) hq he hend
theorem Decode.example_step_directive_82_kind : ∀ (h : Host), type_of% (@Decode.example_step_directive_82 h) = @Codec.stepLoadValueKind h Code.unmarshalSSZ Reg64.rbx Reg64.rsp 120 82 83 := by
  intro h; with_reducible rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Directive 83 `add $0x28,%rbx`: stepAddKind. -/
theorem Decode.example_step_directive_83 (k : Nat) (hk : Code.unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh Code.unmarshalSSZ k) :
    ∀
    (final : MachineState → Prop) (s : MachineData)
    (hk' : ∀ fl : StatusFlags, Eventually (step1 Host.exe) final
      ⟨{ regs := s.regs.set64 Reg64.rbx (s.regs.get64 Reg64.rbx + (40 : Int64).toBitVec), zmms := s.zmms, status := fl, dmem := s.dmem },
        Host.addrOf (k + 84)⟩),
    Eventually (step1 Host.exe) final ⟨s, Host.addrOf (k + 83)⟩ := by
  have hq := Codec.window_infix_at hk 83 1
  have he : Codec.eraseNop ((Code.unmarshalSSZ.drop 83).take 1) = [Codec.instrAddImmediate Reg64.rbx 40] := by rfl
  have hend : k + 83 + ((Code.unmarshalSSZ.drop 83).take 1).length = k + 84 := by rfl
  with_reducible exact Codec.step_add_immediate Reg64.rbx 40 _ (k + 83) (k + 84) hq he hend
theorem Decode.example_step_directive_83_kind : ∀ (h : Host), type_of% (@Decode.example_step_directive_83 h) = @Codec.stepAddKind h Code.unmarshalSSZ Reg64.rbx 40 83 84 := by
  intro h; with_reducible rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Directive 84 `mov 0x88(%rsp),%rdi`: stepLoadBytesKind. -/
theorem Decode.example_step_directive_84 (k : Nat) (hk : Code.unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh Code.unmarshalSSZ k) :
    ∀
    (base a : BitVec 64) (ha : base + (136 : Int64).toBitVec = a) (bs : List UInt8) (hbs : bs.length = 8)
    (F : DataMem → Prop)
    (final : MachineState → Prop) (s : MachineData)
    (hb : s.regs.get64 Reg64.rsp = base) (hm : (Eq (bs.At a) ⋆ F) s.dmem)
    (hk' : Eventually (step1 Host.exe) final ⟨Codec.setRegister s Reg64.rdi (BitVec.ofInt 64 (Int.ofBytes bs)), Host.addrOf (k + 85)⟩),
    Eventually (step1 Host.exe) final ⟨s, Host.addrOf (k + 84)⟩ := by
  have hq := Codec.window_infix_at hk 84 1
  have he : Codec.eraseNop ((Code.unmarshalSSZ.drop 84).take 1) = [Codec.instrLoad Reg64.rdi Reg64.rsp 136] := by rfl
  have hend : k + 84 + ((Code.unmarshalSSZ.drop 84).take 1).length = k + 85 := by rfl
  with_reducible exact Codec.step_load_bytes Reg64.rdi Reg64.rsp 136 _ (k + 84) (k + 85) hq he hend
theorem Decode.example_step_directive_84_kind : ∀ (h : Host), type_of% (@Decode.example_step_directive_84 h) = @Codec.stepLoadBytesKind h Code.unmarshalSSZ Reg64.rdi Reg64.rsp 136 84 85 := by
  intro h; with_reducible rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Directive 85 `add $-0x28,%rdi`: stepAddKind. -/
theorem Decode.example_step_directive_85 (k : Nat) (hk : Code.unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh Code.unmarshalSSZ k) :
    ∀
    (final : MachineState → Prop) (s : MachineData)
    (hk' : ∀ fl : StatusFlags, Eventually (step1 Host.exe) final
      ⟨{ regs := s.regs.set64 Reg64.rdi (s.regs.get64 Reg64.rdi + ((-40) : Int64).toBitVec), zmms := s.zmms, status := fl, dmem := s.dmem },
        Host.addrOf (k + 86)⟩),
    Eventually (step1 Host.exe) final ⟨s, Host.addrOf (k + 85)⟩ := by
  have hq := Codec.window_infix_at hk 85 1
  have he : Codec.eraseNop ((Code.unmarshalSSZ.drop 85).take 1) = [Codec.instrAddImmediate Reg64.rdi (-40)] := by rfl
  have hend : k + 85 + ((Code.unmarshalSSZ.drop 85).take 1).length = k + 86 := by rfl
  with_reducible exact Codec.step_add_immediate Reg64.rdi (-40) _ (k + 85) (k + 86) hq he hend
theorem Decode.example_step_directive_85_kind : ∀ (h : Host), type_of% (@Decode.example_step_directive_85 h) = @Codec.stepAddKind h Code.unmarshalSSZ Reg64.rdi (-40) 85 86 := by
  intro h; with_reducible rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Directive 86 `add $0x28,%rax`: stepAddKind. -/
theorem Decode.example_step_directive_86 (k : Nat) (hk : Code.unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh Code.unmarshalSSZ k) :
    ∀
    (final : MachineState → Prop) (s : MachineData)
    (hk' : ∀ fl : StatusFlags, Eventually (step1 Host.exe) final
      ⟨{ regs := s.regs.set64 Reg64.rax (s.regs.get64 Reg64.rax + (40 : Int64).toBitVec), zmms := s.zmms, status := fl, dmem := s.dmem },
        Host.addrOf (k + 87)⟩),
    Eventually (step1 Host.exe) final ⟨s, Host.addrOf (k + 86)⟩ := by
  have hq := Codec.window_infix_at hk 86 1
  have he : Codec.eraseNop ((Code.unmarshalSSZ.drop 86).take 1) = [Codec.instrAddImmediate Reg64.rax 40] := by rfl
  have hend : k + 86 + ((Code.unmarshalSSZ.drop 86).take 1).length = k + 87 := by rfl
  with_reducible exact Codec.step_add_immediate Reg64.rax 40 _ (k + 86) (k + 87) hq he hend
theorem Decode.example_step_directive_86_kind : ∀ (h : Host), type_of% (@Decode.example_step_directive_86 h) = @Codec.stepAddKind h Code.unmarshalSSZ Reg64.rax 40 86 87 := by
  intro h; with_reducible rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Directive 87 `mov $0x8,%ecx`: stepMoveImmediateKind. -/
theorem Decode.example_step_directive_87 (k : Nat) (hk : Code.unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh Code.unmarshalSSZ k) :
    ∀
    (final : MachineState → Prop) (s : MachineData)
    (hk' : Eventually (step1 Host.exe) final ⟨Codec.setRegister s Reg64.rcx (BitVec.zeroExtend 64 (BitVec.truncate 32 (8 : Int64).toBitVec)), Host.addrOf (k + 88)⟩),
    Eventually (step1 Host.exe) final ⟨s, Host.addrOf (k + 87)⟩ := by
  have hq := Codec.window_infix_at hk 87 1
  have he : Codec.eraseNop ((Code.unmarshalSSZ.drop 87).take 1) = [Codec.instrMoveImmediate32 Reg64.rcx 8] := by rfl
  have hend : k + 87 + ((Code.unmarshalSSZ.drop 87).take 1).length = k + 88 := by rfl
  with_reducible exact Codec.step_move_immediate Reg64.rcx 8 _ (k + 87) (k + 88) hq he hend
theorem Decode.example_step_directive_87_kind : ∀ (h : Host), type_of% (@Decode.example_step_directive_87 h) = @Codec.stepMoveImmediateKind h Code.unmarshalSSZ Reg64.rcx 8 87 88 := by
  intro h; with_reducible rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- `ValidatorIndex`: call block over the window 88–90 (`callq; test; je`), `callq` at 88, continuation label at 117. -/
theorem Decode.example_step_ValidatorIndex_call (k : Nat) (hk : Code.unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh Code.unmarshalSSZ k) :
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
      (fun st => st.pc = Host.addrOf (k + 117 + 1) ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0
        ∧ st.data.regs.rsp = { toBitVec := sp } ∧ st.data.regs.rbp = rbp0 ∧ st.data.regs.r14 = r140 ∧
        (Eq ((Int.toBytes 8 (Host.addrOf (k + 88 + 1)).toBitVec.toInt).At aRet)
          ⋆ Eq ((Int.toBytes 8 rbp0.toBitVec.toInt).At aFp) ⋆ Eq ((Int.toBytes 8 src.toInt).At aS2)
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (r140.toBitVec + 16))
          ⋆ Eq (e8.At src) ⋆ Eq (e8.At dst) ⋆ F) st.data.dmem)
      ⟨s, Host.addrOf (k + 88)⟩ := by
  have hq := Codec.window_infix_at hk 88 3
  have he : Codec.eraseNop ((Code.unmarshalSSZ.drop 88).take 3) = Codec.callDecode "github.com_OffchainLabs_prysm_v7_consensus_types_primitives.ValidatorIndex.UnmarshalSSZ" "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommitteeMessage.UnmarshalSSZ_1e7" := by rfl
  have hjc : k + 88 + Codec.nonNopIndex ((Code.unmarshalSSZ.drop 88).take 3) 0 = k + 88 := by rfl
  have hB := Codec.infix_sub (q := Codec.callDecodeContinuationLabel "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommitteeMessage.UnmarshalSSZ_1e7") 117 hk
    (by simp only [Code.unmarshalSSZ, Codec.callDecodeContinuationLabel, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero])
  have hl := Machine.label_at' hk hf (j := 117)
    (by simp only [Code.unmarshalSSZ, List.getElem?_cons_succ, List.getElem?_cons_zero]; rfl)
    (by simp only [Code.unmarshalSSZ, List.take_succ_cons, List.take_zero, List.contains_cons, List.contains_nil]; decide)
  with_reducible exact Codec.call_decode_segment_window _ _ _ (k + 88) (k + 88) (k + 117) hq he hjc hB hl
theorem Decode.example_step_ValidatorIndex_call_kind : ∀ (h : Host), type_of% (@Decode.example_step_ValidatorIndex_call h) = @Codec.callDecodeSegmentKindWindow h Code.unmarshalSSZ "github.com_OffchainLabs_prysm_v7_consensus_types_primitives.ValidatorIndex.UnmarshalSSZ" "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommitteeMessage.UnmarshalSSZ_1e7" 88 88 117 := by
  intro h; with_reducible rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- `ValidatorIndex` (callee decoder field, Go offset 40, SSZ offset 40): the WHOLE call field 82–117, composed from the
step theorems of its set-up and the call-block theorem (worked example of the `decoder --steps` emission recipe). The entry
conditions of the call block (rax = `rcv + 40`, rbx = `bf + 40`, rcx = 8) are closed by `rfl` on the state
that the steps computed. -/
theorem Decode.example_step_ValidatorIndex_field (k : Nat) (hk : Code.unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh Code.unmarshalSSZ k) :
    ∀ (hC : Uint64CalleeAccept "github.com_OffchainLabs_prysm_v7_consensus_types_primitives.ValidatorIndex.UnmarshalSSZ")
    (sp rcv bf aRet aFp aS2 aB aD : BitVec 64)
    (hRet : sp - 8 = aRet) (hFp : sp - 16 = aFp) (hS2 : sp + 8 = aS2)
    (hB : sp + (120 : Int64).toBitVec = aB) (hD : sp + (136 : Int64).toBitVec = aD)
    (rbp0 r140 guard : UInt64) (e8 rslot fp s2 c0 vD : List UInt8)
    (he8 : e8.length = 8) (hrs : rslot.length = 8) (hfp : fp.length = 8) (hs2 : s2.length = 8)
    (hc0 : c0.length = 8) (hvD : vD.length = 8) (hguard : guard.toNat < aRet.toNat)
    (F : DataMem → Prop)
    (s : MachineData) (hrsp : s.regs.rsp = { toBitVec := sp }) (hrbp : s.regs.rbp = rbp0)
    (hr14 : s.regs.r14 = r140) (hrax : s.regs.rax.toBitVec = rcv)
    (h_mem : s.dmem =⋆ Eq (rslot.At aRet) ⋆ Eq (fp.At aFp) ⋆ Eq (s2.At aS2)
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (r140.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 bf.toInt).At aB) ⋆ Eq (vD.At aD)
      ⋆ Eq (e8.At (bf + 40)) ⋆ Eq (c0.At (rcv + 40)) ⋆ F),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 117 + 1) ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0
        ∧ st.data.regs.rsp = { toBitVec := sp } ∧ st.data.regs.rbp = rbp0 ∧ st.data.regs.r14 = r140 ∧
        (Eq ((Int.toBytes 8 (Host.addrOf (k + 88 + 1)).toBitVec.toInt).At aRet)
          ⋆ Eq ((Int.toBytes 8 rbp0.toBitVec.toInt).At aFp) ⋆ Eq ((Int.toBytes 8 (bf + 40).toInt).At aS2)
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (r140.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 bf.toInt).At aB) ⋆ Eq (vD.At aD)
          ⋆ Eq (e8.At (bf + 40)) ⋆ Eq (e8.At (rcv + 40)) ⋆ F) st.data.dmem)
      ⟨s, Host.addrOf (k + 82)⟩ := by
  intro hC sp rcv bf aRet aFp aS2 aB aD hRet hFp hS2 hB hD rbp0 r140 guard e8 rslot fp s2 c0 vD he8 hrs hfp hs2 hc0 hvD
    hguard F s hrsp hrbp hr14 hrax h_mem
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at hrsp hrbp hr14 hrax h_mem ⊢
  subst rsp rbp r14 hrax
  apply Decode.example_step_directive_82 k hk hf sp aB bf hB _ _ _ (by rfl) (by ecancel)
  normalize_registers
  apply Decode.example_step_directive_83 k hk hf
  intro fl1; normalize_registers
  apply Decode.example_step_directive_84 k hk hf sp aD hD vD hvD _ _ _ (by rfl) (by ecancel)
  normalize_registers
  apply Decode.example_step_directive_85 k hk hf
  intro fl2; normalize_registers
  apply Decode.example_step_directive_86 k hk hf
  intro fl3; normalize_registers
  apply Decode.example_step_directive_87 k hk hf
  normalize_registers
  refine eventually_trans _ _ _ _ (Decode.example_step_ValidatorIndex_call k hk hf hC sp (rax.toBitVec + 40) (bf + 40) aRet aFp aS2 hRet hFp hS2 rbp0 r140 guard e8 rslot
    fp s2 c0 he8 hrs hfp hs2 hc0 hguard _ _ (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by first | rfl | decide)
    (by ecancel)) ?_
  rintro ⟨d, pc⟩ ⟨hpc, hrax', hrbx', hrsp', hrbp', hr14', Hm⟩
  dsimp only at hpc hrax' hrbx' hrsp' hrbp' hr14' Hm
  apply Eventually.done
  refine ⟨hpc, hrax', hrbx', hrsp', hrbp', hr14', ?_⟩
  dsimp only
  ecancel

/-! ## SyncCommitteeMessage.BlockRoot — byte segment with the receiver reloaded into rax (missed by the frozen generator), its tail as steps, whole field -/

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
/-- `BlockRoot` (32-byte vector): decode segment over the windows 47–55 and 60–71; receiver in rdx after makeslice, in rax after memmove (`callq` at 66). -/
theorem Decode.example_step_BlockRoot_segment (k : Nat) (hk : Code.unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh Code.unmarshalSSZ k) :
    ∀
    (sp rcv bf aR aB aS aRet aLo aP aL aC aSrc : BitVec 64) (St : Nat)
    (hR : sp + (112 : Int64).toBitVec = aR) (hB' : sp + (120 : Int64).toBitVec = aB) (hS : sp + (56 : Int64).toBitVec = aS)
    (hRet : sp - 8 = aRet) (hLo : sp - 8 - BitVec.ofNat 64 St = aLo)
    (hP : rcv + (16 : Int64).toBitVec = aP) (hL : rcv + (24 : Int64).toBitVec = aL) (hC : rcv + (32 : Int64).toBitVec = aC)
    (hSrc : bf + (8 : Int64).toBitVec = aSrc)
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
      (fun st => st.pc = Host.addrOf (k + 72) ∧ st.data.regs.rsp = { toBitVec := sp }
        ∧ st.data.regs.rbp = rbp0 ∧ st.data.regs.r14 = r140 ∧
        ∃ (p : BitVec 64) (spl' lo' : List UInt8), spl'.length = 24 ∧ lo'.length = St
          ∧ st.data.regs.get64 Reg64.rax = rcv ∧
        (Eq ((Int.toBytes 8 rcv.toInt).At aR) ⋆ Eq ((Int.toBytes 8 bf.toInt).At aB)
          ⋆ Eq (spl'.At sp)
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 66 + 1)).toBitVec.toInt).At aRet)
          ⋆ Eq (lo'.At aLo)
          ⋆ Eq ((Int.toBytes 8 p.toInt).At aS)
          ⋆ Heap (avail - 32)
          ⋆ Eq ((Int.toBytes 8 p.toInt).At aP) ⋆ Eq ((Int.toBytes 8 32).At aL)
          ⋆ Eq ((Int.toBytes 8 32).At aC) ⋆ Eq (root.At p)
          ⋆ Eq (root.At aSrc)
          ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf (k + 47)⟩ := by
  have hqA := Codec.window_infix_at hk 47 9
  have heA : Codec.eraseNop ((Code.unmarshalSSZ.drop 47).take 9) = Codec.bytesDecodeHeadRegister Reg64.rdx 32 "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommitteeMessage.UnmarshalSSZ_fd" 112 24 32 := by rfl
  have hqB := Codec.window_infix_at hk 60 12
  have heB : Codec.eraseNop ((Code.unmarshalSSZ.drop 60).take 12) = Codec.bytesDecodeMiddleRegisters Reg64.rdx Reg64.rax 32 "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommitteeMessage.UnmarshalSSZ_fd" "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommitteeMessage.UnmarshalSSZ_13e" 112 120 56 16 24 32 8 := by rfl
  have hjl : k + 60 + Codec.nonNopIndex ((Code.unmarshalSSZ.drop 60).take 12) 0 = k + 60 := by rfl
  have hl := Machine.label_at' hk hf (j := 60)
    (by simp only [Code.unmarshalSSZ, List.getElem?_cons_succ, List.getElem?_cons_zero]; rfl)
    (by simp only [Code.unmarshalSSZ, List.take_succ_cons, List.take_zero, List.contains_cons, List.contains_nil]; decide)
  have hjm : k + 60 + Codec.nonNopIndex ((Code.unmarshalSSZ.drop 60).take 12) 6 = k + 66 := by rfl
  have hend : k + 60 + ((Code.unmarshalSSZ.drop 60).take 12).length = k + 72 := by rfl
  with_reducible exact Codec.bytes_decode_segment_window 32 (Or.inl rfl) Reg64.rdx Reg64.rax (Or.inl rfl) (Or.inl rfl) _ _ _ _ _ _ _ _ _ _ _ (k + 47) (k + 60) (k + 60) (k + 66) (k + 72) hqA heA hqB heB hjl hl hjm hend
theorem Decode.example_step_BlockRoot_segment_kind : ∀ (h : Host), type_of% (@Decode.example_step_BlockRoot_segment h) = @Codec.bytesDecodeSegmentKindWindow h 32 Code.unmarshalSSZ Reg64.rax 47 66 72 112 120 56 16 24 32 8 := by
  intro h; with_reducible rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Directive 72 `mov 0x38(%rsp),%rsi`: stepLoadValueKind. -/
theorem Decode.example_step_directive_72 (k : Nat) (hk : Code.unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh Code.unmarshalSSZ k) :
    ∀
    (base a v : BitVec 64) (ha : base + (56 : Int64).toBitVec = a)
    (F : DataMem → Prop)
    (final : MachineState → Prop) (s : MachineData)
    (hb : s.regs.get64 Reg64.rsp = base) (hm : (Eq ((Int.toBytes 8 v.toInt).At a) ⋆ F) s.dmem)
    (hk' : Eventually (step1 Host.exe) final ⟨Codec.setRegister s Reg64.rsi v, Host.addrOf (k + 73)⟩),
    Eventually (step1 Host.exe) final ⟨s, Host.addrOf (k + 72)⟩ := by
  have hq := Codec.window_infix_at hk 72 1
  have he : Codec.eraseNop ((Code.unmarshalSSZ.drop 72).take 1) = [Codec.instrLoad Reg64.rsi Reg64.rsp 56] := by rfl
  have hend : k + 72 + ((Code.unmarshalSSZ.drop 72).take 1).length = k + 73 := by rfl
  with_reducible exact Codec.step_load_value Reg64.rsi Reg64.rsp 56 _ (k + 72) (k + 73) hq he hend
theorem Decode.example_step_directive_72_kind : ∀ (h : Host), type_of% (@Decode.example_step_directive_72 h) = @Codec.stepLoadValueKind h Code.unmarshalSSZ Reg64.rsi Reg64.rsp 56 72 73 := by
  intro h; with_reducible rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Directive 73 `jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommitteeMessage.UnmarshalSSZ_153`: stepJumpKind. -/
theorem Decode.example_step_directive_73 (k : Nat) (hk : Code.unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh Code.unmarshalSSZ k) :
    ∀
    (final : MachineState → Prop) (s : MachineData)
    (hk' : Eventually (step1 Host.exe) final ⟨s, Host.addrOf (k + 80)⟩),
    Eventually (step1 Host.exe) final ⟨s, Host.addrOf (k + 73)⟩ := by
  have hq := Codec.window_infix_at hk 73 1
  have he : Codec.eraseNop ((Code.unmarshalSSZ.drop 73).take 1) = [Codec.instrJump "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommitteeMessage.UnmarshalSSZ_153"] := by rfl
  have hl := Machine.label_at' hk hf (j := 80)
    (by simp only [Code.unmarshalSSZ, List.getElem?_cons_succ, List.getElem?_cons_zero]; rfl)
    (by simp only [Code.unmarshalSSZ, List.take_succ_cons, List.take_zero, List.contains_cons, List.contains_nil]; decide)
  with_reducible exact Codec.step_jump "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommitteeMessage.UnmarshalSSZ_153" _ (k + 73) (k + 80) hq he hl
theorem Decode.example_step_directive_73_kind : ∀ (h : Host), type_of% (@Decode.example_step_directive_73 h) = @Codec.stepJumpKind h Code.unmarshalSSZ "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommitteeMessage.UnmarshalSSZ_153" 73 80 := by
  intro h; with_reducible rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Directive 80 `L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommitteeMessage.UnmarshalSSZ_153:`: stepLabelKind. -/
theorem Decode.example_step_directive_80 (k : Nat) (hk : Code.unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh Code.unmarshalSSZ k) :
    ∀
    (final : MachineState → Prop) (s : MachineData)
    (hk' : Eventually (step1 Host.exe) final ⟨s, Host.addrOf (k + 81)⟩),
    Eventually (step1 Host.exe) final ⟨s, Host.addrOf (k + 80)⟩ := by
  have hq := Codec.window_infix_at hk 80 1
  have he : Codec.eraseNop ((Code.unmarshalSSZ.drop 80).take 1) = [Codec.instrLabel "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommitteeMessage.UnmarshalSSZ_153"] := by rfl
  have hend : k + 80 + ((Code.unmarshalSSZ.drop 80).take 1).length = k + 81 := by rfl
  with_reducible exact Codec.step_label "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommitteeMessage.UnmarshalSSZ_153" _ (k + 80) (k + 81) hq he hend
theorem Decode.example_step_directive_80_kind : ∀ (h : Host), type_of% (@Decode.example_step_directive_80 h) = @Codec.stepLabelKind h Code.unmarshalSSZ "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommitteeMessage.UnmarshalSSZ_153" 80 81 := by
  intro h; with_reducible rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Directive 81 `mov %rsi,0x10(%rax)`: stepStoreKind. -/
theorem Decode.example_step_directive_81 (k : Nat) (hk : Code.unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh Code.unmarshalSSZ k) :
    ∀
    (base a : BitVec 64) (ha : base + (16 : Int64).toBitVec = a) (bs : List UInt8) (hbs : bs.length = 8)
    (F : DataMem → Prop)
    (final : MachineState → Prop) (s : MachineData)
    (hb : s.regs.get64 Reg64.rax = base) (hm : (Eq (bs.At a) ⋆ F) s.dmem)
    (hk' : ∀ m' : DataMem, (Eq ((Int.toBytes 8 (@BitVec.toInt 64 (s.regs.get64 Reg64.rsi))).At a) ⋆ F) m' →
      Eventually (step1 Host.exe) final ⟨{ s with dmem := m' }, Host.addrOf (k + 82)⟩),
    Eventually (step1 Host.exe) final ⟨s, Host.addrOf (k + 81)⟩ := by
  have hq := Codec.window_infix_at hk 81 1
  have he : Codec.eraseNop ((Code.unmarshalSSZ.drop 81).take 1) = [Codec.instrStore Reg64.rsi Reg64.rax 16] := by rfl
  have hend : k + 81 + ((Code.unmarshalSSZ.drop 81).take 1).length = k + 82 := by rfl
  with_reducible exact Codec.step_store Reg64.rsi Reg64.rax 16 _ (k + 81) (k + 82) hq he hend
theorem Decode.example_step_directive_81_kind : ∀ (h : Host), type_of% (@Decode.example_step_directive_81 h) = @Codec.stepStoreKind h Code.unmarshalSSZ Reg64.rsi Reg64.rax 16 81 82 := by
  intro h; with_reducible rfl

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
/-- `BlockRoot`: the WHOLE byte field 47–81 (segment, then the tail `mov 0x38(%rsp),%rsi; jmp; label; mov %rsi,0x10(%rax)`
as four steps): worked example of the `decoder --steps` emission recipe for a byte field. Statement = the segment statement
with the end at directive 82. -/
theorem Decode.example_step_BlockRoot_field (k : Nat) (hk : Code.unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh Code.unmarshalSSZ k) :
    ∀
    (sp rcv bf aR aB aS aRet aLo aP aL aC aSrc : BitVec 64) (St : Nat)
    (hR : sp + (112 : Int64).toBitVec = aR) (hB' : sp + (120 : Int64).toBitVec = aB) (hS : sp + (56 : Int64).toBitVec = aS)
    (hRet : sp - 8 = aRet) (hLo : sp - 8 - BitVec.ofNat 64 St = aLo)
    (hP : rcv + (16 : Int64).toBitVec = aP) (hL : rcv + (24 : Int64).toBitVec = aL) (hC : rcv + (32 : Int64).toBitVec = aC)
    (hSrc : bf + (8 : Int64).toBitVec = aSrc)
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
      (fun st => st.pc = Host.addrOf (k + 82) ∧ st.data.regs.rsp = { toBitVec := sp }
        ∧ st.data.regs.rbp = rbp0 ∧ st.data.regs.r14 = r140 ∧
        ∃ (p : BitVec 64) (spl' lo' : List UInt8), spl'.length = 24 ∧ lo'.length = St
          ∧ st.data.regs.get64 Reg64.rax = rcv ∧
        (Eq ((Int.toBytes 8 rcv.toInt).At aR) ⋆ Eq ((Int.toBytes 8 bf.toInt).At aB)
          ⋆ Eq (spl'.At sp)
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 66 + 1)).toBitVec.toInt).At aRet)
          ⋆ Eq (lo'.At aLo)
          ⋆ Eq ((Int.toBytes 8 p.toInt).At aS)
          ⋆ Heap (avail - 32)
          ⋆ Eq ((Int.toBytes 8 p.toInt).At aP) ⋆ Eq ((Int.toBytes 8 32).At aL)
          ⋆ Eq ((Int.toBytes 8 32).At aC) ⋆ Eq (root.At p)
          ⋆ Eq (root.At aSrc)
          ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf (k + 47)⟩ := by
  intro sp rcv bf aR aB aS aRet aLo aP aL aC aSrc St hR hB' hS hRet hLo hP hL hC hSrc rbp0 r140 root hroot spl rslot lo lS vP vL vC hspl hrs hlo hlS hvP hvL hvC R Heap avail hav s hrsp hrbp hr14 h_mem hms hmm
  refine eventually_trans _ _ _ _ (Decode.example_step_BlockRoot_segment k hk hf sp rcv bf aR aB aS aRet aLo aP aL aC aSrc St hR hB' hS hRet hLo hP hL hC hSrc rbp0 r140 root hroot spl rslot lo lS vP vL vC hspl hrs hlo hlS hvP hvL hvC R Heap avail hav s hrsp hrbp hr14 h_mem hms hmm) ?_
  rintro ⟨d, pc⟩ ⟨hpc, hrsp', hrbp', hr14', p, spl', lo', hspl', hlo', hrY, Hm⟩
  dsimp only at hpc hrsp' hrbp' hr14' hrY Hm
  subst hpc
  obtain ⟨⟨rax1, rbx1, rcx1, rdx1, rsi1, rdi1, rsp1, rbp1, r81, r91, r101, r111, r121, r131, r141, r151⟩, zmms1, flags1, mem1⟩ := d
  simp only at hrsp' hrbp' hr14' hrY Hm
  subst hrsp' hrbp' hr14'
  apply Decode.example_step_directive_72 k hk hf sp aS p hS _ _ _ (by rfl) (by ecancel)
  normalize_registers
  apply Decode.example_step_directive_73 k hk hf
  apply Decode.example_step_directive_80 k hk hf
  apply Decode.example_step_directive_81 k hk hf rcv aP hP (Int.toBytes 8 p.toInt) (Int.toBytes_length 8 _) _ _ _ (by exact hrY) (by ecancel)
  intro m' H
  normalize_registers
  simp only [Reg64s.get64] at H
  apply Eventually.done
  refine ⟨rfl, rfl, rfl, rfl, p, spl', lo', hspl', hlo', hrY, ?_⟩
  dsimp only
  ecancel

/-! ## SyncCommitteeMessage.Signature — `nop` before `callq runtime.makeslice` -/

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
/-- `Signature` (96-byte vector): decode segment over the windows 120–129 and 134–145; receiver in rdx after makeslice, in rdx after memmove (`callq` at 140); a `nop` is inside the first window. -/
theorem Decode.example_step_Signature_segment (k : Nat) (hk : Code.unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh Code.unmarshalSSZ k) :
    ∀
    (sp rcv bf aR aB aS aRet aLo aP aL aC aSrc : BitVec 64) (St : Nat)
    (hR : sp + (112 : Int64).toBitVec = aR) (hB' : sp + (120 : Int64).toBitVec = aB) (hS : sp + (56 : Int64).toBitVec = aS)
    (hRet : sp - 8 = aRet) (hLo : sp - 8 - BitVec.ofNat 64 St = aLo)
    (hP : rcv + (48 : Int64).toBitVec = aP) (hL : rcv + (56 : Int64).toBitVec = aL) (hC : rcv + (64 : Int64).toBitVec = aC)
    (hSrc : bf + (48 : Int64).toBitVec = aSrc)
    (rbp0 r140 : UInt64) (root : List UInt8) (hroot : root.length = 96)
    (spl rslot lo lS vP vL vC : List UInt8)
    (hspl : spl.length = 24) (hrs : rslot.length = 8) (hlo : lo.length = St) (hlS : lS.length = 8)
    (hvP : vP.length = 8) (hvL : vL.length = 8) (hvC : vC.length = 8)
    (R : DataMem → Prop) (Heap : Nat → DataMem → Prop) (avail : Nat) (hav : 96 ≤ avail)
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
      (fun st => st.pc = Host.addrOf (k + 146) ∧ st.data.regs.rsp = { toBitVec := sp }
        ∧ st.data.regs.rbp = rbp0 ∧ st.data.regs.r14 = r140 ∧
        ∃ (p : BitVec 64) (spl' lo' : List UInt8), spl'.length = 24 ∧ lo'.length = St
          ∧ st.data.regs.get64 Reg64.rdx = rcv ∧
        (Eq ((Int.toBytes 8 rcv.toInt).At aR) ⋆ Eq ((Int.toBytes 8 bf.toInt).At aB)
          ⋆ Eq (spl'.At sp)
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 140 + 1)).toBitVec.toInt).At aRet)
          ⋆ Eq (lo'.At aLo)
          ⋆ Eq ((Int.toBytes 8 p.toInt).At aS)
          ⋆ Heap (avail - 96)
          ⋆ Eq ((Int.toBytes 8 p.toInt).At aP) ⋆ Eq ((Int.toBytes 8 96).At aL)
          ⋆ Eq ((Int.toBytes 8 96).At aC) ⋆ Eq (root.At p)
          ⋆ Eq (root.At aSrc)
          ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf (k + 120)⟩ := by
  have hqA := Codec.window_infix_at hk 120 10
  have heA : Codec.eraseNop ((Code.unmarshalSSZ.drop 120).take 10) = Codec.bytesDecodeHeadRegister Reg64.rdx 96 "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommitteeMessage.UnmarshalSSZ_233" 112 56 64 := by rfl
  have hqB := Codec.window_infix_at hk 134 12
  have heB : Codec.eraseNop ((Code.unmarshalSSZ.drop 134).take 12) = Codec.bytesDecodeMiddleRegisters Reg64.rdx Reg64.rdx 96 "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommitteeMessage.UnmarshalSSZ_233" "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommitteeMessage.UnmarshalSSZ_274" 112 120 56 48 56 64 48 := by rfl
  have hjl : k + 134 + Codec.nonNopIndex ((Code.unmarshalSSZ.drop 134).take 12) 0 = k + 134 := by rfl
  have hl := Machine.label_at' hk hf (j := 134)
    (by simp only [Code.unmarshalSSZ, List.getElem?_cons_succ, List.getElem?_cons_zero]; rfl)
    (by simp only [Code.unmarshalSSZ, List.take_succ_cons, List.take_zero, List.contains_cons, List.contains_nil]; decide)
  have hjm : k + 134 + Codec.nonNopIndex ((Code.unmarshalSSZ.drop 134).take 12) 6 = k + 140 := by rfl
  have hend : k + 134 + ((Code.unmarshalSSZ.drop 134).take 12).length = k + 146 := by rfl
  with_reducible exact Codec.bytes_decode_segment_window 96 (Or.inr (Or.inr rfl)) Reg64.rdx Reg64.rdx (Or.inl rfl) (Or.inr (Or.inr (Or.inl rfl))) _ _ _ _ _ _ _ _ _ _ _ (k + 120) (k + 134) (k + 134) (k + 140) (k + 146) hqA heA hqB heB hjl hl hjm hend
theorem Decode.example_step_Signature_segment_kind : ∀ (h : Host), type_of% (@Decode.example_step_Signature_segment h) = @Codec.bytesDecodeSegmentKindWindow h 96 Code.unmarshalSSZ Reg64.rdx 120 140 146 112 120 56 48 56 64 48 := by
  intro h; with_reducible rfl

end Prysm.SyncCommitteeMessage
