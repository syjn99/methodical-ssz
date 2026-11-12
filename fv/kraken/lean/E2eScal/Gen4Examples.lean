import Codec.Kind.WindowSteps
import Codec.Kind.FixedBytesDecodeWindow
import E2eScal.CallReg
import E2eScal.H5Code
import E2eScal.H4Code
import E2eScal.BhCode
import E2e.Code

/-!
# Example instances of the window and step mechanisms on the development sites

One theorem and one `_kind` line per emitted unit, in the shape a generated theorem is to have (the idiom of
`Gen3Examples.lean`). Examples for the generator unit; not generator output (the text was produced by a
scratch script from the `.S` files and the kind texts; directive index = `.S` line − 1). The code constants are written
without their namespaces (`open` below), as in the generated modules, so that the negative suite can swap them.

* a step theorem per set-up directive (`<type>_g4_s<index>`, kinds of `KindStep.lean`);
* a call-block theorem per callee field (`…_call`, `callDecSegKindG4`); the window starts where the set-up
  steps end, so a padding `nop` before the `callq` (Checkpoint, BeaconBlockHeader) or after it
  (PendingConsolidation) is inside the window;
* a byte-segment theorem (`…_seg`, `bytesDecSegKindWindow`) over two windows;
* the two fully worked compositions: a whole call field (`sm_g4_ValidatorIndex_field`, `pc_g4_TargetIndex_field`)
  and a whole byte field (`sm_g4_BlockRoot_field`). These have no kind: they only apply kinded theorems, and
  their statements are checked by the accept proofs that use them (`SmAcceptG4.lean`, `PcAcceptG4.lean`).
The callee specification stays a hypothesis `U64CalleeAcc "<callee label>"` of each call-block theorem.
-/

open Machine Runtime TestTarget E2eScal.H5Code E2eScal.H4Code E2eScal.BhCode E2e.Code
variable [Host]

open Codec
namespace E2eScal.Gen4Ex

/-! ## SyncCommitteeMessage.ValidatorIndex — set-up with the receiver already in rax (missed by the hold-out run): six steps, call block, whole field -/

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Directive 82 `mov 0x78(%rsp),%rbx`: stepLdvKind. -/
theorem sm_g4_s82 (k : Nat) (hk : SmUnmarshal.IsInfixAt Host.prog k) (hf : LabelsFresh SmUnmarshal k) :
    ∀
    (base a v : BitVec 64) (ha : base + (120 : Int64).toBitVec = a)
    (F : DataMem → Prop)
    (final : MachineState → Prop) (s : MachineData)
    (hb : s.regs.get64 Reg64.rsp = base) (hm : (Eq ((Int.toBytes 8 v.toInt).At a) ⋆ F) s.dmem)
    (hk' : Eventually (step1 Host.exe) final ⟨Codec.setR s Reg64.rbx v, Host.addrOf (k + 83)⟩),
    Eventually (step1 Host.exe) final ⟨s, Host.addrOf (k + 82)⟩ := by
  have hq := Codec.win hk 82 1
  have he : Codec.eraseNop ((SmUnmarshal.drop 82).take 1) = [Codec.iLd Reg64.rbx Reg64.rsp 120] := by rfl
  have hend : k + 82 + ((SmUnmarshal.drop 82).take 1).length = k + 83 := by rfl
  with_reducible exact Codec.kstep_ldv Reg64.rbx Reg64.rsp 120 _ (k + 82) (k + 83) hq he hend
theorem sm_g4_s82_kind : ∀ (h : Host), type_of% (@sm_g4_s82 h) = @Codec.stepLdvKind h SmUnmarshal Reg64.rbx Reg64.rsp 120 82 83 := by
  intro h; with_reducible rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Directive 83 `add $0x28,%rbx`: stepAddKind. -/
theorem sm_g4_s83 (k : Nat) (hk : SmUnmarshal.IsInfixAt Host.prog k) (hf : LabelsFresh SmUnmarshal k) :
    ∀
    (final : MachineState → Prop) (s : MachineData)
    (hk' : ∀ fl : StatusFlags, Eventually (step1 Host.exe) final
      ⟨{ regs := s.regs.set64 Reg64.rbx (s.regs.get64 Reg64.rbx + (40 : Int64).toBitVec), zmms := s.zmms, status := fl, dmem := s.dmem },
        Host.addrOf (k + 84)⟩),
    Eventually (step1 Host.exe) final ⟨s, Host.addrOf (k + 83)⟩ := by
  have hq := Codec.win hk 83 1
  have he : Codec.eraseNop ((SmUnmarshal.drop 83).take 1) = [Codec.iAdd Reg64.rbx 40] := by rfl
  have hend : k + 83 + ((SmUnmarshal.drop 83).take 1).length = k + 84 := by rfl
  with_reducible exact Codec.kstep_add Reg64.rbx 40 _ (k + 83) (k + 84) hq he hend
theorem sm_g4_s83_kind : ∀ (h : Host), type_of% (@sm_g4_s83 h) = @Codec.stepAddKind h SmUnmarshal Reg64.rbx 40 83 84 := by
  intro h; with_reducible rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Directive 84 `mov 0x88(%rsp),%rdi`: stepLdbKind. -/
theorem sm_g4_s84 (k : Nat) (hk : SmUnmarshal.IsInfixAt Host.prog k) (hf : LabelsFresh SmUnmarshal k) :
    ∀
    (base a : BitVec 64) (ha : base + (136 : Int64).toBitVec = a) (bs : List UInt8) (hbs : bs.length = 8)
    (F : DataMem → Prop)
    (final : MachineState → Prop) (s : MachineData)
    (hb : s.regs.get64 Reg64.rsp = base) (hm : (Eq (bs.At a) ⋆ F) s.dmem)
    (hk' : Eventually (step1 Host.exe) final ⟨Codec.setR s Reg64.rdi (BitVec.ofInt 64 (Int.ofBytes bs)), Host.addrOf (k + 85)⟩),
    Eventually (step1 Host.exe) final ⟨s, Host.addrOf (k + 84)⟩ := by
  have hq := Codec.win hk 84 1
  have he : Codec.eraseNop ((SmUnmarshal.drop 84).take 1) = [Codec.iLd Reg64.rdi Reg64.rsp 136] := by rfl
  have hend : k + 84 + ((SmUnmarshal.drop 84).take 1).length = k + 85 := by rfl
  with_reducible exact Codec.kstep_ldb Reg64.rdi Reg64.rsp 136 _ (k + 84) (k + 85) hq he hend
theorem sm_g4_s84_kind : ∀ (h : Host), type_of% (@sm_g4_s84 h) = @Codec.stepLdbKind h SmUnmarshal Reg64.rdi Reg64.rsp 136 84 85 := by
  intro h; with_reducible rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Directive 85 `add $-0x28,%rdi`: stepAddKind. -/
theorem sm_g4_s85 (k : Nat) (hk : SmUnmarshal.IsInfixAt Host.prog k) (hf : LabelsFresh SmUnmarshal k) :
    ∀
    (final : MachineState → Prop) (s : MachineData)
    (hk' : ∀ fl : StatusFlags, Eventually (step1 Host.exe) final
      ⟨{ regs := s.regs.set64 Reg64.rdi (s.regs.get64 Reg64.rdi + ((-40) : Int64).toBitVec), zmms := s.zmms, status := fl, dmem := s.dmem },
        Host.addrOf (k + 86)⟩),
    Eventually (step1 Host.exe) final ⟨s, Host.addrOf (k + 85)⟩ := by
  have hq := Codec.win hk 85 1
  have he : Codec.eraseNop ((SmUnmarshal.drop 85).take 1) = [Codec.iAdd Reg64.rdi (-40)] := by rfl
  have hend : k + 85 + ((SmUnmarshal.drop 85).take 1).length = k + 86 := by rfl
  with_reducible exact Codec.kstep_add Reg64.rdi (-40) _ (k + 85) (k + 86) hq he hend
theorem sm_g4_s85_kind : ∀ (h : Host), type_of% (@sm_g4_s85 h) = @Codec.stepAddKind h SmUnmarshal Reg64.rdi (-40) 85 86 := by
  intro h; with_reducible rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Directive 86 `add $0x28,%rax`: stepAddKind. -/
theorem sm_g4_s86 (k : Nat) (hk : SmUnmarshal.IsInfixAt Host.prog k) (hf : LabelsFresh SmUnmarshal k) :
    ∀
    (final : MachineState → Prop) (s : MachineData)
    (hk' : ∀ fl : StatusFlags, Eventually (step1 Host.exe) final
      ⟨{ regs := s.regs.set64 Reg64.rax (s.regs.get64 Reg64.rax + (40 : Int64).toBitVec), zmms := s.zmms, status := fl, dmem := s.dmem },
        Host.addrOf (k + 87)⟩),
    Eventually (step1 Host.exe) final ⟨s, Host.addrOf (k + 86)⟩ := by
  have hq := Codec.win hk 86 1
  have he : Codec.eraseNop ((SmUnmarshal.drop 86).take 1) = [Codec.iAdd Reg64.rax 40] := by rfl
  have hend : k + 86 + ((SmUnmarshal.drop 86).take 1).length = k + 87 := by rfl
  with_reducible exact Codec.kstep_add Reg64.rax 40 _ (k + 86) (k + 87) hq he hend
theorem sm_g4_s86_kind : ∀ (h : Host), type_of% (@sm_g4_s86 h) = @Codec.stepAddKind h SmUnmarshal Reg64.rax 40 86 87 := by
  intro h; with_reducible rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Directive 87 `mov $0x8,%ecx`: stepMovIKind. -/
theorem sm_g4_s87 (k : Nat) (hk : SmUnmarshal.IsInfixAt Host.prog k) (hf : LabelsFresh SmUnmarshal k) :
    ∀
    (final : MachineState → Prop) (s : MachineData)
    (hk' : Eventually (step1 Host.exe) final ⟨Codec.setR s Reg64.rcx (BitVec.zeroExtend 64 (BitVec.truncate 32 (8 : Int64).toBitVec)), Host.addrOf (k + 88)⟩),
    Eventually (step1 Host.exe) final ⟨s, Host.addrOf (k + 87)⟩ := by
  have hq := Codec.win hk 87 1
  have he : Codec.eraseNop ((SmUnmarshal.drop 87).take 1) = [Codec.iMovI Reg64.rcx 8] := by rfl
  have hend : k + 87 + ((SmUnmarshal.drop 87).take 1).length = k + 88 := by rfl
  with_reducible exact Codec.kstep_movi Reg64.rcx 8 _ (k + 87) (k + 88) hq he hend
theorem sm_g4_s87_kind : ∀ (h : Host), type_of% (@sm_g4_s87 h) = @Codec.stepMovIKind h SmUnmarshal Reg64.rcx 8 87 88 := by
  intro h; with_reducible rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- `ValidatorIndex`: call block over the window 88–90 (`callq; test; je`), `callq` at 88, continuation label at 117. -/
theorem sm_g4_ValidatorIndex_call (k : Nat) (hk : SmUnmarshal.IsInfixAt Host.prog k) (hf : LabelsFresh SmUnmarshal k) :
    ∀ (hC : U64CalleeAcc "github.com_OffchainLabs_prysm_v7_consensus_types_primitives.ValidatorIndex.UnmarshalSSZ")
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
  have hq := Codec.win hk 88 3
  have he : Codec.eraseNop ((SmUnmarshal.drop 88).take 3) = E2eScal.callDec "github.com_OffchainLabs_prysm_v7_consensus_types_primitives.ValidatorIndex.UnmarshalSSZ" "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommitteeMessage.UnmarshalSSZ_1e7" := by rfl
  have hjc : k + 88 + Codec.nopPos ((SmUnmarshal.drop 88).take 3) 0 = k + 88 := by rfl
  have hB := Codec.infix_sub (q := E2eScal.callDecL "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommitteeMessage.UnmarshalSSZ_1e7") 117 hk
    (by simp only [SmUnmarshal, E2eScal.callDecL, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero])
  have hl := Machine.label_at' hk hf (j := 117)
    (by simp only [SmUnmarshal, List.getElem?_cons_succ, List.getElem?_cons_zero]; rfl)
    (by simp only [SmUnmarshal, List.take_succ_cons, List.take_zero, List.contains_cons, List.contains_nil]; decide)
  with_reducible exact E2eScal.calldec_seg_w _ _ _ (k + 88) (k + 88) (k + 117) hq he hjc hB hl
theorem sm_g4_ValidatorIndex_call_kind : ∀ (h : Host), type_of% (@sm_g4_ValidatorIndex_call h) = @E2eScal.callDecSegKindG4 h SmUnmarshal "github.com_OffchainLabs_prysm_v7_consensus_types_primitives.ValidatorIndex.UnmarshalSSZ" "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommitteeMessage.UnmarshalSSZ_1e7" 88 88 117 := by
  intro h; with_reducible rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- `ValidatorIndex` (callee decoder field, Go offset 40, SSZ offset 40): the WHOLE call field 82–117, composed from the
step theorems of its set-up and the call-block theorem (worked example of the `p2dec --gen4` emission recipe). The entry
conditions of the call block (rax = `rcv + 40`, rbx = `bf + 40`, rcx = 8) are closed by `rfl` on the state
that the steps computed. -/
theorem sm_g4_ValidatorIndex_field (k : Nat) (hk : SmUnmarshal.IsInfixAt Host.prog k) (hf : LabelsFresh SmUnmarshal k) :
    ∀ (hC : U64CalleeAcc "github.com_OffchainLabs_prysm_v7_consensus_types_primitives.ValidatorIndex.UnmarshalSSZ")
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
  apply sm_g4_s82 k hk hf sp aB bf hB _ _ _ (by rfl) (by ecancel)
  kn
  apply sm_g4_s83 k hk hf
  intro fl1; kn
  apply sm_g4_s84 k hk hf sp aD hD vD hvD _ _ _ (by rfl) (by ecancel)
  kn
  apply sm_g4_s85 k hk hf
  intro fl2; kn
  apply sm_g4_s86 k hk hf
  intro fl3; kn
  apply sm_g4_s87 k hk hf
  kn
  refine eventually_trans _ _ _ _ (sm_g4_ValidatorIndex_call k hk hf hC sp (rax.toBitVec + 40) (bf + 40) aRet aFp aS2 hRet hFp hS2 rbp0 r140 guard e8 rslot
    fp s2 c0 he8 hrs hfp hs2 hc0 hguard _ _ (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by first | rfl | decide)
    (by ecancel)) ?_
  rintro ⟨d, pc⟩ ⟨hpc, hrax', hrbx', hrsp', hrbp', hr14', Hm⟩
  dsimp only at hpc hrax' hrbx' hrsp' hrbp' hr14' Hm
  apply Eventually.done
  refine ⟨hpc, hrax', hrbx', hrsp', hrbp', hr14', ?_⟩
  dsimp only
  ecancel

/-! ## SyncCommitteeMessage.BlockRoot — byte segment with the receiver reloaded into rax (missed by the hold-out run), its tail as steps, whole field -/

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
/-- `BlockRoot` (32-byte vector): decode segment over the windows 47–55 and 60–71; receiver in rdx after makeslice, in rax after memmove (`callq` at 66). -/
theorem sm_g4_BlockRoot_seg (k : Nat) (hk : SmUnmarshal.IsInfixAt Host.prog k) (hf : LabelsFresh SmUnmarshal k) :
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
    (hms : MakesliceC Heap E2e.Data.e2eU8Type_addr 1 St) (hmm : MemmoveC St),
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
  have hqA := Codec.win hk 47 9
  have heA : Codec.eraseNop ((SmUnmarshal.drop 47).take 9) = Codec.bytesDecHeadR Reg64.rdx 32 "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommitteeMessage.UnmarshalSSZ_fd" 112 24 32 := by rfl
  have hqB := Codec.win hk 60 12
  have heB : Codec.eraseNop ((SmUnmarshal.drop 60).take 12) = Codec.bytesDecMidR Reg64.rdx Reg64.rax 32 "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommitteeMessage.UnmarshalSSZ_fd" "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommitteeMessage.UnmarshalSSZ_13e" 112 120 56 16 24 32 8 := by rfl
  have hjl : k + 60 + Codec.nopPos ((SmUnmarshal.drop 60).take 12) 0 = k + 60 := by rfl
  have hl := Machine.label_at' hk hf (j := 60)
    (by simp only [SmUnmarshal, List.getElem?_cons_succ, List.getElem?_cons_zero]; rfl)
    (by simp only [SmUnmarshal, List.take_succ_cons, List.take_zero, List.contains_cons, List.contains_nil]; decide)
  have hjm : k + 60 + Codec.nopPos ((SmUnmarshal.drop 60).take 12) 6 = k + 66 := by rfl
  have hend : k + 60 + ((SmUnmarshal.drop 60).take 12).length = k + 72 := by rfl
  with_reducible exact Codec.bytesdec_seg_window 32 (Or.inl rfl) Reg64.rdx Reg64.rax (Or.inl rfl) (Or.inl rfl) _ _ _ _ _ _ _ _ _ _ _ (k + 47) (k + 60) (k + 60) (k + 66) (k + 72) hqA heA hqB heB hjl hl hjm hend
theorem sm_g4_BlockRoot_seg_kind : ∀ (h : Host), type_of% (@sm_g4_BlockRoot_seg h) = @Codec.bytesDecSegKindWindow h 32 SmUnmarshal Reg64.rax 47 66 72 112 120 56 16 24 32 8 := by
  intro h; with_reducible rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Directive 72 `mov 0x38(%rsp),%rsi`: stepLdvKind. -/
theorem sm_g4_s72 (k : Nat) (hk : SmUnmarshal.IsInfixAt Host.prog k) (hf : LabelsFresh SmUnmarshal k) :
    ∀
    (base a v : BitVec 64) (ha : base + (56 : Int64).toBitVec = a)
    (F : DataMem → Prop)
    (final : MachineState → Prop) (s : MachineData)
    (hb : s.regs.get64 Reg64.rsp = base) (hm : (Eq ((Int.toBytes 8 v.toInt).At a) ⋆ F) s.dmem)
    (hk' : Eventually (step1 Host.exe) final ⟨Codec.setR s Reg64.rsi v, Host.addrOf (k + 73)⟩),
    Eventually (step1 Host.exe) final ⟨s, Host.addrOf (k + 72)⟩ := by
  have hq := Codec.win hk 72 1
  have he : Codec.eraseNop ((SmUnmarshal.drop 72).take 1) = [Codec.iLd Reg64.rsi Reg64.rsp 56] := by rfl
  have hend : k + 72 + ((SmUnmarshal.drop 72).take 1).length = k + 73 := by rfl
  with_reducible exact Codec.kstep_ldv Reg64.rsi Reg64.rsp 56 _ (k + 72) (k + 73) hq he hend
theorem sm_g4_s72_kind : ∀ (h : Host), type_of% (@sm_g4_s72 h) = @Codec.stepLdvKind h SmUnmarshal Reg64.rsi Reg64.rsp 56 72 73 := by
  intro h; with_reducible rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Directive 73 `jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommitteeMessage.UnmarshalSSZ_153`: stepJmpKind. -/
theorem sm_g4_s73 (k : Nat) (hk : SmUnmarshal.IsInfixAt Host.prog k) (hf : LabelsFresh SmUnmarshal k) :
    ∀
    (final : MachineState → Prop) (s : MachineData)
    (hk' : Eventually (step1 Host.exe) final ⟨s, Host.addrOf (k + 80)⟩),
    Eventually (step1 Host.exe) final ⟨s, Host.addrOf (k + 73)⟩ := by
  have hq := Codec.win hk 73 1
  have he : Codec.eraseNop ((SmUnmarshal.drop 73).take 1) = [Codec.iJmp "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommitteeMessage.UnmarshalSSZ_153"] := by rfl
  have hl := Machine.label_at' hk hf (j := 80)
    (by simp only [SmUnmarshal, List.getElem?_cons_succ, List.getElem?_cons_zero]; rfl)
    (by simp only [SmUnmarshal, List.take_succ_cons, List.take_zero, List.contains_cons, List.contains_nil]; decide)
  with_reducible exact Codec.kstep_jmp "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommitteeMessage.UnmarshalSSZ_153" _ (k + 73) (k + 80) hq he hl
theorem sm_g4_s73_kind : ∀ (h : Host), type_of% (@sm_g4_s73 h) = @Codec.stepJmpKind h SmUnmarshal "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommitteeMessage.UnmarshalSSZ_153" 73 80 := by
  intro h; with_reducible rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Directive 80 `L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommitteeMessage.UnmarshalSSZ_153:`: stepLabelKind. -/
theorem sm_g4_s80 (k : Nat) (hk : SmUnmarshal.IsInfixAt Host.prog k) (hf : LabelsFresh SmUnmarshal k) :
    ∀
    (final : MachineState → Prop) (s : MachineData)
    (hk' : Eventually (step1 Host.exe) final ⟨s, Host.addrOf (k + 81)⟩),
    Eventually (step1 Host.exe) final ⟨s, Host.addrOf (k + 80)⟩ := by
  have hq := Codec.win hk 80 1
  have he : Codec.eraseNop ((SmUnmarshal.drop 80).take 1) = [Codec.iLabel "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommitteeMessage.UnmarshalSSZ_153"] := by rfl
  have hend : k + 80 + ((SmUnmarshal.drop 80).take 1).length = k + 81 := by rfl
  with_reducible exact Codec.kstep_label "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommitteeMessage.UnmarshalSSZ_153" _ (k + 80) (k + 81) hq he hend
theorem sm_g4_s80_kind : ∀ (h : Host), type_of% (@sm_g4_s80 h) = @Codec.stepLabelKind h SmUnmarshal "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommitteeMessage.UnmarshalSSZ_153" 80 81 := by
  intro h; with_reducible rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Directive 81 `mov %rsi,0x10(%rax)`: stepStKind. -/
theorem sm_g4_s81 (k : Nat) (hk : SmUnmarshal.IsInfixAt Host.prog k) (hf : LabelsFresh SmUnmarshal k) :
    ∀
    (base a : BitVec 64) (ha : base + (16 : Int64).toBitVec = a) (bs : List UInt8) (hbs : bs.length = 8)
    (F : DataMem → Prop)
    (final : MachineState → Prop) (s : MachineData)
    (hb : s.regs.get64 Reg64.rax = base) (hm : (Eq (bs.At a) ⋆ F) s.dmem)
    (hk' : ∀ m' : DataMem, (Eq ((Int.toBytes 8 (@BitVec.toInt 64 (s.regs.get64 Reg64.rsi))).At a) ⋆ F) m' →
      Eventually (step1 Host.exe) final ⟨{ s with dmem := m' }, Host.addrOf (k + 82)⟩),
    Eventually (step1 Host.exe) final ⟨s, Host.addrOf (k + 81)⟩ := by
  have hq := Codec.win hk 81 1
  have he : Codec.eraseNop ((SmUnmarshal.drop 81).take 1) = [Codec.iSt Reg64.rsi Reg64.rax 16] := by rfl
  have hend : k + 81 + ((SmUnmarshal.drop 81).take 1).length = k + 82 := by rfl
  with_reducible exact Codec.kstep_st Reg64.rsi Reg64.rax 16 _ (k + 81) (k + 82) hq he hend
theorem sm_g4_s81_kind : ∀ (h : Host), type_of% (@sm_g4_s81 h) = @Codec.stepStKind h SmUnmarshal Reg64.rsi Reg64.rax 16 81 82 := by
  intro h; with_reducible rfl

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
/-- `BlockRoot`: the WHOLE byte field 47–81 (segment, then the tail `mov 0x38(%rsp),%rsi; jmp; label; mov %rsi,0x10(%rax)`
as four steps): worked example of the `p2dec --gen4` emission recipe for a byte field. Statement = the segment statement
with the end at directive 82. -/
theorem sm_g4_BlockRoot_field (k : Nat) (hk : SmUnmarshal.IsInfixAt Host.prog k) (hf : LabelsFresh SmUnmarshal k) :
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
    (hms : MakesliceC Heap E2e.Data.e2eU8Type_addr 1 St) (hmm : MemmoveC St),
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
  refine eventually_trans _ _ _ _ (sm_g4_BlockRoot_seg k hk hf sp rcv bf aR aB aS aRet aLo aP aL aC aSrc St hR hB' hS hRet hLo hP hL hC hSrc rbp0 r140 root hroot spl rslot lo lS vP vL vC hspl hrs hlo hlS hvP hvL hvC R Heap avail hav s hrsp hrbp hr14 h_mem hms hmm) ?_
  rintro ⟨d, pc⟩ ⟨hpc, hrsp', hrbp', hr14', p, spl', lo', hspl', hlo', hrY, Hm⟩
  dsimp only at hpc hrsp' hrbp' hr14' hrY Hm
  subst hpc
  obtain ⟨⟨rax1, rbx1, rcx1, rdx1, rsi1, rdi1, rsp1, rbp1, r81, r91, r101, r111, r121, r131, r141, r151⟩, zmms1, flags1, mem1⟩ := d
  simp only at hrsp' hrbp' hr14' hrY Hm
  subst hrsp' hrbp' hr14'
  apply sm_g4_s72 k hk hf sp aS p hS _ _ _ (by rfl) (by ecancel)
  kn
  apply sm_g4_s73 k hk hf
  apply sm_g4_s80 k hk hf
  apply sm_g4_s81 k hk hf rcv aP hP (Int.toBytes 8 p.toInt) (Int.toBytes_length 8 _) _ _ _ (by exact hrY) (by ecancel)
  intro m' H
  kn
  simp only [Reg64s.get64] at H
  apply Eventually.done
  refine ⟨rfl, rfl, rfl, rfl, p, spl', lo', hspl', hlo', hrY, ?_⟩
  dsimp only
  ecancel

/-! ## SyncCommitteeMessage.Signature and Deposit_Data.WithdrawalCredentials — `nop` before `callq runtime.makeslice` -/

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
/-- `Signature` (96-byte vector): decode segment over the windows 120–129 and 134–145; receiver in rdx after makeslice, in rdx after memmove (`callq` at 140); a `nop` is inside the first window. -/
theorem sm_g4_Signature_seg (k : Nat) (hk : SmUnmarshal.IsInfixAt Host.prog k) (hf : LabelsFresh SmUnmarshal k) :
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
    (hms : MakesliceC Heap E2e.Data.e2eU8Type_addr 1 St) (hmm : MemmoveC St),
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
  have hqA := Codec.win hk 120 10
  have heA : Codec.eraseNop ((SmUnmarshal.drop 120).take 10) = Codec.bytesDecHeadR Reg64.rdx 96 "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommitteeMessage.UnmarshalSSZ_233" 112 56 64 := by rfl
  have hqB := Codec.win hk 134 12
  have heB : Codec.eraseNop ((SmUnmarshal.drop 134).take 12) = Codec.bytesDecMidR Reg64.rdx Reg64.rdx 96 "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommitteeMessage.UnmarshalSSZ_233" "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommitteeMessage.UnmarshalSSZ_274" 112 120 56 48 56 64 48 := by rfl
  have hjl : k + 134 + Codec.nopPos ((SmUnmarshal.drop 134).take 12) 0 = k + 134 := by rfl
  have hl := Machine.label_at' hk hf (j := 134)
    (by simp only [SmUnmarshal, List.getElem?_cons_succ, List.getElem?_cons_zero]; rfl)
    (by simp only [SmUnmarshal, List.take_succ_cons, List.take_zero, List.contains_cons, List.contains_nil]; decide)
  have hjm : k + 134 + Codec.nopPos ((SmUnmarshal.drop 134).take 12) 6 = k + 140 := by rfl
  have hend : k + 134 + ((SmUnmarshal.drop 134).take 12).length = k + 146 := by rfl
  with_reducible exact Codec.bytesdec_seg_window 96 (Or.inr (Or.inr rfl)) Reg64.rdx Reg64.rdx (Or.inl rfl) (Or.inr (Or.inr (Or.inl rfl))) _ _ _ _ _ _ _ _ _ _ _ (k + 120) (k + 134) (k + 134) (k + 140) (k + 146) hqA heA hqB heB hjl hl hjm hend
theorem sm_g4_Signature_seg_kind : ∀ (h : Host), type_of% (@sm_g4_Signature_seg h) = @Codec.bytesDecSegKindWindow h 96 SmUnmarshal Reg64.rdx 120 140 146 112 120 56 48 56 64 48 := by
  intro h; with_reducible rfl

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
/-- `WithdrawalCredentials` (32-byte vector): decode segment over the windows 47–56 and 61–72; receiver in rdx after makeslice, in rdx after memmove (`callq` at 67); a `nop` is inside the first window. -/
theorem dd_g4_WithdrawalCredentials_seg (k : Nat) (hk : DdUnmarshal.IsInfixAt Host.prog k) (hf : LabelsFresh DdUnmarshal k) :
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
    (hms : MakesliceC Heap E2e.Data.e2eU8Type_addr 1 St) (hmm : MemmoveC St),
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
  have hqA := Codec.win hk 47 10
  have heA : Codec.eraseNop ((DdUnmarshal.drop 47).take 10) = Codec.bytesDecHeadR Reg64.rdx 32 "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Deposit_Data.UnmarshalSSZ_113" 48 40 48 := by rfl
  have hqB := Codec.win hk 61 12
  have heB : Codec.eraseNop ((DdUnmarshal.drop 61).take 12) = Codec.bytesDecMidR Reg64.rdx Reg64.rdx 32 "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Deposit_Data.UnmarshalSSZ_113" "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Deposit_Data.UnmarshalSSZ_154" 48 56 24 32 40 48 48 := by rfl
  have hjl : k + 61 + Codec.nopPos ((DdUnmarshal.drop 61).take 12) 0 = k + 61 := by rfl
  have hl := Machine.label_at' hk hf (j := 61)
    (by simp only [DdUnmarshal, List.getElem?_cons_succ, List.getElem?_cons_zero]; rfl)
    (by simp only [DdUnmarshal, List.take_succ_cons, List.take_zero, List.contains_cons, List.contains_nil]; decide)
  have hjm : k + 61 + Codec.nopPos ((DdUnmarshal.drop 61).take 12) 6 = k + 67 := by rfl
  have hend : k + 61 + ((DdUnmarshal.drop 61).take 12).length = k + 73 := by rfl
  with_reducible exact Codec.bytesdec_seg_window 32 (Or.inl rfl) Reg64.rdx Reg64.rdx (Or.inl rfl) (Or.inr (Or.inr (Or.inl rfl))) _ _ _ _ _ _ _ _ _ _ _ (k + 47) (k + 61) (k + 61) (k + 67) (k + 73) hqA heA hqB heB hjl hl hjm hend
theorem dd_g4_WithdrawalCredentials_seg_kind : ∀ (h : Host), type_of% (@dd_g4_WithdrawalCredentials_seg h) = @Codec.bytesDecSegKindWindow h 32 DdUnmarshal Reg64.rdx 47 67 73 48 56 24 32 40 48 48 := by
  intro h; with_reducible rfl

/-! ## PendingConsolidation.TargetIndex — `nop` after the callee call (missed by the hold-out run): reload set-up as steps, call window, whole field -/

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Directive 48 `mov 0x60(%rsp),%rbx`: stepLdvKind. -/
theorem pc_g4_s48 (k : Nat) (hk : PcUnmarshal.IsInfixAt Host.prog k) (hf : LabelsFresh PcUnmarshal k) :
    ∀
    (base a v : BitVec 64) (ha : base + (96 : Int64).toBitVec = a)
    (F : DataMem → Prop)
    (final : MachineState → Prop) (s : MachineData)
    (hb : s.regs.get64 Reg64.rsp = base) (hm : (Eq ((Int.toBytes 8 v.toInt).At a) ⋆ F) s.dmem)
    (hk' : Eventually (step1 Host.exe) final ⟨Codec.setR s Reg64.rbx v, Host.addrOf (k + 49)⟩),
    Eventually (step1 Host.exe) final ⟨s, Host.addrOf (k + 48)⟩ := by
  have hq := Codec.win hk 48 1
  have he : Codec.eraseNop ((PcUnmarshal.drop 48).take 1) = [Codec.iLd Reg64.rbx Reg64.rsp 96] := by rfl
  have hend : k + 48 + ((PcUnmarshal.drop 48).take 1).length = k + 49 := by rfl
  with_reducible exact Codec.kstep_ldv Reg64.rbx Reg64.rsp 96 _ (k + 48) (k + 49) hq he hend
theorem pc_g4_s48_kind : ∀ (h : Host), type_of% (@pc_g4_s48 h) = @Codec.stepLdvKind h PcUnmarshal Reg64.rbx Reg64.rsp 96 48 49 := by
  intro h; with_reducible rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Directive 49 `add $0x8,%rbx`: stepAddKind. -/
theorem pc_g4_s49 (k : Nat) (hk : PcUnmarshal.IsInfixAt Host.prog k) (hf : LabelsFresh PcUnmarshal k) :
    ∀
    (final : MachineState → Prop) (s : MachineData)
    (hk' : ∀ fl : StatusFlags, Eventually (step1 Host.exe) final
      ⟨{ regs := s.regs.set64 Reg64.rbx (s.regs.get64 Reg64.rbx + (8 : Int64).toBitVec), zmms := s.zmms, status := fl, dmem := s.dmem },
        Host.addrOf (k + 50)⟩),
    Eventually (step1 Host.exe) final ⟨s, Host.addrOf (k + 49)⟩ := by
  have hq := Codec.win hk 49 1
  have he : Codec.eraseNop ((PcUnmarshal.drop 49).take 1) = [Codec.iAdd Reg64.rbx 8] := by rfl
  have hend : k + 49 + ((PcUnmarshal.drop 49).take 1).length = k + 50 := by rfl
  with_reducible exact Codec.kstep_add Reg64.rbx 8 _ (k + 49) (k + 50) hq he hend
theorem pc_g4_s49_kind : ∀ (h : Host), type_of% (@pc_g4_s49 h) = @Codec.stepAddKind h PcUnmarshal Reg64.rbx 8 49 50 := by
  intro h; with_reducible rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Directive 50 `mov 0x70(%rsp),%rdi`: stepLdbKind. -/
theorem pc_g4_s50 (k : Nat) (hk : PcUnmarshal.IsInfixAt Host.prog k) (hf : LabelsFresh PcUnmarshal k) :
    ∀
    (base a : BitVec 64) (ha : base + (112 : Int64).toBitVec = a) (bs : List UInt8) (hbs : bs.length = 8)
    (F : DataMem → Prop)
    (final : MachineState → Prop) (s : MachineData)
    (hb : s.regs.get64 Reg64.rsp = base) (hm : (Eq (bs.At a) ⋆ F) s.dmem)
    (hk' : Eventually (step1 Host.exe) final ⟨Codec.setR s Reg64.rdi (BitVec.ofInt 64 (Int.ofBytes bs)), Host.addrOf (k + 51)⟩),
    Eventually (step1 Host.exe) final ⟨s, Host.addrOf (k + 50)⟩ := by
  have hq := Codec.win hk 50 1
  have he : Codec.eraseNop ((PcUnmarshal.drop 50).take 1) = [Codec.iLd Reg64.rdi Reg64.rsp 112] := by rfl
  have hend : k + 50 + ((PcUnmarshal.drop 50).take 1).length = k + 51 := by rfl
  with_reducible exact Codec.kstep_ldb Reg64.rdi Reg64.rsp 112 _ (k + 50) (k + 51) hq he hend
theorem pc_g4_s50_kind : ∀ (h : Host), type_of% (@pc_g4_s50 h) = @Codec.stepLdbKind h PcUnmarshal Reg64.rdi Reg64.rsp 112 50 51 := by
  intro h; with_reducible rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Directive 51 `add $-0x8,%rdi`: stepAddKind. -/
theorem pc_g4_s51 (k : Nat) (hk : PcUnmarshal.IsInfixAt Host.prog k) (hf : LabelsFresh PcUnmarshal k) :
    ∀
    (final : MachineState → Prop) (s : MachineData)
    (hk' : ∀ fl : StatusFlags, Eventually (step1 Host.exe) final
      ⟨{ regs := s.regs.set64 Reg64.rdi (s.regs.get64 Reg64.rdi + ((-8) : Int64).toBitVec), zmms := s.zmms, status := fl, dmem := s.dmem },
        Host.addrOf (k + 52)⟩),
    Eventually (step1 Host.exe) final ⟨s, Host.addrOf (k + 51)⟩ := by
  have hq := Codec.win hk 51 1
  have he : Codec.eraseNop ((PcUnmarshal.drop 51).take 1) = [Codec.iAdd Reg64.rdi (-8)] := by rfl
  have hend : k + 51 + ((PcUnmarshal.drop 51).take 1).length = k + 52 := by rfl
  with_reducible exact Codec.kstep_add Reg64.rdi (-8) _ (k + 51) (k + 52) hq he hend
theorem pc_g4_s51_kind : ∀ (h : Host), type_of% (@pc_g4_s51 h) = @Codec.stepAddKind h PcUnmarshal Reg64.rdi (-8) 51 52 := by
  intro h; with_reducible rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Directive 52 `mov 0x58(%rsp),%rax`: stepLdvKind. -/
theorem pc_g4_s52 (k : Nat) (hk : PcUnmarshal.IsInfixAt Host.prog k) (hf : LabelsFresh PcUnmarshal k) :
    ∀
    (base a v : BitVec 64) (ha : base + (88 : Int64).toBitVec = a)
    (F : DataMem → Prop)
    (final : MachineState → Prop) (s : MachineData)
    (hb : s.regs.get64 Reg64.rsp = base) (hm : (Eq ((Int.toBytes 8 v.toInt).At a) ⋆ F) s.dmem)
    (hk' : Eventually (step1 Host.exe) final ⟨Codec.setR s Reg64.rax v, Host.addrOf (k + 53)⟩),
    Eventually (step1 Host.exe) final ⟨s, Host.addrOf (k + 52)⟩ := by
  have hq := Codec.win hk 52 1
  have he : Codec.eraseNop ((PcUnmarshal.drop 52).take 1) = [Codec.iLd Reg64.rax Reg64.rsp 88] := by rfl
  have hend : k + 52 + ((PcUnmarshal.drop 52).take 1).length = k + 53 := by rfl
  with_reducible exact Codec.kstep_ldv Reg64.rax Reg64.rsp 88 _ (k + 52) (k + 53) hq he hend
theorem pc_g4_s52_kind : ∀ (h : Host), type_of% (@pc_g4_s52 h) = @Codec.stepLdvKind h PcUnmarshal Reg64.rax Reg64.rsp 88 52 53 := by
  intro h; with_reducible rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Directive 53 `add $0x10,%rax`: stepAddKind. -/
theorem pc_g4_s53 (k : Nat) (hk : PcUnmarshal.IsInfixAt Host.prog k) (hf : LabelsFresh PcUnmarshal k) :
    ∀
    (final : MachineState → Prop) (s : MachineData)
    (hk' : ∀ fl : StatusFlags, Eventually (step1 Host.exe) final
      ⟨{ regs := s.regs.set64 Reg64.rax (s.regs.get64 Reg64.rax + (16 : Int64).toBitVec), zmms := s.zmms, status := fl, dmem := s.dmem },
        Host.addrOf (k + 54)⟩),
    Eventually (step1 Host.exe) final ⟨s, Host.addrOf (k + 53)⟩ := by
  have hq := Codec.win hk 53 1
  have he : Codec.eraseNop ((PcUnmarshal.drop 53).take 1) = [Codec.iAdd Reg64.rax 16] := by rfl
  have hend : k + 53 + ((PcUnmarshal.drop 53).take 1).length = k + 54 := by rfl
  with_reducible exact Codec.kstep_add Reg64.rax 16 _ (k + 53) (k + 54) hq he hend
theorem pc_g4_s53_kind : ∀ (h : Host), type_of% (@pc_g4_s53 h) = @Codec.stepAddKind h PcUnmarshal Reg64.rax 16 53 54 := by
  intro h; with_reducible rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Directive 54 `mov $0x8,%ecx`: stepMovIKind. -/
theorem pc_g4_s54 (k : Nat) (hk : PcUnmarshal.IsInfixAt Host.prog k) (hf : LabelsFresh PcUnmarshal k) :
    ∀
    (final : MachineState → Prop) (s : MachineData)
    (hk' : Eventually (step1 Host.exe) final ⟨Codec.setR s Reg64.rcx (BitVec.zeroExtend 64 (BitVec.truncate 32 (8 : Int64).toBitVec)), Host.addrOf (k + 55)⟩),
    Eventually (step1 Host.exe) final ⟨s, Host.addrOf (k + 54)⟩ := by
  have hq := Codec.win hk 54 1
  have he : Codec.eraseNop ((PcUnmarshal.drop 54).take 1) = [Codec.iMovI Reg64.rcx 8] := by rfl
  have hend : k + 54 + ((PcUnmarshal.drop 54).take 1).length = k + 55 := by rfl
  with_reducible exact Codec.kstep_movi Reg64.rcx 8 _ (k + 54) (k + 55) hq he hend
theorem pc_g4_s54_kind : ∀ (h : Host), type_of% (@pc_g4_s54 h) = @Codec.stepMovIKind h PcUnmarshal Reg64.rcx 8 54 55 := by
  intro h; with_reducible rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- `TargetIndex`: call block over the window 55–58 (`callq; nop; test; je`), `callq` at 55, continuation label at 85. -/
theorem pc_g4_TargetIndex_call (k : Nat) (hk : PcUnmarshal.IsInfixAt Host.prog k) (hf : LabelsFresh PcUnmarshal k) :
    ∀ (hC : U64CalleeAcc "github.com_OffchainLabs_prysm_v7_consensus_types_primitives.ValidatorIndex.UnmarshalSSZ")
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
  have hq := Codec.win hk 55 4
  have he : Codec.eraseNop ((PcUnmarshal.drop 55).take 4) = E2eScal.callDec "github.com_OffchainLabs_prysm_v7_consensus_types_primitives.ValidatorIndex.UnmarshalSSZ" "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingConsolidation.UnmarshalSSZ_14d" := by rfl
  have hjc : k + 55 + Codec.nopPos ((PcUnmarshal.drop 55).take 4) 0 = k + 55 := by rfl
  have hB := Codec.infix_sub (q := E2eScal.callDecL "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingConsolidation.UnmarshalSSZ_14d") 85 hk
    (by simp only [PcUnmarshal, E2eScal.callDecL, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero])
  have hl := Machine.label_at' hk hf (j := 85)
    (by simp only [PcUnmarshal, List.getElem?_cons_succ, List.getElem?_cons_zero]; rfl)
    (by simp only [PcUnmarshal, List.take_succ_cons, List.take_zero, List.contains_cons, List.contains_nil]; decide)
  with_reducible exact E2eScal.calldec_seg_w _ _ _ (k + 55) (k + 55) (k + 85) hq he hjc hB hl
theorem pc_g4_TargetIndex_call_kind : ∀ (h : Host), type_of% (@pc_g4_TargetIndex_call h) = @E2eScal.callDecSegKindG4 h PcUnmarshal "github.com_OffchainLabs_prysm_v7_consensus_types_primitives.ValidatorIndex.UnmarshalSSZ" "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingConsolidation.UnmarshalSSZ_14d" 55 55 85 := by
  intro h; with_reducible rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- `TargetIndex` (callee decoder field, Go offset 16, SSZ offset 8): the WHOLE call field 48–85, composed from the
step theorems of its set-up and the call-block theorem (worked example of the `p2dec --gen4` emission recipe). The entry
conditions of the call block (rax = `rcv + 16`, rbx = `bf + 8`, rcx = 8) are closed by `rfl` on the state
that the steps computed. -/
theorem pc_g4_TargetIndex_field (k : Nat) (hk : PcUnmarshal.IsInfixAt Host.prog k) (hf : LabelsFresh PcUnmarshal k) :
    ∀ (hC : U64CalleeAcc "github.com_OffchainLabs_prysm_v7_consensus_types_primitives.ValidatorIndex.UnmarshalSSZ")
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
  apply pc_g4_s48 k hk hf sp aB bf hB _ _ _ (by rfl) (by ecancel)
  kn
  apply pc_g4_s49 k hk hf
  intro fl1; kn
  apply pc_g4_s50 k hk hf sp aD hD vD hvD _ _ _ (by rfl) (by ecancel)
  kn
  apply pc_g4_s51 k hk hf
  intro fl2; kn
  apply pc_g4_s52 k hk hf sp aR rcv hR _ _ _ (by rfl) (by ecancel)
  kn
  apply pc_g4_s53 k hk hf
  intro fl3; kn
  apply pc_g4_s54 k hk hf
  kn
  refine eventually_trans _ _ _ _ (pc_g4_TargetIndex_call k hk hf hC sp (rcv + 16) (bf + 8) aRet aFp aS2 hRet hFp hS2 rbp0 r140 guard e8 rslot
    fp s2 c0 he8 hrs hfp hs2 hc0 hguard _ _ (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by first | rfl | decide)
    (by ecancel)) ?_
  rintro ⟨d, pc⟩ ⟨hpc, hrax', hrbx', hrsp', hrbp', hr14', Hm⟩
  dsimp only at hpc hrax' hrbx' hrsp' hrbp' hr14' Hm
  apply Eventually.done
  refine ⟨hpc, hrax', hrbx', hrsp', hrbp', hr14', ?_⟩
  dsimp only
  ecancel

/-! ## `p2dec --gen3` set-up forms as steps: first-field form with pad (Checkpoint.Epoch), reload form with pad (BeaconBlockHeader.ProposerIndex), `lea` form with the interleaved uint64 read (PendingPartialWithdrawal.WithdrawableEpoch) -/

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Directive 14 `add $0x8,%rax`: stepAddKind. -/
theorem cp_g4_s14 (k : Nat) (hk : CpUnmarshal.IsInfixAt Host.prog k) (hf : LabelsFresh CpUnmarshal k) :
    ∀
    (final : MachineState → Prop) (s : MachineData)
    (hk' : ∀ fl : StatusFlags, Eventually (step1 Host.exe) final
      ⟨{ regs := s.regs.set64 Reg64.rax (s.regs.get64 Reg64.rax + (8 : Int64).toBitVec), zmms := s.zmms, status := fl, dmem := s.dmem },
        Host.addrOf (k + 15)⟩),
    Eventually (step1 Host.exe) final ⟨s, Host.addrOf (k + 14)⟩ := by
  have hq := Codec.win hk 14 1
  have he : Codec.eraseNop ((CpUnmarshal.drop 14).take 1) = [Codec.iAdd Reg64.rax 8] := by rfl
  have hend : k + 14 + ((CpUnmarshal.drop 14).take 1).length = k + 15 := by rfl
  with_reducible exact Codec.kstep_add Reg64.rax 8 _ (k + 14) (k + 15) hq he hend
theorem cp_g4_s14_kind : ∀ (h : Host), type_of% (@cp_g4_s14 h) = @Codec.stepAddKind h CpUnmarshal Reg64.rax 8 14 15 := by
  intro h; with_reducible rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Directive 15 `mov $0x8,%ecx`: stepMovIKind. -/
theorem cp_g4_s15 (k : Nat) (hk : CpUnmarshal.IsInfixAt Host.prog k) (hf : LabelsFresh CpUnmarshal k) :
    ∀
    (final : MachineState → Prop) (s : MachineData)
    (hk' : Eventually (step1 Host.exe) final ⟨Codec.setR s Reg64.rcx (BitVec.zeroExtend 64 (BitVec.truncate 32 (8 : Int64).toBitVec)), Host.addrOf (k + 16)⟩),
    Eventually (step1 Host.exe) final ⟨s, Host.addrOf (k + 15)⟩ := by
  have hq := Codec.win hk 15 1
  have he : Codec.eraseNop ((CpUnmarshal.drop 15).take 1) = [Codec.iMovI Reg64.rcx 8] := by rfl
  have hend : k + 15 + ((CpUnmarshal.drop 15).take 1).length = k + 16 := by rfl
  with_reducible exact Codec.kstep_movi Reg64.rcx 8 _ (k + 15) (k + 16) hq he hend
theorem cp_g4_s15_kind : ∀ (h : Host), type_of% (@cp_g4_s15 h) = @Codec.stepMovIKind h CpUnmarshal Reg64.rcx 8 15 16 := by
  intro h; with_reducible rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- `Epoch`: call block over the window 16–19 (`nop; callq; test; je`), `callq` at 17, continuation label at 47. -/
theorem cp_g4_Epoch_call (k : Nat) (hk : CpUnmarshal.IsInfixAt Host.prog k) (hf : LabelsFresh CpUnmarshal k) :
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
      ⟨s, Host.addrOf (k + 16)⟩ := by
  have hq := Codec.win hk 16 4
  have he : Codec.eraseNop ((CpUnmarshal.drop 16).take 4) = E2eScal.callDec "github.com_OffchainLabs_prysm_v7_consensus_types_primitives.Epoch.UnmarshalSSZ" "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Checkpoint.UnmarshalSSZ_b4" := by rfl
  have hjc : k + 16 + Codec.nopPos ((CpUnmarshal.drop 16).take 4) 0 = k + 17 := by rfl
  have hB := Codec.infix_sub (q := E2eScal.callDecL "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Checkpoint.UnmarshalSSZ_b4") 47 hk
    (by simp only [CpUnmarshal, E2eScal.callDecL, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero])
  have hl := Machine.label_at' hk hf (j := 47)
    (by simp only [CpUnmarshal, List.getElem?_cons_succ, List.getElem?_cons_zero]; rfl)
    (by simp only [CpUnmarshal, List.take_succ_cons, List.take_zero, List.contains_cons, List.contains_nil]; decide)
  with_reducible exact E2eScal.calldec_seg_w _ _ _ (k + 16) (k + 17) (k + 47) hq he hjc hB hl
theorem cp_g4_Epoch_call_kind : ∀ (h : Host), type_of% (@cp_g4_Epoch_call h) = @E2eScal.callDecSegKindG4 h CpUnmarshal "github.com_OffchainLabs_prysm_v7_consensus_types_primitives.Epoch.UnmarshalSSZ" "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Checkpoint.UnmarshalSSZ_b4" 16 17 47 := by
  intro h; with_reducible rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Directive 47 `mov 0x78(%rsp),%rbx`: stepLdvKind. -/
theorem bh_g4_s47 (k : Nat) (hk : BhUnmarshal.IsInfixAt Host.prog k) (hf : LabelsFresh BhUnmarshal k) :
    ∀
    (base a v : BitVec 64) (ha : base + (120 : Int64).toBitVec = a)
    (F : DataMem → Prop)
    (final : MachineState → Prop) (s : MachineData)
    (hb : s.regs.get64 Reg64.rsp = base) (hm : (Eq ((Int.toBytes 8 v.toInt).At a) ⋆ F) s.dmem)
    (hk' : Eventually (step1 Host.exe) final ⟨Codec.setR s Reg64.rbx v, Host.addrOf (k + 48)⟩),
    Eventually (step1 Host.exe) final ⟨s, Host.addrOf (k + 47)⟩ := by
  have hq := Codec.win hk 47 1
  have he : Codec.eraseNop ((BhUnmarshal.drop 47).take 1) = [Codec.iLd Reg64.rbx Reg64.rsp 120] := by rfl
  have hend : k + 47 + ((BhUnmarshal.drop 47).take 1).length = k + 48 := by rfl
  with_reducible exact Codec.kstep_ldv Reg64.rbx Reg64.rsp 120 _ (k + 47) (k + 48) hq he hend
theorem bh_g4_s47_kind : ∀ (h : Host), type_of% (@bh_g4_s47 h) = @Codec.stepLdvKind h BhUnmarshal Reg64.rbx Reg64.rsp 120 47 48 := by
  intro h; with_reducible rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Directive 48 `add $0x8,%rbx`: stepAddKind. -/
theorem bh_g4_s48 (k : Nat) (hk : BhUnmarshal.IsInfixAt Host.prog k) (hf : LabelsFresh BhUnmarshal k) :
    ∀
    (final : MachineState → Prop) (s : MachineData)
    (hk' : ∀ fl : StatusFlags, Eventually (step1 Host.exe) final
      ⟨{ regs := s.regs.set64 Reg64.rbx (s.regs.get64 Reg64.rbx + (8 : Int64).toBitVec), zmms := s.zmms, status := fl, dmem := s.dmem },
        Host.addrOf (k + 49)⟩),
    Eventually (step1 Host.exe) final ⟨s, Host.addrOf (k + 48)⟩ := by
  have hq := Codec.win hk 48 1
  have he : Codec.eraseNop ((BhUnmarshal.drop 48).take 1) = [Codec.iAdd Reg64.rbx 8] := by rfl
  have hend : k + 48 + ((BhUnmarshal.drop 48).take 1).length = k + 49 := by rfl
  with_reducible exact Codec.kstep_add Reg64.rbx 8 _ (k + 48) (k + 49) hq he hend
theorem bh_g4_s48_kind : ∀ (h : Host), type_of% (@bh_g4_s48 h) = @Codec.stepAddKind h BhUnmarshal Reg64.rbx 8 48 49 := by
  intro h; with_reducible rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Directive 49 `mov 0x88(%rsp),%rdi`: stepLdbKind. -/
theorem bh_g4_s49 (k : Nat) (hk : BhUnmarshal.IsInfixAt Host.prog k) (hf : LabelsFresh BhUnmarshal k) :
    ∀
    (base a : BitVec 64) (ha : base + (136 : Int64).toBitVec = a) (bs : List UInt8) (hbs : bs.length = 8)
    (F : DataMem → Prop)
    (final : MachineState → Prop) (s : MachineData)
    (hb : s.regs.get64 Reg64.rsp = base) (hm : (Eq (bs.At a) ⋆ F) s.dmem)
    (hk' : Eventually (step1 Host.exe) final ⟨Codec.setR s Reg64.rdi (BitVec.ofInt 64 (Int.ofBytes bs)), Host.addrOf (k + 50)⟩),
    Eventually (step1 Host.exe) final ⟨s, Host.addrOf (k + 49)⟩ := by
  have hq := Codec.win hk 49 1
  have he : Codec.eraseNop ((BhUnmarshal.drop 49).take 1) = [Codec.iLd Reg64.rdi Reg64.rsp 136] := by rfl
  have hend : k + 49 + ((BhUnmarshal.drop 49).take 1).length = k + 50 := by rfl
  with_reducible exact Codec.kstep_ldb Reg64.rdi Reg64.rsp 136 _ (k + 49) (k + 50) hq he hend
theorem bh_g4_s49_kind : ∀ (h : Host), type_of% (@bh_g4_s49 h) = @Codec.stepLdbKind h BhUnmarshal Reg64.rdi Reg64.rsp 136 49 50 := by
  intro h; with_reducible rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Directive 50 `add $-0x8,%rdi`: stepAddKind. -/
theorem bh_g4_s50 (k : Nat) (hk : BhUnmarshal.IsInfixAt Host.prog k) (hf : LabelsFresh BhUnmarshal k) :
    ∀
    (final : MachineState → Prop) (s : MachineData)
    (hk' : ∀ fl : StatusFlags, Eventually (step1 Host.exe) final
      ⟨{ regs := s.regs.set64 Reg64.rdi (s.regs.get64 Reg64.rdi + ((-8) : Int64).toBitVec), zmms := s.zmms, status := fl, dmem := s.dmem },
        Host.addrOf (k + 51)⟩),
    Eventually (step1 Host.exe) final ⟨s, Host.addrOf (k + 50)⟩ := by
  have hq := Codec.win hk 50 1
  have he : Codec.eraseNop ((BhUnmarshal.drop 50).take 1) = [Codec.iAdd Reg64.rdi (-8)] := by rfl
  have hend : k + 50 + ((BhUnmarshal.drop 50).take 1).length = k + 51 := by rfl
  with_reducible exact Codec.kstep_add Reg64.rdi (-8) _ (k + 50) (k + 51) hq he hend
theorem bh_g4_s50_kind : ∀ (h : Host), type_of% (@bh_g4_s50 h) = @Codec.stepAddKind h BhUnmarshal Reg64.rdi (-8) 50 51 := by
  intro h; with_reducible rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Directive 51 `mov 0x70(%rsp),%rax`: stepLdvKind. -/
theorem bh_g4_s51 (k : Nat) (hk : BhUnmarshal.IsInfixAt Host.prog k) (hf : LabelsFresh BhUnmarshal k) :
    ∀
    (base a v : BitVec 64) (ha : base + (112 : Int64).toBitVec = a)
    (F : DataMem → Prop)
    (final : MachineState → Prop) (s : MachineData)
    (hb : s.regs.get64 Reg64.rsp = base) (hm : (Eq ((Int.toBytes 8 v.toInt).At a) ⋆ F) s.dmem)
    (hk' : Eventually (step1 Host.exe) final ⟨Codec.setR s Reg64.rax v, Host.addrOf (k + 52)⟩),
    Eventually (step1 Host.exe) final ⟨s, Host.addrOf (k + 51)⟩ := by
  have hq := Codec.win hk 51 1
  have he : Codec.eraseNop ((BhUnmarshal.drop 51).take 1) = [Codec.iLd Reg64.rax Reg64.rsp 112] := by rfl
  have hend : k + 51 + ((BhUnmarshal.drop 51).take 1).length = k + 52 := by rfl
  with_reducible exact Codec.kstep_ldv Reg64.rax Reg64.rsp 112 _ (k + 51) (k + 52) hq he hend
theorem bh_g4_s51_kind : ∀ (h : Host), type_of% (@bh_g4_s51 h) = @Codec.stepLdvKind h BhUnmarshal Reg64.rax Reg64.rsp 112 51 52 := by
  intro h; with_reducible rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Directive 52 `add $0x10,%rax`: stepAddKind. -/
theorem bh_g4_s52 (k : Nat) (hk : BhUnmarshal.IsInfixAt Host.prog k) (hf : LabelsFresh BhUnmarshal k) :
    ∀
    (final : MachineState → Prop) (s : MachineData)
    (hk' : ∀ fl : StatusFlags, Eventually (step1 Host.exe) final
      ⟨{ regs := s.regs.set64 Reg64.rax (s.regs.get64 Reg64.rax + (16 : Int64).toBitVec), zmms := s.zmms, status := fl, dmem := s.dmem },
        Host.addrOf (k + 53)⟩),
    Eventually (step1 Host.exe) final ⟨s, Host.addrOf (k + 52)⟩ := by
  have hq := Codec.win hk 52 1
  have he : Codec.eraseNop ((BhUnmarshal.drop 52).take 1) = [Codec.iAdd Reg64.rax 16] := by rfl
  have hend : k + 52 + ((BhUnmarshal.drop 52).take 1).length = k + 53 := by rfl
  with_reducible exact Codec.kstep_add Reg64.rax 16 _ (k + 52) (k + 53) hq he hend
theorem bh_g4_s52_kind : ∀ (h : Host), type_of% (@bh_g4_s52 h) = @Codec.stepAddKind h BhUnmarshal Reg64.rax 16 52 53 := by
  intro h; with_reducible rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Directive 53 `mov $0x8,%ecx`: stepMovIKind. -/
theorem bh_g4_s53 (k : Nat) (hk : BhUnmarshal.IsInfixAt Host.prog k) (hf : LabelsFresh BhUnmarshal k) :
    ∀
    (final : MachineState → Prop) (s : MachineData)
    (hk' : Eventually (step1 Host.exe) final ⟨Codec.setR s Reg64.rcx (BitVec.zeroExtend 64 (BitVec.truncate 32 (8 : Int64).toBitVec)), Host.addrOf (k + 54)⟩),
    Eventually (step1 Host.exe) final ⟨s, Host.addrOf (k + 53)⟩ := by
  have hq := Codec.win hk 53 1
  have he : Codec.eraseNop ((BhUnmarshal.drop 53).take 1) = [Codec.iMovI Reg64.rcx 8] := by rfl
  have hend : k + 53 + ((BhUnmarshal.drop 53).take 1).length = k + 54 := by rfl
  with_reducible exact Codec.kstep_movi Reg64.rcx 8 _ (k + 53) (k + 54) hq he hend
theorem bh_g4_s53_kind : ∀ (h : Host), type_of% (@bh_g4_s53 h) = @Codec.stepMovIKind h BhUnmarshal Reg64.rcx 8 53 54 := by
  intro h; with_reducible rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- `ProposerIndex`: call block over the window 54–57 (`nop; callq; test; je`), `callq` at 55, continuation label at 85. -/
theorem bh_g4_ProposerIndex_call (k : Nat) (hk : BhUnmarshal.IsInfixAt Host.prog k) (hf : LabelsFresh BhUnmarshal k) :
    ∀ (hC : U64CalleeAcc "github.com_OffchainLabs_prysm_v7_consensus_types_primitives.ValidatorIndex.UnmarshalSSZ")
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
  have hq := Codec.win hk 54 4
  have he : Codec.eraseNop ((BhUnmarshal.drop 54).take 4) = E2eScal.callDec "github.com_OffchainLabs_prysm_v7_consensus_types_primitives.ValidatorIndex.UnmarshalSSZ" "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockHeader.UnmarshalSSZ_154" := by rfl
  have hjc : k + 54 + Codec.nopPos ((BhUnmarshal.drop 54).take 4) 0 = k + 55 := by rfl
  have hB := Codec.infix_sub (q := E2eScal.callDecL "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockHeader.UnmarshalSSZ_154") 85 hk
    (by simp only [BhUnmarshal, E2eScal.callDecL, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero])
  have hl := Machine.label_at' hk hf (j := 85)
    (by simp only [BhUnmarshal, List.getElem?_cons_succ, List.getElem?_cons_zero]; rfl)
    (by simp only [BhUnmarshal, List.take_succ_cons, List.take_zero, List.contains_cons, List.contains_nil]; decide)
  with_reducible exact E2eScal.calldec_seg_w _ _ _ (k + 54) (k + 55) (k + 85) hq he hjc hB hl
theorem bh_g4_ProposerIndex_call_kind : ∀ (h : Host), type_of% (@bh_g4_ProposerIndex_call h) = @E2eScal.callDecSegKindG4 h BhUnmarshal "github.com_OffchainLabs_prysm_v7_consensus_types_primitives.ValidatorIndex.UnmarshalSSZ" "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockHeader.UnmarshalSSZ_154" 54 55 85 := by
  intro h; with_reducible rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Directive 48 `mov 0x60(%rsp),%rbx`: stepLdvKind. -/
theorem pw_g4_s48 (k : Nat) (hk : PwUnmarshal.IsInfixAt Host.prog k) (hf : LabelsFresh PwUnmarshal k) :
    ∀
    (base a v : BitVec 64) (ha : base + (96 : Int64).toBitVec = a)
    (F : DataMem → Prop)
    (final : MachineState → Prop) (s : MachineData)
    (hb : s.regs.get64 Reg64.rsp = base) (hm : (Eq ((Int.toBytes 8 v.toInt).At a) ⋆ F) s.dmem)
    (hk' : Eventually (step1 Host.exe) final ⟨Codec.setR s Reg64.rbx v, Host.addrOf (k + 49)⟩),
    Eventually (step1 Host.exe) final ⟨s, Host.addrOf (k + 48)⟩ := by
  have hq := Codec.win hk 48 1
  have he : Codec.eraseNop ((PwUnmarshal.drop 48).take 1) = [Codec.iLd Reg64.rbx Reg64.rsp 96] := by rfl
  have hend : k + 48 + ((PwUnmarshal.drop 48).take 1).length = k + 49 := by rfl
  with_reducible exact Codec.kstep_ldv Reg64.rbx Reg64.rsp 96 _ (k + 48) (k + 49) hq he hend
theorem pw_g4_s48_kind : ∀ (h : Host), type_of% (@pw_g4_s48 h) = @Codec.stepLdvKind h PwUnmarshal Reg64.rbx Reg64.rsp 96 48 49 := by
  intro h; with_reducible rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Directive 49 `lea 0x10(%rbx),%rdx`: stepLeaKind. -/
theorem pw_g4_s49 (k : Nat) (hk : PwUnmarshal.IsInfixAt Host.prog k) (hf : LabelsFresh PwUnmarshal k) :
    ∀
    (final : MachineState → Prop) (s : MachineData)
    (hk' : Eventually (step1 Host.exe) final ⟨Codec.setR s Reg64.rdx (s.regs.get64 Reg64.rbx + (16 : Int64).toBitVec), Host.addrOf (k + 50)⟩),
    Eventually (step1 Host.exe) final ⟨s, Host.addrOf (k + 49)⟩ := by
  have hq := Codec.win hk 49 1
  have he : Codec.eraseNop ((PwUnmarshal.drop 49).take 1) = [Codec.iLea Reg64.rdx Reg64.rbx 16] := by rfl
  have hend : k + 49 + ((PwUnmarshal.drop 49).take 1).length = k + 50 := by rfl
  with_reducible exact Codec.kstep_lea Reg64.rdx Reg64.rbx 16 _ (k + 49) (k + 50) hq he hend
theorem pw_g4_s49_kind : ∀ (h : Host), type_of% (@pw_g4_s49 h) = @Codec.stepLeaKind h PwUnmarshal Reg64.rdx Reg64.rbx 16 49 50 := by
  intro h; with_reducible rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Directive 50 `mov 0x70(%rsp),%rdi`: stepLdbKind. -/
theorem pw_g4_s50 (k : Nat) (hk : PwUnmarshal.IsInfixAt Host.prog k) (hf : LabelsFresh PwUnmarshal k) :
    ∀
    (base a : BitVec 64) (ha : base + (112 : Int64).toBitVec = a) (bs : List UInt8) (hbs : bs.length = 8)
    (F : DataMem → Prop)
    (final : MachineState → Prop) (s : MachineData)
    (hb : s.regs.get64 Reg64.rsp = base) (hm : (Eq (bs.At a) ⋆ F) s.dmem)
    (hk' : Eventually (step1 Host.exe) final ⟨Codec.setR s Reg64.rdi (BitVec.ofInt 64 (Int.ofBytes bs)), Host.addrOf (k + 51)⟩),
    Eventually (step1 Host.exe) final ⟨s, Host.addrOf (k + 50)⟩ := by
  have hq := Codec.win hk 50 1
  have he : Codec.eraseNop ((PwUnmarshal.drop 50).take 1) = [Codec.iLd Reg64.rdi Reg64.rsp 112] := by rfl
  have hend : k + 50 + ((PwUnmarshal.drop 50).take 1).length = k + 51 := by rfl
  with_reducible exact Codec.kstep_ldb Reg64.rdi Reg64.rsp 112 _ (k + 50) (k + 51) hq he hend
theorem pw_g4_s50_kind : ∀ (h : Host), type_of% (@pw_g4_s50 h) = @Codec.stepLdbKind h PwUnmarshal Reg64.rdi Reg64.rsp 112 50 51 := by
  intro h; with_reducible rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Directive 51 `add $-0x10,%rdi`: stepAddKind. -/
theorem pw_g4_s51 (k : Nat) (hk : PwUnmarshal.IsInfixAt Host.prog k) (hf : LabelsFresh PwUnmarshal k) :
    ∀
    (final : MachineState → Prop) (s : MachineData)
    (hk' : ∀ fl : StatusFlags, Eventually (step1 Host.exe) final
      ⟨{ regs := s.regs.set64 Reg64.rdi (s.regs.get64 Reg64.rdi + ((-16) : Int64).toBitVec), zmms := s.zmms, status := fl, dmem := s.dmem },
        Host.addrOf (k + 52)⟩),
    Eventually (step1 Host.exe) final ⟨s, Host.addrOf (k + 51)⟩ := by
  have hq := Codec.win hk 51 1
  have he : Codec.eraseNop ((PwUnmarshal.drop 51).take 1) = [Codec.iAdd Reg64.rdi (-16)] := by rfl
  have hend : k + 51 + ((PwUnmarshal.drop 51).take 1).length = k + 52 := by rfl
  with_reducible exact Codec.kstep_add Reg64.rdi (-16) _ (k + 51) (k + 52) hq he hend
theorem pw_g4_s51_kind : ∀ (h : Host), type_of% (@pw_g4_s51 h) = @Codec.stepAddKind h PwUnmarshal Reg64.rdi (-16) 51 52 := by
  intro h; with_reducible rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Directive 52 `mov 0x58(%rsp),%rax`: stepLdvKind. -/
theorem pw_g4_s52 (k : Nat) (hk : PwUnmarshal.IsInfixAt Host.prog k) (hf : LabelsFresh PwUnmarshal k) :
    ∀
    (base a v : BitVec 64) (ha : base + (88 : Int64).toBitVec = a)
    (F : DataMem → Prop)
    (final : MachineState → Prop) (s : MachineData)
    (hb : s.regs.get64 Reg64.rsp = base) (hm : (Eq ((Int.toBytes 8 v.toInt).At a) ⋆ F) s.dmem)
    (hk' : Eventually (step1 Host.exe) final ⟨Codec.setR s Reg64.rax v, Host.addrOf (k + 53)⟩),
    Eventually (step1 Host.exe) final ⟨s, Host.addrOf (k + 52)⟩ := by
  have hq := Codec.win hk 52 1
  have he : Codec.eraseNop ((PwUnmarshal.drop 52).take 1) = [Codec.iLd Reg64.rax Reg64.rsp 88] := by rfl
  have hend : k + 52 + ((PwUnmarshal.drop 52).take 1).length = k + 53 := by rfl
  with_reducible exact Codec.kstep_ldv Reg64.rax Reg64.rsp 88 _ (k + 52) (k + 53) hq he hend
theorem pw_g4_s52_kind : ∀ (h : Host), type_of% (@pw_g4_s52 h) = @Codec.stepLdvKind h PwUnmarshal Reg64.rax Reg64.rsp 88 52 53 := by
  intro h; with_reducible rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Directive 53 `lea 0x18(%rax),%rsi`: stepLeaKind. -/
theorem pw_g4_s53 (k : Nat) (hk : PwUnmarshal.IsInfixAt Host.prog k) (hf : LabelsFresh PwUnmarshal k) :
    ∀
    (final : MachineState → Prop) (s : MachineData)
    (hk' : Eventually (step1 Host.exe) final ⟨Codec.setR s Reg64.rsi (s.regs.get64 Reg64.rax + (24 : Int64).toBitVec), Host.addrOf (k + 54)⟩),
    Eventually (step1 Host.exe) final ⟨s, Host.addrOf (k + 53)⟩ := by
  have hq := Codec.win hk 53 1
  have he : Codec.eraseNop ((PwUnmarshal.drop 53).take 1) = [Codec.iLea Reg64.rsi Reg64.rax 24] := by rfl
  have hend : k + 53 + ((PwUnmarshal.drop 53).take 1).length = k + 54 := by rfl
  with_reducible exact Codec.kstep_lea Reg64.rsi Reg64.rax 24 _ (k + 53) (k + 54) hq he hend
theorem pw_g4_s53_kind : ∀ (h : Host), type_of% (@pw_g4_s53 h) = @Codec.stepLeaKind h PwUnmarshal Reg64.rsi Reg64.rax 24 53 54 := by
  intro h; with_reducible rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Directive 54 `mov 0x8(%rbx),%r8`: stepLdbKind. -/
theorem pw_g4_s54 (k : Nat) (hk : PwUnmarshal.IsInfixAt Host.prog k) (hf : LabelsFresh PwUnmarshal k) :
    ∀
    (base a : BitVec 64) (ha : base + (8 : Int64).toBitVec = a) (bs : List UInt8) (hbs : bs.length = 8)
    (F : DataMem → Prop)
    (final : MachineState → Prop) (s : MachineData)
    (hb : s.regs.get64 Reg64.rbx = base) (hm : (Eq (bs.At a) ⋆ F) s.dmem)
    (hk' : Eventually (step1 Host.exe) final ⟨Codec.setR s Reg64.r8 (BitVec.ofInt 64 (Int.ofBytes bs)), Host.addrOf (k + 55)⟩),
    Eventually (step1 Host.exe) final ⟨s, Host.addrOf (k + 54)⟩ := by
  have hq := Codec.win hk 54 1
  have he : Codec.eraseNop ((PwUnmarshal.drop 54).take 1) = [Codec.iLd Reg64.r8 Reg64.rbx 8] := by rfl
  have hend : k + 54 + ((PwUnmarshal.drop 54).take 1).length = k + 55 := by rfl
  with_reducible exact Codec.kstep_ldb Reg64.r8 Reg64.rbx 8 _ (k + 54) (k + 55) hq he hend
theorem pw_g4_s54_kind : ∀ (h : Host), type_of% (@pw_g4_s54 h) = @Codec.stepLdbKind h PwUnmarshal Reg64.r8 Reg64.rbx 8 54 55 := by
  intro h; with_reducible rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Directive 55 `mov %r8,0x10(%rax)`: stepStKind. -/
theorem pw_g4_s55 (k : Nat) (hk : PwUnmarshal.IsInfixAt Host.prog k) (hf : LabelsFresh PwUnmarshal k) :
    ∀
    (base a : BitVec 64) (ha : base + (16 : Int64).toBitVec = a) (bs : List UInt8) (hbs : bs.length = 8)
    (F : DataMem → Prop)
    (final : MachineState → Prop) (s : MachineData)
    (hb : s.regs.get64 Reg64.rax = base) (hm : (Eq (bs.At a) ⋆ F) s.dmem)
    (hk' : ∀ m' : DataMem, (Eq ((Int.toBytes 8 (@BitVec.toInt 64 (s.regs.get64 Reg64.r8))).At a) ⋆ F) m' →
      Eventually (step1 Host.exe) final ⟨{ s with dmem := m' }, Host.addrOf (k + 56)⟩),
    Eventually (step1 Host.exe) final ⟨s, Host.addrOf (k + 55)⟩ := by
  have hq := Codec.win hk 55 1
  have he : Codec.eraseNop ((PwUnmarshal.drop 55).take 1) = [Codec.iSt Reg64.r8 Reg64.rax 16] := by rfl
  have hend : k + 55 + ((PwUnmarshal.drop 55).take 1).length = k + 56 := by rfl
  with_reducible exact Codec.kstep_st Reg64.r8 Reg64.rax 16 _ (k + 55) (k + 56) hq he hend
theorem pw_g4_s55_kind : ∀ (h : Host), type_of% (@pw_g4_s55 h) = @Codec.stepStKind h PwUnmarshal Reg64.r8 Reg64.rax 16 55 56 := by
  intro h; with_reducible rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Directive 56 `mov %rsi,%rax`: stepMovRRKind. -/
theorem pw_g4_s56 (k : Nat) (hk : PwUnmarshal.IsInfixAt Host.prog k) (hf : LabelsFresh PwUnmarshal k) :
    ∀
    (final : MachineState → Prop) (s : MachineData)
    (hk' : Eventually (step1 Host.exe) final ⟨Codec.setR s Reg64.rax (s.regs.get64 Reg64.rsi), Host.addrOf (k + 57)⟩),
    Eventually (step1 Host.exe) final ⟨s, Host.addrOf (k + 56)⟩ := by
  have hq := Codec.win hk 56 1
  have he : Codec.eraseNop ((PwUnmarshal.drop 56).take 1) = [Codec.iMovRR Reg64.rax Reg64.rsi] := by rfl
  have hend : k + 56 + ((PwUnmarshal.drop 56).take 1).length = k + 57 := by rfl
  with_reducible exact Codec.kstep_mov_rr Reg64.rax Reg64.rsi _ (k + 56) (k + 57) hq he hend
theorem pw_g4_s56_kind : ∀ (h : Host), type_of% (@pw_g4_s56 h) = @Codec.stepMovRRKind h PwUnmarshal Reg64.rax Reg64.rsi 56 57 := by
  intro h; with_reducible rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Directive 57 `mov %rdx,%rbx`: stepMovRRKind. -/
theorem pw_g4_s57 (k : Nat) (hk : PwUnmarshal.IsInfixAt Host.prog k) (hf : LabelsFresh PwUnmarshal k) :
    ∀
    (final : MachineState → Prop) (s : MachineData)
    (hk' : Eventually (step1 Host.exe) final ⟨Codec.setR s Reg64.rbx (s.regs.get64 Reg64.rdx), Host.addrOf (k + 58)⟩),
    Eventually (step1 Host.exe) final ⟨s, Host.addrOf (k + 57)⟩ := by
  have hq := Codec.win hk 57 1
  have he : Codec.eraseNop ((PwUnmarshal.drop 57).take 1) = [Codec.iMovRR Reg64.rbx Reg64.rdx] := by rfl
  have hend : k + 57 + ((PwUnmarshal.drop 57).take 1).length = k + 58 := by rfl
  with_reducible exact Codec.kstep_mov_rr Reg64.rbx Reg64.rdx _ (k + 57) (k + 58) hq he hend
theorem pw_g4_s57_kind : ∀ (h : Host), type_of% (@pw_g4_s57 h) = @Codec.stepMovRRKind h PwUnmarshal Reg64.rbx Reg64.rdx 57 58 := by
  intro h; with_reducible rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Directive 58 `mov $0x8,%ecx`: stepMovIKind. -/
theorem pw_g4_s58 (k : Nat) (hk : PwUnmarshal.IsInfixAt Host.prog k) (hf : LabelsFresh PwUnmarshal k) :
    ∀
    (final : MachineState → Prop) (s : MachineData)
    (hk' : Eventually (step1 Host.exe) final ⟨Codec.setR s Reg64.rcx (BitVec.zeroExtend 64 (BitVec.truncate 32 (8 : Int64).toBitVec)), Host.addrOf (k + 59)⟩),
    Eventually (step1 Host.exe) final ⟨s, Host.addrOf (k + 58)⟩ := by
  have hq := Codec.win hk 58 1
  have he : Codec.eraseNop ((PwUnmarshal.drop 58).take 1) = [Codec.iMovI Reg64.rcx 8] := by rfl
  have hend : k + 58 + ((PwUnmarshal.drop 58).take 1).length = k + 59 := by rfl
  with_reducible exact Codec.kstep_movi Reg64.rcx 8 _ (k + 58) (k + 59) hq he hend
theorem pw_g4_s58_kind : ∀ (h : Host), type_of% (@pw_g4_s58 h) = @Codec.stepMovIKind h PwUnmarshal Reg64.rcx 8 58 59 := by
  intro h; with_reducible rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- `WithdrawableEpoch`: call block over the window 59–61 (`callq; test; je`), `callq` at 59, continuation label at 88. -/
theorem pw_g4_WithdrawableEpoch_call (k : Nat) (hk : PwUnmarshal.IsInfixAt Host.prog k) (hf : LabelsFresh PwUnmarshal k) :
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
  have he : Codec.eraseNop ((PwUnmarshal.drop 59).take 3) = E2eScal.callDec "github.com_OffchainLabs_prysm_v7_consensus_types_primitives.Epoch.UnmarshalSSZ" "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingPartialWithdrawal.UnmarshalSSZ_159" := by rfl
  have hjc : k + 59 + Codec.nopPos ((PwUnmarshal.drop 59).take 3) 0 = k + 59 := by rfl
  have hB := Codec.infix_sub (q := E2eScal.callDecL "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingPartialWithdrawal.UnmarshalSSZ_159") 88 hk
    (by simp only [PwUnmarshal, E2eScal.callDecL, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero])
  have hl := Machine.label_at' hk hf (j := 88)
    (by simp only [PwUnmarshal, List.getElem?_cons_succ, List.getElem?_cons_zero]; rfl)
    (by simp only [PwUnmarshal, List.take_succ_cons, List.take_zero, List.contains_cons, List.contains_nil]; decide)
  with_reducible exact E2eScal.calldec_seg_w _ _ _ (k + 59) (k + 59) (k + 88) hq he hjc hB hl
theorem pw_g4_WithdrawableEpoch_call_kind : ∀ (h : Host), type_of% (@pw_g4_WithdrawableEpoch_call h) = @E2eScal.callDecSegKindG4 h PwUnmarshal "github.com_OffchainLabs_prysm_v7_consensus_types_primitives.Epoch.UnmarshalSSZ" "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingPartialWithdrawal.UnmarshalSSZ_159" 59 59 88 := by
  intro h; with_reducible rfl

end E2eScal.Gen4Ex
