import Prysm.BeaconBlockHeader.DecodeAcceptFromGeneratedCallSegments
import Prysm.SyncCommitteeMessage.DecodeSegments
import Prysm.SyncCommitteeMessage.GeneratedDecodeSteps
import Prysm.SyncCommitteeMessage.Statements

/-!
# `(*v1alpha1.SyncCommitteeMessage).UnmarshalSSZ`, accept path from the GENERATED `p2dec --gen4` chains

`Decode.accept_from_generated_steps : Decode.accept_statement` (the pre-committed hand statement, `Prysm/SyncCommitteeMessage/Statements.lean`, unchanged). Every field
is a HAND field composition (`sm_gg_*_field`; no kind exists for a field composition, so its statement is checked
only through this accept theorem) over the GENERATED theorems of `Prysm/SyncCommitteeMessage/GeneratedDecodeSteps.lean` (`p2dec --gen4`, raw output):
* Slot 15–46: generated steps 15, 16 + generated call block (`Decode.generated_step_Slot_call`);
* BlockRoot 47–81: generated segment (`Decode.generated_step_BlockRoot_seg`, rY = rax) + generated tail steps 72, 73, 80, 81;
* ValidatorIndex 82–117: generated steps 82–87 + generated call block;
* Signature 120–155: generated segment (the padding `nop` inside its window) + generated tail steps 146, 147, 154, 155.
Hand text that remains: the field compositions, the head `Decode.head0` and the spills `Decode.spill2` (`Prysm/SyncCommitteeMessage/DecodeSegments.lean`; the
generated steps 118 / 119 are not used), the epilogue 156–160 and the accept proof's glue. In-sample (development
data); no transfer claim.
-/

open Machine Runtime Prysm.AttestationData.Code Prysm.SyncCommitteeMessage.Code Codec
variable [Host]

namespace Prysm.SyncCommitteeMessage

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- `Slot`: the WHOLE call field 15–46 (generated steps 15, 16 and the generated call block 17–19, label 46). -/
theorem Decode.from_generated_steps_Slot_field (k : Nat) (hk : Code.unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh Code.unmarshalSSZ k) :
    ∀ (hC : U64CalleeAcc "github.com_OffchainLabs_prysm_v7_consensus_types_primitives.Slot.UnmarshalSSZ")
    (sp rcv bf aRet aFp aS2 : BitVec 64)
    (hRet : sp - 8 = aRet) (hFp : sp - 16 = aFp) (hS2 : sp + 8 = aS2)
    (rbp0 r140 guard : UInt64) (e8 rslot fp s2 c0 : List UInt8)
    (he8 : e8.length = 8) (hrs : rslot.length = 8) (hfp : fp.length = 8) (hs2 : s2.length = 8)
    (hc0 : c0.length = 8) (hguard : guard.toNat < aRet.toNat)
    (F : DataMem → Prop)
    (s : MachineData) (hrsp : s.regs.rsp = { toBitVec := sp }) (hrbp : s.regs.rbp = rbp0)
    (hr14 : s.regs.r14 = r140) (hrax : s.regs.rax.toBitVec = rcv) (hrbx : s.regs.rbx.toBitVec = bf)
    (h_mem : s.dmem =⋆ Eq (rslot.At aRet) ⋆ Eq (fp.At aFp) ⋆ Eq (s2.At aS2)
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (r140.toBitVec + 16))
      ⋆ Eq (e8.At bf) ⋆ Eq (c0.At (rcv + 8)) ⋆ F),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 46 + 1) ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0
        ∧ st.data.regs.rsp = { toBitVec := sp } ∧ st.data.regs.rbp = rbp0 ∧ st.data.regs.r14 = r140 ∧
        (Eq ((Int.toBytes 8 (Host.addrOf (k + 17 + 1)).toBitVec.toInt).At aRet)
          ⋆ Eq ((Int.toBytes 8 rbp0.toBitVec.toInt).At aFp) ⋆ Eq ((Int.toBytes 8 bf.toInt).At aS2)
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (r140.toBitVec + 16))
          ⋆ Eq (e8.At bf) ⋆ Eq (e8.At (rcv + 8)) ⋆ F) st.data.dmem)
      ⟨s, Host.addrOf (k + 15)⟩ := by
  intro hC sp rcv bf aRet aFp aS2 hRet hFp hS2 rbp0 r140 guard e8 rslot fp s2 c0 he8 hrs hfp hs2 hc0
    hguard F s hrsp hrbp hr14 hrax hrbx h_mem
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at hrsp hrbp hr14 hrax hrbx h_mem ⊢
  subst rsp rbp r14 hrax hrbx
  apply Decode.generated_step_s15 k hk hf
  intro fl1; kn
  apply Decode.generated_step_s16 k hk hf
  kn
  refine eventually_trans _ _ _ _ (Decode.generated_step_Slot_call k hk hf hC sp (rax.toBitVec + 8) rbx.toBitVec aRet aFp aS2 hRet hFp hS2 rbp0 r140 guard e8 rslot
    fp s2 c0 he8 hrs hfp hs2 hc0 hguard _ _ (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by first | rfl | decide)
    (by ecancel)) ?_
  rintro ⟨d, pc⟩ ⟨hpc, hrax', hrbx', hrsp', hrbp', hr14', Hm⟩
  dsimp only at hpc hrax' hrbx' hrsp' hrbp' hr14' Hm
  apply Eventually.done
  refine ⟨hpc, hrax', hrbx', hrsp', hrbp', hr14', ?_⟩
  dsimp only
  ecancel

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
/-- `BlockRoot`: the WHOLE byte field 47–81 (segment, then the tail `mov 0x38(%rsp),%rsi; jmp; label; mov %rsi,0x10(%rax)`
as four steps): worked example of the `p2dec --gen4` emission recipe for a byte field. Statement = the segment statement
with the end at directive 82. -/
theorem Decode.from_generated_steps_BlockRoot_field (k : Nat) (hk : Code.unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh Code.unmarshalSSZ k) :
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
    (hms : MakesliceC Heap ElfData.CheckpointAndEpoch.e2eU8Type_addr 1 St) (hmm : MemmoveC St),
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
  refine eventually_trans _ _ _ _ (Decode.generated_step_BlockRoot_seg k hk hf sp rcv bf aR aB aS aRet aLo aP aL aC aSrc St hR hB' hS hRet hLo hP hL hC hSrc rbp0 r140 root hroot spl rslot lo lS vP vL vC hspl hrs hlo hlS hvP hvL hvC R Heap avail hav s hrsp hrbp hr14 h_mem hms hmm) ?_
  rintro ⟨d, pc⟩ ⟨hpc, hrsp', hrbp', hr14', p, spl', lo', hspl', hlo', hrY, Hm⟩
  dsimp only at hpc hrsp' hrbp' hr14' hrY Hm
  subst hpc
  obtain ⟨⟨rax1, rbx1, rcx1, rdx1, rsi1, rdi1, rsp1, rbp1, r81, r91, r101, r111, r121, r131, r141, r151⟩, zmms1, flags1, mem1⟩ := d
  simp only at hrsp' hrbp' hr14' hrY Hm
  subst hrsp' hrbp' hr14'
  apply Decode.generated_step_s72 k hk hf sp aS p hS _ _ _ (by rfl) (by ecancel)
  kn
  apply Decode.generated_step_s73 k hk hf
  apply Decode.generated_step_s80 k hk hf
  apply Decode.generated_step_s81 k hk hf rcv aP hP (Int.toBytes 8 p.toInt) (Int.toBytes_length 8 _) _ _ _ (by exact hrY) (by ecancel)
  intro m' H
  kn
  simp only [Reg64s.get64] at H
  apply Eventually.done
  refine ⟨rfl, rfl, rfl, rfl, p, spl', lo', hspl', hlo', hrY, ?_⟩
  dsimp only
  ecancel

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- `ValidatorIndex` (callee decoder field, Go offset 40, SSZ offset 40): the WHOLE call field 82–117, composed from the
step theorems of its set-up and the call-block theorem (worked example of the `p2dec --gen4` emission recipe). The entry
conditions of the call block (rax = `rcv + 40`, rbx = `bf + 40`, rcx = 8) are closed by `rfl` on the state
that the steps computed. -/
theorem Decode.from_generated_steps_ValidatorIndex_field (k : Nat) (hk : Code.unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh Code.unmarshalSSZ k) :
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
  apply Decode.generated_step_s82 k hk hf sp aB bf hB _ _ _ (by rfl) (by ecancel)
  kn
  apply Decode.generated_step_s83 k hk hf
  intro fl1; kn
  apply Decode.generated_step_s84 k hk hf sp aD hD vD hvD _ _ _ (by rfl) (by ecancel)
  kn
  apply Decode.generated_step_s85 k hk hf
  intro fl2; kn
  apply Decode.generated_step_s86 k hk hf
  intro fl3; kn
  apply Decode.generated_step_s87 k hk hf
  kn
  refine eventually_trans _ _ _ _ (Decode.generated_step_ValidatorIndex_call k hk hf hC sp (rax.toBitVec + 40) (bf + 40) aRet aFp aS2 hRet hFp hS2 rbp0 r140 guard e8 rslot
    fp s2 c0 he8 hrs hfp hs2 hc0 hguard _ _ (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by first | rfl | decide)
    (by ecancel)) ?_
  rintro ⟨d, pc⟩ ⟨hpc, hrax', hrbx', hrsp', hrbp', hr14', Hm⟩
  dsimp only at hpc hrax' hrbx' hrsp' hrbp' hr14' Hm
  apply Eventually.done
  refine ⟨hpc, hrax', hrbx', hrsp', hrbp', hr14', ?_⟩
  dsimp only
  ecancel

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
/-- `Signature`: the WHOLE byte field 120–155 (generated segment, then the generated tail steps 146, 147, 154, 155). -/
theorem Decode.from_generated_steps_Signature_field (k : Nat) (hk : Code.unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh Code.unmarshalSSZ k) :
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
    (hms : MakesliceC Heap ElfData.CheckpointAndEpoch.e2eU8Type_addr 1 St) (hmm : MemmoveC St),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 156) ∧ st.data.regs.rsp = { toBitVec := sp }
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
  intro sp rcv bf aR aB aS aRet aLo aP aL aC aSrc St hR hB' hS hRet hLo hP hL hC hSrc rbp0 r140 root hroot spl rslot lo lS vP vL vC hspl hrs hlo hlS hvP hvL hvC R Heap avail hav s hrsp hrbp hr14 h_mem hms hmm
  refine eventually_trans _ _ _ _ (Decode.generated_step_Signature_seg k hk hf sp rcv bf aR aB aS aRet aLo aP aL aC aSrc St hR hB' hS hRet hLo hP hL hC hSrc rbp0 r140 root hroot spl rslot lo lS vP vL vC hspl hrs hlo hlS hvP hvL hvC R Heap avail hav s hrsp hrbp hr14 h_mem hms hmm) ?_
  rintro ⟨d, pc⟩ ⟨hpc, hrsp', hrbp', hr14', p, spl', lo', hspl', hlo', hrY, Hm⟩
  dsimp only at hpc hrsp' hrbp' hr14' hrY Hm
  subst hpc
  obtain ⟨⟨rax1, rbx1, rcx1, rdx1, rsi1, rdi1, rsp1, rbp1, r81, r91, r101, r111, r121, r131, r141, r151⟩, zmms1, flags1, mem1⟩ := d
  simp only at hrsp' hrbp' hr14' hrY Hm
  subst hrsp' hrbp' hr14'
  apply Decode.generated_step_s146 k hk hf sp aS p hS _ _ _ (by rfl) (by ecancel)
  kn
  apply Decode.generated_step_s147 k hk hf
  apply Decode.generated_step_s154 k hk hf
  apply Decode.generated_step_s155 k hk hf rcv aP hP (Int.toBytes 8 p.toInt) (Int.toBytes_length 8 _) _ _ _ (by exact hrY) (by ecancel)
  intro m' H
  kn
  simp only [Reg64s.get64] at H
  apply Eventually.done
  refine ⟨rfl, rfl, rfl, rfl, p, spl', lo', hspl', hlo', hrY, ?_⟩
  dsimp only
  ecancel

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
/-- **Accept path of the real `(*v1alpha1.SyncCommitteeMessage).UnmarshalSSZ` (Go 1.26.10) from the generated `p2dec --gen4`
chains**; statement = the hand statement `Decode.accept_statement` (unchanged). -/
theorem Decode.accept_from_generated_steps : Decode.accept_statement := by
  intro k hk hf kS hkS hfS kV hkV hfV in0 rt in1 sig hin0 hrt hin1 hsig s ra guard
    fp s1 s2 s4 sp0 sp1 sp2 s28 s30 l38 rslot lo ast a8 aP1 aL1 aC1 a40 aP2 aL2 aC2
    hfp h1 h2 h4 hsp0 hsp1 hsp2 hs28 hs30 hl38 hrs hast ha8 haP1 haL1 haC1 ha40 haP2 haL2 haC2
    R S hS hlo Heap avail h_mem hguard hlen hav hms hmm
  have hsl : U64CalleeAcc Prysm.Slot.Code.unmarshalSSZLabel := Prysm.Slot.Decode.accept_function_spec_holds kS hkS hfS
  have hvi : U64CalleeAcc Prysm.ValidatorIndex.Code.unmarshalLabel := Prysm.ValidatorIndex.Decode.accept_function_spec_holds kV hkV hfV
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hguard hlen ⊢
  have hrsp_lt : rsp.toNat < 2 ^ 64 := rsp.toNat_lt_size
  have hg : guard.toNat < (rsp.toBitVec - 112).toNat := Prysm.BeaconBlockHeader.Decode.accept_guard _ _ hguard
  have hlS : (lo.take S).length = S := by simp [hlo]
  have hl8 : (lo.drop S).length = 8 := by simp [hlo]
  have hlos : Eq (lo.At (rsp.toBitVec - 120 - BitVec.ofNat 64 S)) =
      Eq ((lo.take S).At (rsp.toBitVec - 120 - BitVec.ofNat 64 S)) ⋆ Eq ((lo.drop S).At (rsp.toBitVec - 120)) := by
    conv => lhs; rw [← List.take_append_drop S lo]
    exact Prysm.BeaconBlockHeader.Decode.lo8 _ S hS _ _ hlS hl8
  rw [hlos] at h_mem
  -- head: entry → directive 15
  refine eventually_trans _ _ _ _ (Decode.head0 k hk _ ra guard fp s1 s2 s4 ast hfp h1 h2 h4 hast _
    (by dsimp only; ecancel) (Nat.lt_of_le_of_lt (Nat.le_add_right _ 112) hguard) hlen) ?_
  rintro ⟨d1, pc1⟩ ⟨hpc1, hrsp1, hrbp1, hr141, hrax1, hrbx1, Hm1⟩
  dsimp only at hpc1 hrsp1 hrbp1 hr141 hrax1 hrbx1 Hm1
  subst hpc1
  -- Slot: 15 → 47 (hand field composition over the generated steps 15, 16 and the generated call block)
  refine eventually_trans _ _ _ _ (Decode.from_generated_steps_Slot_field k hk hf hsl
    (rsp.toBitVec - 104) rax.toBitVec rbx.toBitVec (rsp.toBitVec - 112) (rsp.toBitVec - 120) (rsp.toBitVec - 96)
    (by bv_omega) (by bv_omega) (by bv_omega)
    { toBitVec := rsp.toBitVec - 8#64 } r14 guard in0 rslot (lo.drop S) sp1 a8 hin0 hrs hl8 hsp1 ha8 hg _ d1
    hrsp1 hrbp1 hr141 (by rw [hrax1]) (by rw [hrbx1]) (by ecancel)) ?_
  rintro ⟨d3, pc3⟩ ⟨hpc3, hrax3, hrbx3, hrsp3, hrbp3, hr143, Hm3⟩
  dsimp only at hpc3 hrax3 hrbx3 hrsp3 hrbp3 hr143 Hm3
  subst hpc3
  -- BlockRoot: 47 → 82 (hand field composition: generated segment + generated tail steps 72, 73, 80, 81)
  refine eventually_trans _ _ _ _ (Decode.from_generated_steps_BlockRoot_field k hk hf
    (rsp.toBitVec - 104) rax.toBitVec rbx.toBitVec
    (rsp.toBitVec + 8) (rsp.toBitVec + 16) (rsp.toBitVec - 48) (rsp.toBitVec - 112)
    (rsp.toBitVec - 120 - BitVec.ofNat 64 S) (rax.toBitVec + 16) (rax.toBitVec + 24) (rax.toBitVec + 32)
    (rbx.toBitVec + 8) (S + 8)
    (by simp only [Int64.toBitVec_ofNat]; bv_omega) (by simp only [Int64.toBitVec_ofNat]; bv_omega)
    (by simp only [Int64.toBitVec_ofNat]; bv_omega) (by bv_omega) (Prysm.BeaconBlockHeader.Decode.stack_low_eq _ _)
    (by simp only [Int64.toBitVec_ofNat]) (by simp only [Int64.toBitVec_ofNat])
    (by simp only [Int64.toBitVec_ofNat]) (by simp only [Int64.toBitVec_ofNat])
    { toBitVec := rsp.toBitVec - 8#64 } r14 rt hrt
    (sp0 ++ (Int.toBytes 8 rbx.toBitVec.toInt ++ sp2)) (Int.toBytes 8 (Host.addrOf (k + 17 + 1)).toBitVec.toInt)
    (lo.take S ++ Int.toBytes 8 (rsp.toBitVec - 8#64).toInt) l38 aP1 aL1 aC1
    (by simp only [List.length_append, hsp0, hsp2, Int.toBytes_length]) (Int.toBytes_length 8 _)
    (by simp only [List.length_append, hlS, Int.toBytes_length]) hl38 haP1 haL1 haC1
    _ Heap avail (by omega) d3 hrsp3 hrbp3 hr143
    (by rw [Prysm.BeaconBlockHeader.Decode.j3 _ _ _ _ hsp0 (Int.toBytes_length 8 _) hsp2, Prysm.BeaconBlockHeader.Decode.lo8 _ S hS _ _ hlS (Int.toBytes_length 8 _)]
        ecancel) hms hmm) ?_
  rintro ⟨d4, pc4⟩ ⟨hpc4, hrsp4, hrbp4, hr144, p1, spl1, lo1, hspl1, hlo1, hrax4, Hm4⟩
  dsimp only at hpc4 hrsp4 hrbp4 hr144 hrax4 Hm4
  subst hpc4
  -- split the spill area and the low stack for the ValidatorIndex callee
  have hq0 : (spl1.take 8).length = 8 := by simp [hspl1]
  have hq1 : ((spl1.drop 8).take 8).length = 8 := by simp [hspl1]
  have hq2 : ((spl1.drop 8).drop 8).length = 8 := by simp [hspl1]
  have hlS1 : (lo1.take S).length = S := by simp [hlo1]
  have hl81 : (lo1.drop S).length = 8 := by simp [hlo1]
  have hsp3 : spl1 = spl1.take 8 ++ ((spl1.drop 8).take 8 ++ (spl1.drop 8).drop 8) := by
    rw [List.take_append_drop, List.take_append_drop]
  have hlo3 : lo1 = lo1.take S ++ lo1.drop S := (List.take_append_drop S lo1).symm
  rw [hsp3, hlo3, Prysm.BeaconBlockHeader.Decode.j3 _ _ _ _ hq0 hq1 hq2, Prysm.BeaconBlockHeader.Decode.lo8 _ S hS _ _ hlS1 hl81] at Hm4
  -- ValidatorIndex: 82 → 118 (hand field composition: generated steps 82–87 + generated call block; hC = Prysm.ValidatorIndex.Decode.accept_function_spec_holds)
  refine eventually_trans _ _ _ _ (Decode.from_generated_steps_ValidatorIndex_field k hk hf hvi
    (rsp.toBitVec - 104) rax.toBitVec rbx.toBitVec (rsp.toBitVec - 112) (rsp.toBitVec - 120) (rsp.toBitVec - 96)
    (rsp.toBitVec + 16) (rsp.toBitVec + 32) (by bv_omega) (by bv_omega) (by bv_omega)
    (by simp only [Int64.toBitVec_ofNat]; bv_omega) (by simp only [Int64.toBitVec_ofNat]; bv_omega)
    { toBitVec := rsp.toBitVec - 8#64 } r14 guard in1
    (Int.toBytes 8 (Host.addrOf (k + 66 + 1)).toBitVec.toInt) (lo1.drop S) ((spl1.drop 8).take 8) a40
    (Int.toBytes 8 rdi.toBitVec.toInt)
    hin1 (Int.toBytes_length 8 _) hl81 hq1 ha40 (Int.toBytes_length 8 _) hg _ d4 hrsp4 hrbp4 hr144
    (by exact hrax4) (by ecancel)) ?_
  rintro ⟨d6, pc6⟩ ⟨hpc6, hrax6, hrbx6, hrsp6, hrbp6, hr146, Hm6⟩
  dsimp only at hpc6 hrax6 hrbx6 hrsp6 hrbp6 hr146 Hm6
  subst hpc6
  -- nil-error spills 118–119
  refine eventually_trans _ _ _ _ (Decode.spill2 k hk (rsp.toBitVec - 104) (rsp.toBitVec - 64) (rsp.toBitVec - 56)
    (by bv_omega) (by bv_omega) s28 s30 hs28 hs30 _ d6 hrsp6 (by ecancel)) ?_
  rintro ⟨d7, pc7⟩ ⟨hpc7, hrsp7, hrbp7, hr147, Hm7⟩
  dsimp only at hpc7 hrsp7 hrbp7 hr147 Hm7
  subst hpc7
  rw [hrax6, hrbx6] at Hm7
  -- Signature: 120 → 156 (hand field composition: generated segment + generated tail steps 146, 147, 154, 155)
  refine eventually_trans _ _ _ _ (Decode.from_generated_steps_Signature_field k hk hf (rsp.toBitVec - 104) rax.toBitVec rbx.toBitVec
    (rsp.toBitVec + 8) (rsp.toBitVec + 16) (rsp.toBitVec - 48) (rsp.toBitVec - 112)
    (rsp.toBitVec - 120 - BitVec.ofNat 64 S) (rax.toBitVec + 48) (rax.toBitVec + 56) (rax.toBitVec + 64)
    (rbx.toBitVec + 48) (S + 8)
    (by simp only [Int64.toBitVec_ofNat]; bv_omega) (by simp only [Int64.toBitVec_ofNat]; bv_omega)
    (by simp only [Int64.toBitVec_ofNat]; bv_omega) (by bv_omega) (Prysm.BeaconBlockHeader.Decode.stack_low_eq _ _)
    (by simp only [Int64.toBitVec_ofNat]) (by simp only [Int64.toBitVec_ofNat])
    (by simp only [Int64.toBitVec_ofNat]) (by simp only [Int64.toBitVec_ofNat])
    _ _ sig hsig
    (spl1.take 8 ++ (Int.toBytes 8 (rbx.toBitVec + 40).toInt ++ (spl1.drop 8).drop 8))
    (Int.toBytes 8 (Host.addrOf (k + 88 + 1)).toBitVec.toInt)
    (lo1.take S ++ Int.toBytes 8 (rsp.toBitVec - 8#64).toInt) (Int.toBytes 8 p1.toInt) aP2 aL2 aC2
    (by simp only [List.length_append, hq0, hq2, Int.toBytes_length]) (Int.toBytes_length 8 _)
    (by simp only [List.length_append, hlS1, Int.toBytes_length]) (Int.toBytes_length 8 _) haP2 haL2 haC2
    _ Heap (avail - 32) (by omega) d7 (hrsp7.trans hrsp6) (hrbp7.trans hrbp6) (hr147.trans hr146)
    (by rw [Prysm.BeaconBlockHeader.Decode.j3 _ _ _ _ hq0 (Int.toBytes_length 8 _) hq2, Prysm.BeaconBlockHeader.Decode.lo8 _ S hS _ _ hlS1 (Int.toBytes_length 8 _)]
        ecancel) hms hmm) ?_
  rintro ⟨d8, pc8⟩ ⟨hpc8, hrsp8, hrbp8, hr148, p2, spl2, lo2, hspl2, hlo2, hrdx8, Hm8⟩
  dsimp only at hpc8 hrsp8 hrbp8 hr148 hrdx8 Hm8
  subst hpc8
  obtain ⟨⟨rax8, rbx8, rcx8, rdx8, rsi8, rdi8, rsp8, rbp8, r88, r98, r108, r118, r128, r138, r148, r158⟩,
    zmms8, flags8, mem8⟩ := d8
  simp only at hrsp8 hrbp8 hr148 hrdx8 Hm8
  replace hrdx8 : rdx8.toBitVec = rax.toBitVec := hrdx8
  subst hrsp8 hrbp8 hr148
  -- epilogue 156–160 (hand steps)
  kat hk Code.unmarshalSSZ 156
  apply load_step_at _ _ (rsp.toBitVec - 64) _ _ (Int.toBytes 8 (UInt64.toBitVec 0).toInt) _ _ (by bhaddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk Code.unmarshalSSZ 157
  apply load_step_at _ _ (rsp.toBitVec - 56) _ _ (Int.toBytes 8 (UInt64.toBitVec 0).toInt) _ _ (by bhaddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk Code.unmarshalSSZ 158
  kat hk Code.unmarshalSSZ 159
  apply load_step_at _ _ (rsp.toBitVec - 8) _ _ (Int.toBytes 8 rbp.toBitVec.toInt) _ _ (by bhaddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk Code.unmarshalSSZ 160
  apply load_step_at _ _ rsp.toBitVec _ _ (Int.toBytes 8 ra.toBitVec.toInt) _ _ (by bhaddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  apply Eventually.done
  rw [show UInt64.toBitVec 0 = 0#64 from rfl] at Hm8
  rw [show k + 140 + 1 = k + 141 from rfl] at Hm8
  rw [show avail - 32 - 96 = avail - 128 by omega] at Hm8
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, p1, p2, spl2, lo2, hspl2, hlo2, ?_⟩
  rotate_right
  · ecancel
  all_goals first
    | exact trivial
    | with_reducible rfl
    | (apply UInt64.toBitVec_inj.mp
       simp only [UInt64.toBitVec_add, UInt64.toBitVec_ofNat, BitVec.ofNat_eq_ofNat, Width.bits]
       done)
    | (apply UInt64.toBitVec_inj.mp; bhaddr)

end Prysm.SyncCommitteeMessage
