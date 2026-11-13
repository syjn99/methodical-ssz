import Codec.Kind.DecodeAcceptAnyFrameInstances
import Codec.FieldFrame
import Prysm.ValidatorIndex.DecodeAcceptFunctionSpec
import Prysm.Epoch.DecodeAccept
import Prysm.Slot.DecodeAccept
import Prysm.PendingDeposit.GeneratedDecodeSteps

/-!
# Worked example: `(*v1alpha1.PendingDeposit).UnmarshalSSZ`, accept theorem in generated style

Text produced from one description of the type (frame facts, field list, boundary states, chain theorem names)
by a scratch emitter (not in the tree); every theorem has a `_kind` line (`decHeadKindAnyFrame`, `decFieldKindAnyFrame`,
`decEpilogueKindAnyFrame`, `decAcceptKindAnyFrame`). The `decoder --steps` chain theorems (`Decode.generated_step_*`) are used as emitted.
-/

open Machine Runtime Prysm.AttestationData.Code Prysm.PendingDeposit.Code Codec
variable [Host]

namespace Prysm.PendingDeposit

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Head: directives 0–13 (prologue, spills); entry → boundary state 0. -/
theorem Decode.example_head : ∀ (k : Nat) (hk : Code.unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh Code.unmarshalSSZ k)
    (kS : Nat) (hkS : Prysm.Slot.Code.unmarshalSSZ.IsInfixAt Host.prog kS) (hfS : LabelsFresh Prysm.Slot.Code.unmarshalSSZ kS)
    (pk wc amt sig sl : List UInt8) (hpk : pk.length = 48) (hwc : wc.length = 32) (hamt : amt.length = 8) (hsig : sig.length = 96) (hsl : sl.length = 8)
    (s : MachineData) (ra guard : UInt64)
    (fp s1 s2 s4 sp0 sp1 sp2 l28 rslot lo ast aP0 aL0 aC0 aP1 aL1 aC1 aN2 aP3 aL3 aC3 aN4 : List UInt8)
    (hfp : fp.length = 8) (hs1 : s1.length = 8) (hs2 : s2.length = 8) (hs4 : s4.length = 8) (hsp0 : sp0.length = 8) (hsp1 : sp1.length = 8) (hsp2 : sp2.length = 8) (hl28 : l28.length = 8) (hrslot : rslot.length = 8) (hast : ast.length = 8) (haP0 : aP0.length = 8) (haL0 : aL0.length = 8) (haC0 : aC0.length = 8) (haP1 : aP1.length = 8) (haL1 : aL1.length = 8) (haC1 : aC1.length = 8) (haN2 : aN2.length = 8) (haP3 : aP3.length = 8) (haL3 : aL3.length = 8) (haC3 : aC3.length = 8) (haN4 : aN4.length = 8)
    (R : DataMem → Prop) (S : Nat) (hS : S < 2 ^ 60) (hlo : lo.length = S + 8)
    (Heap : Nat → DataMem → Prop) (avail : Nat)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8))
      ⋆ Eq (s1.At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq (s4.At (s.regs.rsp.toBitVec + 32))
      ⋆ Eq (sp0.At (s.regs.rsp.toBitVec - 72))
      ⋆ Eq (sp1.At (s.regs.rsp.toBitVec - 64))
      ⋆ Eq (sp2.At (s.regs.rsp.toBitVec - 56))
      ⋆ Eq (l28.At (s.regs.rsp.toBitVec - 32))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 80))
      ⋆ Eq (lo.At (s.regs.rsp.toBitVec - 88 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Heap avail
      ⋆ Eq (pk.At s.regs.rbx.toBitVec)
      ⋆ Eq (wc.At (s.regs.rbx.toBitVec + 48))
      ⋆ Eq (amt.At (s.regs.rbx.toBitVec + 80))
      ⋆ Eq (sig.At (s.regs.rbx.toBitVec + 88))
      ⋆ Eq (sl.At (s.regs.rbx.toBitVec + 184))
      ⋆ Eq (ast.At s.regs.rax.toBitVec)
      ⋆ Eq (aP0.At (s.regs.rax.toBitVec + 8))
      ⋆ Eq (aL0.At (s.regs.rax.toBitVec + 16))
      ⋆ Eq (aC0.At (s.regs.rax.toBitVec + 24))
      ⋆ Eq (aP1.At (s.regs.rax.toBitVec + 32))
      ⋆ Eq (aL1.At (s.regs.rax.toBitVec + 40))
      ⋆ Eq (aC1.At (s.regs.rax.toBitVec + 48))
      ⋆ Eq (aN2.At (s.regs.rax.toBitVec + 56))
      ⋆ Eq (aP3.At (s.regs.rax.toBitVec + 64))
      ⋆ Eq (aL3.At (s.regs.rax.toBitVec + 72))
      ⋆ Eq (aC3.At (s.regs.rax.toBitVec + 80))
      ⋆ Eq (aN4.At (s.regs.rax.toBitVec + 88))
      ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec)
      ⋆ R)
    (hguard : guard.toNat + 80 < s.regs.rsp.toNat) (hlen : s.regs.rcx = 192) (hav : 176 ≤ avail)
    (hms : MakesliceContract Heap ElfData.PrysmTarget.typeUint8_addr 1 (S + 8)) (hmm : MemmoveContract (S + 8)),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 14)
        ∧ st.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - 72 }
        ∧ st.data.regs.rbp = { toBitVec := s.regs.rsp.toBitVec - 8 }
        ∧ st.data.regs.r14 = s.regs.r14 ∧
        
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec + 32))
          ⋆ Eq (sp0.At (s.regs.rsp.toBitVec - 72))
          ⋆ Eq (sp1.At (s.regs.rsp.toBitVec - 64))
          ⋆ Eq (sp2.At (s.regs.rsp.toBitVec - 56))
          ⋆ Eq (l28.At (s.regs.rsp.toBitVec - 32))
          ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 80))
          ⋆ Eq (lo.At (s.regs.rsp.toBitVec - 88 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Heap avail
          ⋆ Eq (pk.At s.regs.rbx.toBitVec)
          ⋆ Eq (wc.At (s.regs.rbx.toBitVec + 48))
          ⋆ Eq (amt.At (s.regs.rbx.toBitVec + 80))
          ⋆ Eq (sig.At (s.regs.rbx.toBitVec + 88))
          ⋆ Eq (sl.At (s.regs.rbx.toBitVec + 184))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq (aP0.At (s.regs.rax.toBitVec + 8))
          ⋆ Eq (aL0.At (s.regs.rax.toBitVec + 16))
          ⋆ Eq (aC0.At (s.regs.rax.toBitVec + 24))
          ⋆ Eq (aP1.At (s.regs.rax.toBitVec + 32))
          ⋆ Eq (aL1.At (s.regs.rax.toBitVec + 40))
          ⋆ Eq (aC1.At (s.regs.rax.toBitVec + 48))
          ⋆ Eq (aN2.At (s.regs.rax.toBitVec + 56))
          ⋆ Eq (aP3.At (s.regs.rax.toBitVec + 64))
          ⋆ Eq (aL3.At (s.regs.rax.toBitVec + 72))
          ⋆ Eq (aC3.At (s.regs.rax.toBitVec + 80))
          ⋆ Eq (aN4.At (s.regs.rax.toBitVec + 88))
          ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec)
          ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  intro k hk hf kS hkS hfS pk wc amt sig sl hpk hwc hamt hsig hsl s ra guard fp s1 s2 s4 sp0 sp1 sp2 l28 rslot lo ast aP0 aL0 aC0 aP1 aL1 aC1 aN2 aP3 aL3 aC3 aN4 hfp hs1 hs2 hs4 hsp0 hsp1 hsp2 hl28 hrslot hast haP0 haL0 haC0 haP1 haL1 haC1 haN2 haP3 haL3 haC3 haN4 R S hS hlo Heap avail h_mem hguard hlen hav hms hmm
  refine eventually_trans _ _ _ _ (decpro_seg _ _ _ _ 64 88 192 _ k (k + 11) (window_infix_at hk 0 11) (by rfl) (by rfl)
    s ra guard (s.regs.rsp.toBitVec - 72) (s.regs.rsp.toBitVec + 16)
    (by simp only [Int64.toBitVec_ofNat] <;> bv_omega) (by simp only [Int64.toBitVec_ofNat] <;> bv_omega)
    fp s2 hfp hs2 _ (by ecancel) (Nat.lt_of_le_of_lt (Nat.le_add_right _ 80) hguard) (by rw [hlen]; rfl)) ?_
  rintro ⟨d1, pc1⟩ ⟨hpc1, hrsp1, hrbp1, hreg1, Hm1⟩
  dsimp only at hpc1 hrsp1 hrbp1 hreg1 Hm1
  subst hpc1
  have hrax1 := UInt64.toBitVec_inj.mp (hreg1 Reg64.rax (by decide) (by decide))
  have hrbx1 := UInt64.toBitVec_inj.mp (hreg1 Reg64.rbx (by decide) (by decide))
  have hrdi1 := UInt64.toBitVec_inj.mp (hreg1 Reg64.rdi (by decide) (by decide))
  have hr141 := UInt64.toBitVec_inj.mp (hreg1 Reg64.r14 (by decide) (by decide))
  clear hreg1
  obtain ⟨⟨rax1, rbx1, rcx1, rdx1, rsi1, rdi1, rsp1, rbp1, r81, r91, r101, r111, r121, r131, r141, r151⟩, zmms1, flags1, mem1⟩ := d1
  simp only at hrsp1 hrbp1 hrax1 hrbx1 hrdi1 hr141 Hm1
  subst hrsp1 hrbp1 hrax1 hrbx1 hrdi1 hr141
  apply step_store Reg64.rax Reg64.rsp 80 _ (k + 11) (k + 12) (window_infix_at hk 11 1) (by rfl) (by rfl)
    (s.regs.rsp.toBitVec - 72) (s.regs.rsp.toBitVec + 8) (by simp only [Int64.toBitVec_ofNat] <;> bv_omega)
    s1 hs1 _ _ _ (by rfl) (by ecancel)
  intro m11 H11; normalize_registers; simp only [Reg64s.get64] at H11
  apply step_store Reg64.rdi Reg64.rsp 104 _ (k + 12) (k + 13) (window_infix_at hk 12 1) (by rfl) (by rfl)
    (s.regs.rsp.toBitVec - 72) (s.regs.rsp.toBitVec + 32) (by simp only [Int64.toBitVec_ofNat] <;> bv_omega)
    s4 hs4 _ _ _ (by rfl) (by ecancel)
  intro m12 H12; normalize_registers; simp only [Reg64s.get64] at H12
  apply step_store Reg64.rbx Reg64.rsp 88 _ (k + 13) (k + 14) (window_infix_at hk 13 1) (by rfl) (by rfl)
    (s.regs.rsp.toBitVec - 72) (s.regs.rsp.toBitVec + 16) (by simp only [Int64.toBitVec_ofNat] <;> bv_omega)
    (Int.toBytes 8 s.regs.rbx.toBitVec.toInt) (Int.toBytes_length 8 _) _ _ _ (by rfl) (by ecancel)
  intro m13 H13; normalize_registers; simp only [Reg64s.get64] at H13
  apply Eventually.done
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  dsimp only
  ecancel
theorem Decode.example_head_kind : ∀ (h : Host), type_of% (@Decode.example_head h)
    = @Codec.decHeadKindAnyFrame h Code.unmarshalSSZ (Codec.layoutMixedFrame40 [Prysm.Slot.Code.unmarshalSSZ] 131 2) [.bytes 48, .bytes 32, .u64, .bytes 96, .u64]
    ⟨14, 0, [],
      [.at (.below 8) (.reg .rbp), .at (.above 8) (.reg .rax), .at (.above 16) (.reg .rbx), .at (.above 32) (.reg .rdi), .at (.below 72) (.original 4), .at (.below 64) (.original 5), .at (.below 56) (.original 6), .at (.below 32) (.original 7), .at (.below 80) (.original 8), .low (.original 9)],
      []⟩ := by
  intro h; rfl

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
/-- Field 1 `PublicKey` (bytes): boundary state 0 (directive 14) → boundary state 1 (directive 49). -/
theorem Decode.example_f1 : ∀ (k : Nat) (hk : Code.unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh Code.unmarshalSSZ k)
    (kS : Nat) (hkS : Prysm.Slot.Code.unmarshalSSZ.IsInfixAt Host.prog kS) (hfS : LabelsFresh Prysm.Slot.Code.unmarshalSSZ kS)
    (pk wc amt sig sl : List UInt8) (hpk : pk.length = 48) (hwc : wc.length = 32) (hamt : amt.length = 8) (hsig : sig.length = 96) (hsl : sl.length = 8)
    (s : MachineData) (ra guard : UInt64)
    (fp s1 s2 s4 sp0 sp1 sp2 l28 rslot lo ast aP0 aL0 aC0 aP1 aL1 aC1 aN2 aP3 aL3 aC3 aN4 : List UInt8)
    (hfp : fp.length = 8) (hs1 : s1.length = 8) (hs2 : s2.length = 8) (hs4 : s4.length = 8) (hsp0 : sp0.length = 8) (hsp1 : sp1.length = 8) (hsp2 : sp2.length = 8) (hl28 : l28.length = 8) (hrslot : rslot.length = 8) (hast : ast.length = 8) (haP0 : aP0.length = 8) (haL0 : aL0.length = 8) (haC0 : aC0.length = 8) (haP1 : aP1.length = 8) (haL1 : aL1.length = 8) (haC1 : aC1.length = 8) (haN2 : aN2.length = 8) (haP3 : aP3.length = 8) (haL3 : aL3.length = 8) (haC3 : aC3.length = 8) (haN4 : aN4.length = 8)
    (R : DataMem → Prop) (S : Nat) (hS : S < 2 ^ 60) (hlo : lo.length = S + 8)
    (Heap : Nat → DataMem → Prop) (avail : Nat)
    (hguard : guard.toNat + 80 < s.regs.rsp.toNat) (hav : 176 ≤ avail)
    (hms : MakesliceContract Heap ElfData.PrysmTarget.typeUint8_addr 1 (S + 8)) (hmm : MemmoveContract (S + 8)) (st0 : MachineState),
    (st0.pc = Host.addrOf (k + 14)
        ∧ st0.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - 72 }
        ∧ st0.data.regs.rbp = { toBitVec := s.regs.rsp.toBitVec - 8 }
        ∧ st0.data.regs.r14 = s.regs.r14 ∧
        
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec + 32))
          ⋆ Eq (sp0.At (s.regs.rsp.toBitVec - 72))
          ⋆ Eq (sp1.At (s.regs.rsp.toBitVec - 64))
          ⋆ Eq (sp2.At (s.regs.rsp.toBitVec - 56))
          ⋆ Eq (l28.At (s.regs.rsp.toBitVec - 32))
          ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 80))
          ⋆ Eq (lo.At (s.regs.rsp.toBitVec - 88 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Heap avail
          ⋆ Eq (pk.At s.regs.rbx.toBitVec)
          ⋆ Eq (wc.At (s.regs.rbx.toBitVec + 48))
          ⋆ Eq (amt.At (s.regs.rbx.toBitVec + 80))
          ⋆ Eq (sig.At (s.regs.rbx.toBitVec + 88))
          ⋆ Eq (sl.At (s.regs.rbx.toBitVec + 184))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq (aP0.At (s.regs.rax.toBitVec + 8))
          ⋆ Eq (aL0.At (s.regs.rax.toBitVec + 16))
          ⋆ Eq (aC0.At (s.regs.rax.toBitVec + 24))
          ⋆ Eq (aP1.At (s.regs.rax.toBitVec + 32))
          ⋆ Eq (aL1.At (s.regs.rax.toBitVec + 40))
          ⋆ Eq (aC1.At (s.regs.rax.toBitVec + 48))
          ⋆ Eq (aN2.At (s.regs.rax.toBitVec + 56))
          ⋆ Eq (aP3.At (s.regs.rax.toBitVec + 64))
          ⋆ Eq (aL3.At (s.regs.rax.toBitVec + 72))
          ⋆ Eq (aC3.At (s.regs.rax.toBitVec + 80))
          ⋆ Eq (aN4.At (s.regs.rax.toBitVec + 88))
          ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec)
          ⋆ R) st0.data.dmem) →
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 49)
        ∧ st.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - 72 }
        ∧ st.data.regs.rbp = { toBitVec := s.regs.rsp.toBitVec - 8 }
        ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ (p1 : BitVec 64) (x0 x1 : List UInt8), x0.length = 24 ∧ x1.length = S + 8 ∧ 
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec + 32))
          ⋆ Eq (x0.At (s.regs.rsp.toBitVec - 72))
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rsp.toBitVec - 32))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 33)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 80))
          ⋆ Eq (x1.At (s.regs.rsp.toBitVec - 88 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Heap (avail - 48)
          ⋆ Eq (pk.At s.regs.rbx.toBitVec)
          ⋆ Eq (wc.At (s.regs.rbx.toBitVec + 48))
          ⋆ Eq (amt.At (s.regs.rbx.toBitVec + 80))
          ⋆ Eq (sig.At (s.regs.rbx.toBitVec + 88))
          ⋆ Eq (sl.At (s.regs.rbx.toBitVec + 184))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 48).At (s.regs.rax.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 48).At (s.regs.rax.toBitVec + 24))
          ⋆ Eq (aP1.At (s.regs.rax.toBitVec + 32))
          ⋆ Eq (aL1.At (s.regs.rax.toBitVec + 40))
          ⋆ Eq (aC1.At (s.regs.rax.toBitVec + 48))
          ⋆ Eq (aN2.At (s.regs.rax.toBitVec + 56))
          ⋆ Eq (aP3.At (s.regs.rax.toBitVec + 64))
          ⋆ Eq (aL3.At (s.regs.rax.toBitVec + 72))
          ⋆ Eq (aC3.At (s.regs.rax.toBitVec + 80))
          ⋆ Eq (aN4.At (s.regs.rax.toBitVec + 88))
          ⋆ Eq (pk.At p1)
          ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec)
          ⋆ R) st.data.dmem)
      st0 := by
  intro k hk hf kS hkS hfS pk wc amt sig sl hpk hwc hamt hsig hsl s ra guard fp s1 s2 s4 sp0 sp1 sp2 l28 rslot lo ast aP0 aL0 aC0 aP1 aL1 aC1 aN2 aP3 aL3 aC3 aN4 hfp hs1 hs2 hs4 hsp0 hsp1 hsp2 hl28 hrslot hast haP0 haL0 haC0 haP1 haL1 haC1 haN2 haP3 haL3 haC3 haN4 R S hS hlo Heap avail hguard hav hms hmm
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at hguard ⊢
  rintro ⟨d, pc⟩ ⟨hpc, hrsp, hrbp, hr14, Hm⟩
  dsimp only at hpc hrsp hrbp hr14  Hm
  subst hpc
  refine eventually_trans _ _ _ _ (Decode.generated_step_PublicKey_seg k hk hf (rsp.toBitVec - 72) rax.toBitVec rbx.toBitVec
    (rsp.toBitVec + 8) (rsp.toBitVec + 16) (rsp.toBitVec - 32) (rsp.toBitVec - 80)
    (rsp.toBitVec - 88 - BitVec.ofNat 64 S) (rax.toBitVec + 8) (rax.toBitVec + 16) (rax.toBitVec + 24) (S + 8)
    (by simp only [Int64.toBitVec_ofNat] <;> bv_omega) (by simp only [Int64.toBitVec_ofNat] <;> bv_omega) (by simp only [Int64.toBitVec_ofNat] <;> bv_omega) (by bv_omega) (frame_low_address_with_calls _ 72 88 S (by decide))
    (by simp only [Int64.toBitVec_ofNat] <;> bv_omega) (by simp only [Int64.toBitVec_ofNat] <;> bv_omega) (by simp only [Int64.toBitVec_ofNat] <;> bv_omega)
    { toBitVec := rsp.toBitVec - 8#64 } r14 pk hpk
    (sp0 ++ (sp1 ++ sp2)) rslot lo l28 aP0 aL0 aC0
    (by simp only [List.length_append, Int.toBytes_length, hsp0, hsp1, hsp2]) hrslot hlo hl28 haP0 haL0 haC0
    _ Heap avail (by omega) d hrsp hrbp hr14
      (by rw [frame_join_three_words (rsp.toBitVec - 72) (rsp.toBitVec - 64) (rsp.toBitVec - 56) _ _ _ hsp0 hsp1 hsp2 (by bv_omega) (by bv_omega)]; ecancel) hms hmm) ?_
  rintro ⟨d', pc'⟩ ⟨hpc', hrsp', hrbp', hr14', p1, spl', lo', hspl', hlo', hrY, Hm'⟩
  dsimp only at hpc' hrsp' hrbp' hr14' hrY Hm'
  subst hpc'
  obtain ⟨⟨rax2, rbx2, rcx2, rdx2, rsi2, rdi2, rsp2, rbp2, r82, r92, r102, r112, r122, r132, r142, r152⟩, zmms2, flags2, mem2⟩ := d'
  simp only at hrsp' hrbp' hr14' hrY Hm'
  subst rsp2 rbp2 r142
  apply Decode.generated_step_s38 k hk hf (rsp.toBitVec - 72) (rsp.toBitVec - 32) p1 (by simp only [Int64.toBitVec_ofNat] <;> bv_omega) _ _ _ (by rfl) (by ecancel)
  normalize_registers
  apply Decode.generated_step_s39 k hk hf
  apply Decode.generated_step_s47 k hk hf
  apply Decode.generated_step_s48 k hk hf rax.toBitVec (rax.toBitVec + 8) (by simp only [Int64.toBitVec_ofNat] <;> bv_omega) (Int.toBytes 8 p1.toInt) (Int.toBytes_length 8 _) _ _ _
    (by exact hrY) (by ecancel)
  intro m' H
  normalize_registers
  simp only [Reg64s.get64] at H
  apply Eventually.done
  refine ⟨rfl, rfl, rfl, rfl, p1, spl', lo', hspl', hlo', ?_⟩
  dsimp only
  rw [show k + 32 + 1 = k + 33 from rfl] at H
  ecancel
theorem Decode.example_f1_kind : ∀ (h : Host), type_of% (@Decode.example_f1 h)
    = @Codec.decFieldKindAnyFrame h Code.unmarshalSSZ (Codec.layoutMixedFrame40 [Prysm.Slot.Code.unmarshalSSZ] 131 2) [.bytes 48, .bytes 32, .u64, .bytes 96, .u64]
    ⟨14, 0, [],
      [.at (.below 8) (.reg .rbp), .at (.above 8) (.reg .rax), .at (.above 16) (.reg .rbx), .at (.above 32) (.reg .rdi), .at (.below 72) (.original 4), .at (.below 64) (.original 5), .at (.below 56) (.original 6), .at (.below 32) (.original 7), .at (.below 80) (.original 8), .low (.original 9)],
      []⟩
    ⟨49, 1, [],
      [.at (.below 8) (.reg .rbp), .at (.above 8) (.reg .rax), .at (.above 16) (.reg .rbx), .at (.above 32) (.reg .rdi), .at (.below 72) (.existential 0), .at (.below 32) (.ptr 0), .at (.below 80) (.ret 33), .low (.existential 1)],
      [.fixed 24, .low]⟩ := by
  intro h; rfl

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
/-- Field 2 `WithdrawalCredentials` (bytes): boundary state 1 (directive 49) → boundary state 2 (directive 85). -/
theorem Decode.example_f2 : ∀ (k : Nat) (hk : Code.unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh Code.unmarshalSSZ k)
    (kS : Nat) (hkS : Prysm.Slot.Code.unmarshalSSZ.IsInfixAt Host.prog kS) (hfS : LabelsFresh Prysm.Slot.Code.unmarshalSSZ kS)
    (pk wc amt sig sl : List UInt8) (hpk : pk.length = 48) (hwc : wc.length = 32) (hamt : amt.length = 8) (hsig : sig.length = 96) (hsl : sl.length = 8)
    (s : MachineData) (ra guard : UInt64)
    (fp s1 s2 s4 sp0 sp1 sp2 l28 rslot lo ast aP0 aL0 aC0 aP1 aL1 aC1 aN2 aP3 aL3 aC3 aN4 : List UInt8)
    (hfp : fp.length = 8) (hs1 : s1.length = 8) (hs2 : s2.length = 8) (hs4 : s4.length = 8) (hsp0 : sp0.length = 8) (hsp1 : sp1.length = 8) (hsp2 : sp2.length = 8) (hl28 : l28.length = 8) (hrslot : rslot.length = 8) (hast : ast.length = 8) (haP0 : aP0.length = 8) (haL0 : aL0.length = 8) (haC0 : aC0.length = 8) (haP1 : aP1.length = 8) (haL1 : aL1.length = 8) (haC1 : aC1.length = 8) (haN2 : aN2.length = 8) (haP3 : aP3.length = 8) (haL3 : aL3.length = 8) (haC3 : aC3.length = 8) (haN4 : aN4.length = 8)
    (R : DataMem → Prop) (S : Nat) (hS : S < 2 ^ 60) (hlo : lo.length = S + 8)
    (Heap : Nat → DataMem → Prop) (avail : Nat)
    (hguard : guard.toNat + 80 < s.regs.rsp.toNat) (hav : 176 ≤ avail)
    (hms : MakesliceContract Heap ElfData.PrysmTarget.typeUint8_addr 1 (S + 8)) (hmm : MemmoveContract (S + 8)) (st0 : MachineState),
    (st0.pc = Host.addrOf (k + 49)
        ∧ st0.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - 72 }
        ∧ st0.data.regs.rbp = { toBitVec := s.regs.rsp.toBitVec - 8 }
        ∧ st0.data.regs.r14 = s.regs.r14 ∧
        ∃ (p1 : BitVec 64) (x0 x1 : List UInt8), x0.length = 24 ∧ x1.length = S + 8 ∧ 
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec + 32))
          ⋆ Eq (x0.At (s.regs.rsp.toBitVec - 72))
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rsp.toBitVec - 32))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 33)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 80))
          ⋆ Eq (x1.At (s.regs.rsp.toBitVec - 88 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Heap (avail - 48)
          ⋆ Eq (pk.At s.regs.rbx.toBitVec)
          ⋆ Eq (wc.At (s.regs.rbx.toBitVec + 48))
          ⋆ Eq (amt.At (s.regs.rbx.toBitVec + 80))
          ⋆ Eq (sig.At (s.regs.rbx.toBitVec + 88))
          ⋆ Eq (sl.At (s.regs.rbx.toBitVec + 184))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 48).At (s.regs.rax.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 48).At (s.regs.rax.toBitVec + 24))
          ⋆ Eq (aP1.At (s.regs.rax.toBitVec + 32))
          ⋆ Eq (aL1.At (s.regs.rax.toBitVec + 40))
          ⋆ Eq (aC1.At (s.regs.rax.toBitVec + 48))
          ⋆ Eq (aN2.At (s.regs.rax.toBitVec + 56))
          ⋆ Eq (aP3.At (s.regs.rax.toBitVec + 64))
          ⋆ Eq (aL3.At (s.regs.rax.toBitVec + 72))
          ⋆ Eq (aC3.At (s.regs.rax.toBitVec + 80))
          ⋆ Eq (aN4.At (s.regs.rax.toBitVec + 88))
          ⋆ Eq (pk.At p1)
          ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec)
          ⋆ R) st0.data.dmem) →
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 85)
        ∧ st.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - 72 }
        ∧ st.data.regs.rbp = { toBitVec := s.regs.rsp.toBitVec - 8 }
        ∧ st.data.regs.r14 = s.regs.r14
        ∧ st.data.regs.get64 Reg64.rdx = s.regs.rax.toBitVec ∧
        ∃ (p1 p2 : BitVec 64) (x0 x1 : List UInt8), x0.length = 24 ∧ x1.length = S + 8 ∧ 
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec + 32))
          ⋆ Eq (x0.At (s.regs.rsp.toBitVec - 72))
          ⋆ Eq ((Int.toBytes 8 p2.toInt).At (s.regs.rsp.toBitVec - 32))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 69)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 80))
          ⋆ Eq (x1.At (s.regs.rsp.toBitVec - 88 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Heap (avail - 80)
          ⋆ Eq (pk.At s.regs.rbx.toBitVec)
          ⋆ Eq (wc.At (s.regs.rbx.toBitVec + 48))
          ⋆ Eq (amt.At (s.regs.rbx.toBitVec + 80))
          ⋆ Eq (sig.At (s.regs.rbx.toBitVec + 88))
          ⋆ Eq (sl.At (s.regs.rbx.toBitVec + 184))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 48).At (s.regs.rax.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 48).At (s.regs.rax.toBitVec + 24))
          ⋆ Eq ((Int.toBytes 8 p2.toInt).At (s.regs.rax.toBitVec + 32))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 40))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 48))
          ⋆ Eq (aN2.At (s.regs.rax.toBitVec + 56))
          ⋆ Eq (aP3.At (s.regs.rax.toBitVec + 64))
          ⋆ Eq (aL3.At (s.regs.rax.toBitVec + 72))
          ⋆ Eq (aC3.At (s.regs.rax.toBitVec + 80))
          ⋆ Eq (aN4.At (s.regs.rax.toBitVec + 88))
          ⋆ Eq (pk.At p1)
          ⋆ Eq (wc.At p2)
          ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec)
          ⋆ R) st.data.dmem)
      st0 := by
  intro k hk hf kS hkS hfS pk wc amt sig sl hpk hwc hamt hsig hsl s ra guard fp s1 s2 s4 sp0 sp1 sp2 l28 rslot lo ast aP0 aL0 aC0 aP1 aL1 aC1 aN2 aP3 aL3 aC3 aN4 hfp hs1 hs2 hs4 hsp0 hsp1 hsp2 hl28 hrslot hast haP0 haL0 haC0 haP1 haL1 haC1 haN2 haP3 haL3 haC3 haN4 R S hS hlo Heap avail hguard hav hms hmm
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at hguard ⊢
  rintro ⟨d, pc⟩ ⟨hpc, hrsp, hrbp, hr14, p1, x0, x1, hx0, hx1, Hm⟩
  dsimp only at hpc hrsp hrbp hr14  Hm
  subst hpc
  refine eventually_trans _ _ _ _ (Decode.generated_step_WithdrawalCredentials_seg k hk hf (rsp.toBitVec - 72) rax.toBitVec rbx.toBitVec
    (rsp.toBitVec + 8) (rsp.toBitVec + 16) (rsp.toBitVec - 32) (rsp.toBitVec - 80)
    (rsp.toBitVec - 88 - BitVec.ofNat 64 S) (rax.toBitVec + 32) (rax.toBitVec + 40) (rax.toBitVec + 48) (rbx.toBitVec + 48) (S + 8)
    (by simp only [Int64.toBitVec_ofNat] <;> bv_omega) (by simp only [Int64.toBitVec_ofNat] <;> bv_omega) (by simp only [Int64.toBitVec_ofNat] <;> bv_omega) (by bv_omega) (frame_low_address_with_calls _ 72 88 S (by decide))
    (by simp only [Int64.toBitVec_ofNat] <;> bv_omega) (by simp only [Int64.toBitVec_ofNat] <;> bv_omega) (by simp only [Int64.toBitVec_ofNat] <;> bv_omega) (by simp only [Int64.toBitVec_ofNat] <;> bv_omega)
    { toBitVec := rsp.toBitVec - 8#64 } r14 wc hwc
    x0 (Int.toBytes 8 (Host.addrOf (k + 33)).toBitVec.toInt) x1 (Int.toBytes 8 p1.toInt) aP1 aL1 aC1
    hx0 (Int.toBytes_length 8 _) hx1 (Int.toBytes_length 8 _) haP1 haL1 haC1
    _ Heap (avail - 48) (by omega) d hrsp hrbp hr14
      (by ecancel) hms hmm) ?_
  rintro ⟨d', pc'⟩ ⟨hpc', hrsp', hrbp', hr14', p2, spl', lo', hspl', hlo', hrY, Hm'⟩
  dsimp only at hpc' hrsp' hrbp' hr14' hrY Hm'
  subst hpc'
  obtain ⟨⟨rax2, rbx2, rcx2, rdx2, rsi2, rdi2, rsp2, rbp2, r82, r92, r102, r112, r122, r132, r142, r152⟩, zmms2, flags2, mem2⟩ := d'
  simp only at hrsp' hrbp' hr14' hrY Hm'
  subst rsp2 rbp2 r142
  apply Decode.generated_step_s74 k hk hf (rsp.toBitVec - 72) (rsp.toBitVec - 32) p2 (by simp only [Int64.toBitVec_ofNat] <;> bv_omega) _ _ _ (by rfl) (by ecancel)
  normalize_registers
  apply Decode.generated_step_s75 k hk hf
  apply Decode.generated_step_s83 k hk hf
  apply Decode.generated_step_s84 k hk hf rax.toBitVec (rax.toBitVec + 32) (by simp only [Int64.toBitVec_ofNat] <;> bv_omega) (Int.toBytes 8 p2.toInt) (Int.toBytes_length 8 _) _ _ _
    (by exact hrY) (by ecancel)
  intro m' H
  normalize_registers
  simp only [Reg64s.get64] at H
  apply Eventually.done
  refine ⟨rfl, rfl, rfl, rfl, hrY, p1, p2, spl', lo', hspl', hlo', ?_⟩
  dsimp only
  rw [show k + 68 + 1 = k + 69 from rfl] at H
  rw [show avail - 48 - 32 = avail - 80 by omega] at H
  ecancel
theorem Decode.example_f2_kind : ∀ (h : Host), type_of% (@Decode.example_f2 h)
    = @Codec.decFieldKindAnyFrame h Code.unmarshalSSZ (Codec.layoutMixedFrame40 [Prysm.Slot.Code.unmarshalSSZ] 131 2) [.bytes 48, .bytes 32, .u64, .bytes 96, .u64]
    ⟨49, 1, [],
      [.at (.below 8) (.reg .rbp), .at (.above 8) (.reg .rax), .at (.above 16) (.reg .rbx), .at (.above 32) (.reg .rdi), .at (.below 72) (.existential 0), .at (.below 32) (.ptr 0), .at (.below 80) (.ret 33), .low (.existential 1)],
      [.fixed 24, .low]⟩
    ⟨85, 2, [(.rdx, .receiver)],
      [.at (.below 8) (.reg .rbp), .at (.above 8) (.reg .rax), .at (.above 16) (.reg .rbx), .at (.above 32) (.reg .rdi), .at (.below 72) (.existential 0), .at (.below 32) (.ptr 1), .at (.below 80) (.ret 69), .low (.existential 1)],
      [.fixed 24, .low]⟩ := by
  intro h; rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Field 3 `Amount` (u64): boundary state 2 (directive 85) → boundary state 3 (directive 88). -/
theorem Decode.example_f3 : ∀ (k : Nat) (hk : Code.unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh Code.unmarshalSSZ k)
    (kS : Nat) (hkS : Prysm.Slot.Code.unmarshalSSZ.IsInfixAt Host.prog kS) (hfS : LabelsFresh Prysm.Slot.Code.unmarshalSSZ kS)
    (pk wc amt sig sl : List UInt8) (hpk : pk.length = 48) (hwc : wc.length = 32) (hamt : amt.length = 8) (hsig : sig.length = 96) (hsl : sl.length = 8)
    (s : MachineData) (ra guard : UInt64)
    (fp s1 s2 s4 sp0 sp1 sp2 l28 rslot lo ast aP0 aL0 aC0 aP1 aL1 aC1 aN2 aP3 aL3 aC3 aN4 : List UInt8)
    (hfp : fp.length = 8) (hs1 : s1.length = 8) (hs2 : s2.length = 8) (hs4 : s4.length = 8) (hsp0 : sp0.length = 8) (hsp1 : sp1.length = 8) (hsp2 : sp2.length = 8) (hl28 : l28.length = 8) (hrslot : rslot.length = 8) (hast : ast.length = 8) (haP0 : aP0.length = 8) (haL0 : aL0.length = 8) (haC0 : aC0.length = 8) (haP1 : aP1.length = 8) (haL1 : aL1.length = 8) (haC1 : aC1.length = 8) (haN2 : aN2.length = 8) (haP3 : aP3.length = 8) (haL3 : aL3.length = 8) (haC3 : aC3.length = 8) (haN4 : aN4.length = 8)
    (R : DataMem → Prop) (S : Nat) (hS : S < 2 ^ 60) (hlo : lo.length = S + 8)
    (Heap : Nat → DataMem → Prop) (avail : Nat)
    (hguard : guard.toNat + 80 < s.regs.rsp.toNat) (hav : 176 ≤ avail)
    (hms : MakesliceContract Heap ElfData.PrysmTarget.typeUint8_addr 1 (S + 8)) (hmm : MemmoveContract (S + 8)) (st0 : MachineState),
    (st0.pc = Host.addrOf (k + 85)
        ∧ st0.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - 72 }
        ∧ st0.data.regs.rbp = { toBitVec := s.regs.rsp.toBitVec - 8 }
        ∧ st0.data.regs.r14 = s.regs.r14
        ∧ st0.data.regs.get64 Reg64.rdx = s.regs.rax.toBitVec ∧
        ∃ (p1 p2 : BitVec 64) (x0 x1 : List UInt8), x0.length = 24 ∧ x1.length = S + 8 ∧ 
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec + 32))
          ⋆ Eq (x0.At (s.regs.rsp.toBitVec - 72))
          ⋆ Eq ((Int.toBytes 8 p2.toInt).At (s.regs.rsp.toBitVec - 32))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 69)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 80))
          ⋆ Eq (x1.At (s.regs.rsp.toBitVec - 88 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Heap (avail - 80)
          ⋆ Eq (pk.At s.regs.rbx.toBitVec)
          ⋆ Eq (wc.At (s.regs.rbx.toBitVec + 48))
          ⋆ Eq (amt.At (s.regs.rbx.toBitVec + 80))
          ⋆ Eq (sig.At (s.regs.rbx.toBitVec + 88))
          ⋆ Eq (sl.At (s.regs.rbx.toBitVec + 184))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 48).At (s.regs.rax.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 48).At (s.regs.rax.toBitVec + 24))
          ⋆ Eq ((Int.toBytes 8 p2.toInt).At (s.regs.rax.toBitVec + 32))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 40))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 48))
          ⋆ Eq (aN2.At (s.regs.rax.toBitVec + 56))
          ⋆ Eq (aP3.At (s.regs.rax.toBitVec + 64))
          ⋆ Eq (aL3.At (s.regs.rax.toBitVec + 72))
          ⋆ Eq (aC3.At (s.regs.rax.toBitVec + 80))
          ⋆ Eq (aN4.At (s.regs.rax.toBitVec + 88))
          ⋆ Eq (pk.At p1)
          ⋆ Eq (wc.At p2)
          ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec)
          ⋆ R) st0.data.dmem) →
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 88)
        ∧ st.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - 72 }
        ∧ st.data.regs.rbp = { toBitVec := s.regs.rsp.toBitVec - 8 }
        ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ (p1 p2 : BitVec 64) (x0 x1 : List UInt8), x0.length = 24 ∧ x1.length = S + 8 ∧ 
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec + 32))
          ⋆ Eq (x0.At (s.regs.rsp.toBitVec - 72))
          ⋆ Eq ((Int.toBytes 8 p2.toInt).At (s.regs.rsp.toBitVec - 32))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 69)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 80))
          ⋆ Eq (x1.At (s.regs.rsp.toBitVec - 88 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Heap (avail - 80)
          ⋆ Eq (pk.At s.regs.rbx.toBitVec)
          ⋆ Eq (wc.At (s.regs.rbx.toBitVec + 48))
          ⋆ Eq (amt.At (s.regs.rbx.toBitVec + 80))
          ⋆ Eq (sig.At (s.regs.rbx.toBitVec + 88))
          ⋆ Eq (sl.At (s.regs.rbx.toBitVec + 184))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 48).At (s.regs.rax.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 48).At (s.regs.rax.toBitVec + 24))
          ⋆ Eq ((Int.toBytes 8 p2.toInt).At (s.regs.rax.toBitVec + 32))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 40))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 48))
          ⋆ Eq (amt.At (s.regs.rax.toBitVec + 56))
          ⋆ Eq (aP3.At (s.regs.rax.toBitVec + 64))
          ⋆ Eq (aL3.At (s.regs.rax.toBitVec + 72))
          ⋆ Eq (aC3.At (s.regs.rax.toBitVec + 80))
          ⋆ Eq (aN4.At (s.regs.rax.toBitVec + 88))
          ⋆ Eq (pk.At p1)
          ⋆ Eq (wc.At p2)
          ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec)
          ⋆ R) st.data.dmem)
      st0 := by
  intro k hk hf kS hkS hfS pk wc amt sig sl hpk hwc hamt hsig hsl s ra guard fp s1 s2 s4 sp0 sp1 sp2 l28 rslot lo ast aP0 aL0 aC0 aP1 aL1 aC1 aN2 aP3 aL3 aC3 aN4 hfp hs1 hs2 hs4 hsp0 hsp1 hsp2 hl28 hrslot hast haP0 haL0 haC0 haP1 haL1 haC1 haN2 haP3 haL3 haC3 haN4 R S hS hlo Heap avail hguard hav hms hmm
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at hguard ⊢
  rintro ⟨d, pc⟩ ⟨hpc, hrsp, hrbp, hr14, hrrdx, p1, p2, x0, x1, hx0, hx1, Hm⟩
  dsimp only at hpc hrsp hrbp hr14 hrrdx Hm
  subst hpc
  obtain ⟨⟨rax1, rbx1, rcx1, rdx1, rsi1, rdi1, rsp1, rbp1, r81, r91, r101, r111, r121, r131, r141, r151⟩, zmms1, flags1, mem1⟩ := d
  simp only [Reg64s.get64] at hrsp hrbp hr14 hrrdx Hm
  subst rsp1 rbp1 r141
  obtain rfl : rax = rdx1 := (UInt64.toBitVec_inj.mp hrrdx).symm
  apply Decode.generated_step_s85 k hk hf (rsp.toBitVec - 72) (rsp.toBitVec + 16) rbx.toBitVec (by simp only [Int64.toBitVec_ofNat] <;> bv_omega) _ _ _ (by rfl) (by ecancel)
  normalize_registers
  apply Decode.generated_step_s86 k hk hf rbx.toBitVec (rbx.toBitVec + 80) (by simp only [Int64.toBitVec_ofNat] <;> bv_omega) amt hamt _ _ _ (by rfl) (by ecancel)
  normalize_registers
  apply Decode.generated_step_s87 k hk hf rax.toBitVec (rax.toBitVec + 56) (by simp only [Int64.toBitVec_ofNat] <;> bv_omega) aN2 haN2 _ _ _
    (by rfl) (by ecancel)
  intro m' H
  normalize_registers
  simp only [Reg64s.get64, toBytes_ofInt_ofBytes 64 8 rfl amt hamt] at H
  apply Eventually.done
  refine ⟨rfl, rfl, rfl, rfl, p1, p2, x0, x1, hx0, hx1, ?_⟩
  dsimp only
  ecancel
theorem Decode.example_f3_kind : ∀ (h : Host), type_of% (@Decode.example_f3 h)
    = @Codec.decFieldKindAnyFrame h Code.unmarshalSSZ (Codec.layoutMixedFrame40 [Prysm.Slot.Code.unmarshalSSZ] 131 2) [.bytes 48, .bytes 32, .u64, .bytes 96, .u64]
    ⟨85, 2, [(.rdx, .receiver)],
      [.at (.below 8) (.reg .rbp), .at (.above 8) (.reg .rax), .at (.above 16) (.reg .rbx), .at (.above 32) (.reg .rdi), .at (.below 72) (.existential 0), .at (.below 32) (.ptr 1), .at (.below 80) (.ret 69), .low (.existential 1)],
      [.fixed 24, .low]⟩
    ⟨88, 3, [],
      [.at (.below 8) (.reg .rbp), .at (.above 8) (.reg .rax), .at (.above 16) (.reg .rbx), .at (.above 32) (.reg .rdi), .at (.below 72) (.existential 0), .at (.below 32) (.ptr 1), .at (.below 80) (.ret 69), .low (.existential 1)],
      [.fixed 24, .low]⟩ := by
  intro h; rfl

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
/-- Field 4 `Signature` (bytes): boundary state 3 (directive 88) → boundary state 4 (directive 123). -/
theorem Decode.example_f4 : ∀ (k : Nat) (hk : Code.unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh Code.unmarshalSSZ k)
    (kS : Nat) (hkS : Prysm.Slot.Code.unmarshalSSZ.IsInfixAt Host.prog kS) (hfS : LabelsFresh Prysm.Slot.Code.unmarshalSSZ kS)
    (pk wc amt sig sl : List UInt8) (hpk : pk.length = 48) (hwc : wc.length = 32) (hamt : amt.length = 8) (hsig : sig.length = 96) (hsl : sl.length = 8)
    (s : MachineData) (ra guard : UInt64)
    (fp s1 s2 s4 sp0 sp1 sp2 l28 rslot lo ast aP0 aL0 aC0 aP1 aL1 aC1 aN2 aP3 aL3 aC3 aN4 : List UInt8)
    (hfp : fp.length = 8) (hs1 : s1.length = 8) (hs2 : s2.length = 8) (hs4 : s4.length = 8) (hsp0 : sp0.length = 8) (hsp1 : sp1.length = 8) (hsp2 : sp2.length = 8) (hl28 : l28.length = 8) (hrslot : rslot.length = 8) (hast : ast.length = 8) (haP0 : aP0.length = 8) (haL0 : aL0.length = 8) (haC0 : aC0.length = 8) (haP1 : aP1.length = 8) (haL1 : aL1.length = 8) (haC1 : aC1.length = 8) (haN2 : aN2.length = 8) (haP3 : aP3.length = 8) (haL3 : aL3.length = 8) (haC3 : aC3.length = 8) (haN4 : aN4.length = 8)
    (R : DataMem → Prop) (S : Nat) (hS : S < 2 ^ 60) (hlo : lo.length = S + 8)
    (Heap : Nat → DataMem → Prop) (avail : Nat)
    (hguard : guard.toNat + 80 < s.regs.rsp.toNat) (hav : 176 ≤ avail)
    (hms : MakesliceContract Heap ElfData.PrysmTarget.typeUint8_addr 1 (S + 8)) (hmm : MemmoveContract (S + 8)) (st0 : MachineState),
    (st0.pc = Host.addrOf (k + 88)
        ∧ st0.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - 72 }
        ∧ st0.data.regs.rbp = { toBitVec := s.regs.rsp.toBitVec - 8 }
        ∧ st0.data.regs.r14 = s.regs.r14 ∧
        ∃ (p1 p2 : BitVec 64) (x0 x1 : List UInt8), x0.length = 24 ∧ x1.length = S + 8 ∧ 
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec + 32))
          ⋆ Eq (x0.At (s.regs.rsp.toBitVec - 72))
          ⋆ Eq ((Int.toBytes 8 p2.toInt).At (s.regs.rsp.toBitVec - 32))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 69)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 80))
          ⋆ Eq (x1.At (s.regs.rsp.toBitVec - 88 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Heap (avail - 80)
          ⋆ Eq (pk.At s.regs.rbx.toBitVec)
          ⋆ Eq (wc.At (s.regs.rbx.toBitVec + 48))
          ⋆ Eq (amt.At (s.regs.rbx.toBitVec + 80))
          ⋆ Eq (sig.At (s.regs.rbx.toBitVec + 88))
          ⋆ Eq (sl.At (s.regs.rbx.toBitVec + 184))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 48).At (s.regs.rax.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 48).At (s.regs.rax.toBitVec + 24))
          ⋆ Eq ((Int.toBytes 8 p2.toInt).At (s.regs.rax.toBitVec + 32))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 40))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 48))
          ⋆ Eq (amt.At (s.regs.rax.toBitVec + 56))
          ⋆ Eq (aP3.At (s.regs.rax.toBitVec + 64))
          ⋆ Eq (aL3.At (s.regs.rax.toBitVec + 72))
          ⋆ Eq (aC3.At (s.regs.rax.toBitVec + 80))
          ⋆ Eq (aN4.At (s.regs.rax.toBitVec + 88))
          ⋆ Eq (pk.At p1)
          ⋆ Eq (wc.At p2)
          ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec)
          ⋆ R) st0.data.dmem) →
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 123)
        ∧ st.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - 72 }
        ∧ st.data.regs.rbp = { toBitVec := s.regs.rsp.toBitVec - 8 }
        ∧ st.data.regs.r14 = s.regs.r14
        ∧ st.data.regs.get64 Reg64.rax = s.regs.rax.toBitVec ∧
        ∃ (p1 p2 p3 : BitVec 64) (x0 x1 : List UInt8), x0.length = 24 ∧ x1.length = S + 8 ∧ 
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec + 32))
          ⋆ Eq (x0.At (s.regs.rsp.toBitVec - 72))
          ⋆ Eq ((Int.toBytes 8 p3.toInt).At (s.regs.rsp.toBitVec - 32))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 108)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 80))
          ⋆ Eq (x1.At (s.regs.rsp.toBitVec - 88 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Heap (avail - 176)
          ⋆ Eq (pk.At s.regs.rbx.toBitVec)
          ⋆ Eq (wc.At (s.regs.rbx.toBitVec + 48))
          ⋆ Eq (amt.At (s.regs.rbx.toBitVec + 80))
          ⋆ Eq (sig.At (s.regs.rbx.toBitVec + 88))
          ⋆ Eq (sl.At (s.regs.rbx.toBitVec + 184))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 48).At (s.regs.rax.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 48).At (s.regs.rax.toBitVec + 24))
          ⋆ Eq ((Int.toBytes 8 p2.toInt).At (s.regs.rax.toBitVec + 32))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 40))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 48))
          ⋆ Eq (amt.At (s.regs.rax.toBitVec + 56))
          ⋆ Eq ((Int.toBytes 8 p3.toInt).At (s.regs.rax.toBitVec + 64))
          ⋆ Eq ((Int.toBytes 8 96).At (s.regs.rax.toBitVec + 72))
          ⋆ Eq ((Int.toBytes 8 96).At (s.regs.rax.toBitVec + 80))
          ⋆ Eq (aN4.At (s.regs.rax.toBitVec + 88))
          ⋆ Eq (pk.At p1)
          ⋆ Eq (wc.At p2)
          ⋆ Eq (sig.At p3)
          ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec)
          ⋆ R) st.data.dmem)
      st0 := by
  intro k hk hf kS hkS hfS pk wc amt sig sl hpk hwc hamt hsig hsl s ra guard fp s1 s2 s4 sp0 sp1 sp2 l28 rslot lo ast aP0 aL0 aC0 aP1 aL1 aC1 aN2 aP3 aL3 aC3 aN4 hfp hs1 hs2 hs4 hsp0 hsp1 hsp2 hl28 hrslot hast haP0 haL0 haC0 haP1 haL1 haC1 haN2 haP3 haL3 haC3 haN4 R S hS hlo Heap avail hguard hav hms hmm
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at hguard ⊢
  rintro ⟨d, pc⟩ ⟨hpc, hrsp, hrbp, hr14, p1, p2, x0, x1, hx0, hx1, Hm⟩
  dsimp only at hpc hrsp hrbp hr14  Hm
  subst hpc
  refine eventually_trans _ _ _ _ (Decode.generated_step_Signature_seg k hk hf (rsp.toBitVec - 72) rax.toBitVec rbx.toBitVec
    (rsp.toBitVec + 8) (rsp.toBitVec + 16) (rsp.toBitVec - 32) (rsp.toBitVec - 80)
    (rsp.toBitVec - 88 - BitVec.ofNat 64 S) (rax.toBitVec + 64) (rax.toBitVec + 72) (rax.toBitVec + 80) (rbx.toBitVec + 88) (S + 8)
    (by simp only [Int64.toBitVec_ofNat] <;> bv_omega) (by simp only [Int64.toBitVec_ofNat] <;> bv_omega) (by simp only [Int64.toBitVec_ofNat] <;> bv_omega) (by bv_omega) (frame_low_address_with_calls _ 72 88 S (by decide))
    (by simp only [Int64.toBitVec_ofNat] <;> bv_omega) (by simp only [Int64.toBitVec_ofNat] <;> bv_omega) (by simp only [Int64.toBitVec_ofNat] <;> bv_omega) (by simp only [Int64.toBitVec_ofNat] <;> bv_omega)
    { toBitVec := rsp.toBitVec - 8#64 } r14 sig hsig
    x0 (Int.toBytes 8 (Host.addrOf (k + 69)).toBitVec.toInt) x1 (Int.toBytes 8 p2.toInt) aP3 aL3 aC3
    hx0 (Int.toBytes_length 8 _) hx1 (Int.toBytes_length 8 _) haP3 haL3 haC3
    _ Heap (avail - 80) (by omega) d hrsp hrbp hr14
      (by ecancel) hms hmm) ?_
  rintro ⟨d', pc'⟩ ⟨hpc', hrsp', hrbp', hr14', p3, spl', lo', hspl', hlo', hrY, Hm'⟩
  dsimp only at hpc' hrsp' hrbp' hr14' hrY Hm'
  subst hpc'
  obtain ⟨⟨rax2, rbx2, rcx2, rdx2, rsi2, rdi2, rsp2, rbp2, r82, r92, r102, r112, r122, r132, r142, r152⟩, zmms2, flags2, mem2⟩ := d'
  simp only at hrsp' hrbp' hr14' hrY Hm'
  subst rsp2 rbp2 r142
  apply Decode.generated_step_s113 k hk hf (rsp.toBitVec - 72) (rsp.toBitVec - 32) p3 (by simp only [Int64.toBitVec_ofNat] <;> bv_omega) _ _ _ (by rfl) (by ecancel)
  normalize_registers
  apply Decode.generated_step_s114 k hk hf
  apply Decode.generated_step_s121 k hk hf
  apply Decode.generated_step_s122 k hk hf rax.toBitVec (rax.toBitVec + 64) (by simp only [Int64.toBitVec_ofNat] <;> bv_omega) (Int.toBytes 8 p3.toInt) (Int.toBytes_length 8 _) _ _ _
    (by exact hrY) (by ecancel)
  intro m' H
  normalize_registers
  simp only [Reg64s.get64] at H
  apply Eventually.done
  refine ⟨rfl, rfl, rfl, rfl, hrY, p1, p2, p3, spl', lo', hspl', hlo', ?_⟩
  dsimp only
  rw [show k + 107 + 1 = k + 108 from rfl] at H
  rw [show avail - 80 - 96 = avail - 176 by omega] at H
  ecancel
theorem Decode.example_f4_kind : ∀ (h : Host), type_of% (@Decode.example_f4 h)
    = @Codec.decFieldKindAnyFrame h Code.unmarshalSSZ (Codec.layoutMixedFrame40 [Prysm.Slot.Code.unmarshalSSZ] 131 2) [.bytes 48, .bytes 32, .u64, .bytes 96, .u64]
    ⟨88, 3, [],
      [.at (.below 8) (.reg .rbp), .at (.above 8) (.reg .rax), .at (.above 16) (.reg .rbx), .at (.above 32) (.reg .rdi), .at (.below 72) (.existential 0), .at (.below 32) (.ptr 1), .at (.below 80) (.ret 69), .low (.existential 1)],
      [.fixed 24, .low]⟩
    ⟨123, 4, [(.rax, .receiver)],
      [.at (.below 8) (.reg .rbp), .at (.above 8) (.reg .rax), .at (.above 16) (.reg .rbx), .at (.above 32) (.reg .rdi), .at (.below 72) (.existential 0), .at (.below 32) (.ptr 2), .at (.below 80) (.ret 108), .low (.existential 1)],
      [.fixed 24, .low]⟩ := by
  intro h; rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Field 5 `Slot` (call): boundary state 4 (directive 123) → boundary state 5 (directive 161). -/
theorem Decode.example_f5 : ∀ (k : Nat) (hk : Code.unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh Code.unmarshalSSZ k)
    (kS : Nat) (hkS : Prysm.Slot.Code.unmarshalSSZ.IsInfixAt Host.prog kS) (hfS : LabelsFresh Prysm.Slot.Code.unmarshalSSZ kS)
    (pk wc amt sig sl : List UInt8) (hpk : pk.length = 48) (hwc : wc.length = 32) (hamt : amt.length = 8) (hsig : sig.length = 96) (hsl : sl.length = 8)
    (s : MachineData) (ra guard : UInt64)
    (fp s1 s2 s4 sp0 sp1 sp2 l28 rslot lo ast aP0 aL0 aC0 aP1 aL1 aC1 aN2 aP3 aL3 aC3 aN4 : List UInt8)
    (hfp : fp.length = 8) (hs1 : s1.length = 8) (hs2 : s2.length = 8) (hs4 : s4.length = 8) (hsp0 : sp0.length = 8) (hsp1 : sp1.length = 8) (hsp2 : sp2.length = 8) (hl28 : l28.length = 8) (hrslot : rslot.length = 8) (hast : ast.length = 8) (haP0 : aP0.length = 8) (haL0 : aL0.length = 8) (haC0 : aC0.length = 8) (haP1 : aP1.length = 8) (haL1 : aL1.length = 8) (haC1 : aC1.length = 8) (haN2 : aN2.length = 8) (haP3 : aP3.length = 8) (haL3 : aL3.length = 8) (haC3 : aC3.length = 8) (haN4 : aN4.length = 8)
    (R : DataMem → Prop) (S : Nat) (hS : S < 2 ^ 60) (hlo : lo.length = S + 8)
    (Heap : Nat → DataMem → Prop) (avail : Nat)
    (hguard : guard.toNat + 80 < s.regs.rsp.toNat) (hav : 176 ≤ avail)
    (hms : MakesliceContract Heap ElfData.PrysmTarget.typeUint8_addr 1 (S + 8)) (hmm : MemmoveContract (S + 8)) (st0 : MachineState),
    (st0.pc = Host.addrOf (k + 123)
        ∧ st0.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - 72 }
        ∧ st0.data.regs.rbp = { toBitVec := s.regs.rsp.toBitVec - 8 }
        ∧ st0.data.regs.r14 = s.regs.r14
        ∧ st0.data.regs.get64 Reg64.rax = s.regs.rax.toBitVec ∧
        ∃ (p1 p2 p3 : BitVec 64) (x0 x1 : List UInt8), x0.length = 24 ∧ x1.length = S + 8 ∧ 
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec + 32))
          ⋆ Eq (x0.At (s.regs.rsp.toBitVec - 72))
          ⋆ Eq ((Int.toBytes 8 p3.toInt).At (s.regs.rsp.toBitVec - 32))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 108)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 80))
          ⋆ Eq (x1.At (s.regs.rsp.toBitVec - 88 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Heap (avail - 176)
          ⋆ Eq (pk.At s.regs.rbx.toBitVec)
          ⋆ Eq (wc.At (s.regs.rbx.toBitVec + 48))
          ⋆ Eq (amt.At (s.regs.rbx.toBitVec + 80))
          ⋆ Eq (sig.At (s.regs.rbx.toBitVec + 88))
          ⋆ Eq (sl.At (s.regs.rbx.toBitVec + 184))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 48).At (s.regs.rax.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 48).At (s.regs.rax.toBitVec + 24))
          ⋆ Eq ((Int.toBytes 8 p2.toInt).At (s.regs.rax.toBitVec + 32))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 40))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 48))
          ⋆ Eq (amt.At (s.regs.rax.toBitVec + 56))
          ⋆ Eq ((Int.toBytes 8 p3.toInt).At (s.regs.rax.toBitVec + 64))
          ⋆ Eq ((Int.toBytes 8 96).At (s.regs.rax.toBitVec + 72))
          ⋆ Eq ((Int.toBytes 8 96).At (s.regs.rax.toBitVec + 80))
          ⋆ Eq (aN4.At (s.regs.rax.toBitVec + 88))
          ⋆ Eq (pk.At p1)
          ⋆ Eq (wc.At p2)
          ⋆ Eq (sig.At p3)
          ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec)
          ⋆ R) st0.data.dmem) →
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 161)
        ∧ st.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - 72 }
        ∧ st.data.regs.rbp = { toBitVec := s.regs.rsp.toBitVec - 8 }
        ∧ st.data.regs.r14 = s.regs.r14
        ∧ st.data.regs.get64 Reg64.rax = 0
        ∧ st.data.regs.get64 Reg64.rbx = 0 ∧
        ∃ (p1 p2 p3 : BitVec 64) (x0 x1 : List UInt8), x0.length = 24 ∧ x1.length = S + 8 ∧ 
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec + 32))
          ⋆ Eq (x0.At (s.regs.rsp.toBitVec - 72))
          ⋆ Eq ((Int.toBytes 8 p3.toInt).At (s.regs.rsp.toBitVec - 32))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 131)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 80))
          ⋆ Eq (x1.At (s.regs.rsp.toBitVec - 88 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Heap (avail - 176)
          ⋆ Eq (pk.At s.regs.rbx.toBitVec)
          ⋆ Eq (wc.At (s.regs.rbx.toBitVec + 48))
          ⋆ Eq (amt.At (s.regs.rbx.toBitVec + 80))
          ⋆ Eq (sig.At (s.regs.rbx.toBitVec + 88))
          ⋆ Eq (sl.At (s.regs.rbx.toBitVec + 184))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 48).At (s.regs.rax.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 48).At (s.regs.rax.toBitVec + 24))
          ⋆ Eq ((Int.toBytes 8 p2.toInt).At (s.regs.rax.toBitVec + 32))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 40))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 48))
          ⋆ Eq (amt.At (s.regs.rax.toBitVec + 56))
          ⋆ Eq ((Int.toBytes 8 p3.toInt).At (s.regs.rax.toBitVec + 64))
          ⋆ Eq ((Int.toBytes 8 96).At (s.regs.rax.toBitVec + 72))
          ⋆ Eq ((Int.toBytes 8 96).At (s.regs.rax.toBitVec + 80))
          ⋆ Eq (sl.At (s.regs.rax.toBitVec + 88))
          ⋆ Eq (pk.At p1)
          ⋆ Eq (wc.At p2)
          ⋆ Eq (sig.At p3)
          ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec)
          ⋆ R) st.data.dmem)
      st0 := by
  intro k hk hf kS hkS hfS pk wc amt sig sl hpk hwc hamt hsig hsl s ra guard fp s1 s2 s4 sp0 sp1 sp2 l28 rslot lo ast aP0 aL0 aC0 aP1 aL1 aC1 aN2 aP3 aL3 aC3 aN4 hfp hs1 hs2 hs4 hsp0 hsp1 hsp2 hl28 hrslot hast haP0 haL0 haC0 haP1 haL1 haC1 haN2 haP3 haL3 haC3 haN4 R S hS hlo Heap avail hguard hav hms hmm
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at hguard ⊢
  rintro ⟨d, pc⟩ ⟨hpc, hrsp, hrbp, hr14, hrrax, p1, p2, p3, x0, x1, hx0, hx1, Hm⟩
  dsimp only at hpc hrsp hrbp hr14 hrrax Hm
  subst hpc
  obtain ⟨⟨rax1, rbx1, rcx1, rdx1, rsi1, rdi1, rsp1, rbp1, r81, r91, r101, r111, r121, r131, r141, r151⟩, zmms1, flags1, mem1⟩ := d
  simp only [Reg64s.get64] at hrsp hrbp hr14 hrrax Hm
  subst rsp1 rbp1 r141
  obtain rfl : rax = rax1 := (UInt64.toBitVec_inj.mp hrrax).symm
  have hC := Prysm.Slot.Decode.accept_function_spec_holds kS hkS hfS
  have hg : guard.toNat < (rsp.toBitVec - 80).toNat := by
    have hgd : guard.toNat + 80 < rsp.toBitVec.toNat := hguard
    bv_omega
  have hq0 : (x0.take 8).length = 8 := by simp [hx0]
  have hq1 : ((x0.drop 8).take 8).length = 8 := by simp [hx0]
  have hq2 : ((x0.drop 8).drop 8).length = 8 := by simp [hx0]
  have hXs : x0 = x0.take 8 ++ ((x0.drop 8).take 8 ++ (x0.drop 8).drop 8) := by
    rw [List.take_append_drop, List.take_append_drop]
  have hlS : (x1.take S).length = S := by simp [hx1]
  have hl8 : (x1.drop S).length = 8 := by simp [hx1]
  have hLs : x1 = x1.take S ++ x1.drop S := (List.take_append_drop S x1).symm
  rw [hXs, hLs, frame_join_three_words (rsp.toBitVec - 72) (rsp.toBitVec - 64) (rsp.toBitVec - 56) _ _ _ hq0 hq1 hq2 (by bv_omega) (by bv_omega), frame_low_stack_split (rsp.toBitVec - 88) S hS _ _ hlS hl8] at Hm
  apply Decode.generated_step_s123 k hk hf (rsp.toBitVec - 72) (rsp.toBitVec + 16) rbx.toBitVec (by simp only [Int64.toBitVec_ofNat] <;> bv_omega) _ _ _ (by rfl) (by ecancel)
  normalize_registers
  apply Decode.generated_step_s124 k hk hf
  intro fl124; normalize_registers
  apply Decode.generated_step_s125 k hk hf (rsp.toBitVec - 72) (rsp.toBitVec + 32) (by simp only [Int64.toBitVec_ofNat] <;> bv_omega) (Int.toBytes 8 rdi.toBitVec.toInt) (Int.toBytes_length 8 _) _ _ _ (by rfl) (by ecancel)
  normalize_registers
  apply Decode.generated_step_s126 k hk hf
  intro fl126; normalize_registers
  apply Decode.generated_step_s127 k hk hf
  intro fl127; normalize_registers
  apply Decode.generated_step_s128 k hk hf
  normalize_registers
  refine eventually_trans _ _ _ _ (Decode.generated_step_Slot_call k hk hf hC (rsp.toBitVec - 72) (rax.toBitVec + 88) (rbx.toBitVec + 184)
    (rsp.toBitVec - 80) (rsp.toBitVec - 88) (rsp.toBitVec - 64) (by bv_omega) (by bv_omega) (by bv_omega)
    { toBitVec := rsp.toBitVec - 8#64 } r14 guard sl (Int.toBytes 8 (Host.addrOf (k + 108)).toBitVec.toInt) (x1.drop S) ((x0.drop 8).take 8) aN4
    hsl (Int.toBytes_length 8 _) hl8 hq1 haN4 hg _ _
    (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by first | rfl | decide) (by ecancel)) ?_
  rintro ⟨d', pc'⟩ ⟨hpc', hrax', hrbx', hrsp', hrbp', hr14', Hm'⟩
  dsimp only at hpc' hrax' hrbx' hrsp' hrbp' hr14' Hm'
  apply Eventually.done
  refine ⟨hpc', hrsp', hrbp', hr14', (congrArg UInt64.toBitVec hrax'), (congrArg UInt64.toBitVec hrbx'), p1, p2, p3, (x0.take 8 ++ (Int.toBytes 8 (rbx.toBitVec + 184).toInt ++ (x0.drop 8).drop 8)), (x1.take S ++ Int.toBytes 8 (rsp.toBitVec - 8#64).toInt),
    (by simp only [List.length_append, hq0, hq2, Int.toBytes_length]), (by simp only [List.length_append, hlS, Int.toBytes_length]), ?_⟩
  dsimp only
  rw [frame_join_three_words (rsp.toBitVec - 72) (rsp.toBitVec - 64) (rsp.toBitVec - 56) _ _ _ hq0 (Int.toBytes_length 8 _) hq2 (by bv_omega) (by bv_omega), frame_low_stack_split (rsp.toBitVec - 88) S hS _ _ hlS (Int.toBytes_length 8 _)]
  rw [show k + 130 + 1 = k + 131 from rfl] at Hm'
  ecancel
theorem Decode.example_f5_kind : ∀ (h : Host), type_of% (@Decode.example_f5 h)
    = @Codec.decFieldKindAnyFrame h Code.unmarshalSSZ (Codec.layoutMixedFrame40 [Prysm.Slot.Code.unmarshalSSZ] 131 2) [.bytes 48, .bytes 32, .u64, .bytes 96, .u64]
    ⟨123, 4, [(.rax, .receiver)],
      [.at (.below 8) (.reg .rbp), .at (.above 8) (.reg .rax), .at (.above 16) (.reg .rbx), .at (.above 32) (.reg .rdi), .at (.below 72) (.existential 0), .at (.below 32) (.ptr 2), .at (.below 80) (.ret 108), .low (.existential 1)],
      [.fixed 24, .low]⟩
    ⟨161, 5, [(.rax, .zero), (.rbx, .zero)],
      [.at (.below 8) (.reg .rbp), .at (.above 8) (.reg .rax), .at (.above 16) (.reg .rbx), .at (.above 32) (.reg .rdi), .at (.below 72) (.existential 0), .at (.below 32) (.ptr 2), .at (.below 80) (.ret 131), .low (.existential 1)],
      [.fixed 24, .low]⟩ := by
  intro h; rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Epilogue: boundary state 5 (directive 161) → return. -/
theorem Decode.example_epi : ∀ (k : Nat) (hk : Code.unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh Code.unmarshalSSZ k)
    (kS : Nat) (hkS : Prysm.Slot.Code.unmarshalSSZ.IsInfixAt Host.prog kS) (hfS : LabelsFresh Prysm.Slot.Code.unmarshalSSZ kS)
    (pk wc amt sig sl : List UInt8) (hpk : pk.length = 48) (hwc : wc.length = 32) (hamt : amt.length = 8) (hsig : sig.length = 96) (hsl : sl.length = 8)
    (s : MachineData) (ra guard : UInt64)
    (fp s1 s2 s4 sp0 sp1 sp2 l28 rslot lo ast aP0 aL0 aC0 aP1 aL1 aC1 aN2 aP3 aL3 aC3 aN4 : List UInt8)
    (hfp : fp.length = 8) (hs1 : s1.length = 8) (hs2 : s2.length = 8) (hs4 : s4.length = 8) (hsp0 : sp0.length = 8) (hsp1 : sp1.length = 8) (hsp2 : sp2.length = 8) (hl28 : l28.length = 8) (hrslot : rslot.length = 8) (hast : ast.length = 8) (haP0 : aP0.length = 8) (haL0 : aL0.length = 8) (haC0 : aC0.length = 8) (haP1 : aP1.length = 8) (haL1 : aL1.length = 8) (haC1 : aC1.length = 8) (haN2 : aN2.length = 8) (haP3 : aP3.length = 8) (haL3 : aL3.length = 8) (haC3 : aC3.length = 8) (haN4 : aN4.length = 8)
    (R : DataMem → Prop) (S : Nat) (hS : S < 2 ^ 60) (hlo : lo.length = S + 8)
    (Heap : Nat → DataMem → Prop) (avail : Nat)
    (st0 : MachineState),
    (st0.pc = Host.addrOf (k + 161)
        ∧ st0.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - 72 }
        ∧ st0.data.regs.rbp = { toBitVec := s.regs.rsp.toBitVec - 8 }
        ∧ st0.data.regs.r14 = s.regs.r14
        ∧ st0.data.regs.get64 Reg64.rax = 0
        ∧ st0.data.regs.get64 Reg64.rbx = 0 ∧
        ∃ (p1 p2 p3 : BitVec 64) (x0 x1 : List UInt8), x0.length = 24 ∧ x1.length = S + 8 ∧ 
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec + 32))
          ⋆ Eq (x0.At (s.regs.rsp.toBitVec - 72))
          ⋆ Eq ((Int.toBytes 8 p3.toInt).At (s.regs.rsp.toBitVec - 32))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 131)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 80))
          ⋆ Eq (x1.At (s.regs.rsp.toBitVec - 88 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Heap (avail - 176)
          ⋆ Eq (pk.At s.regs.rbx.toBitVec)
          ⋆ Eq (wc.At (s.regs.rbx.toBitVec + 48))
          ⋆ Eq (amt.At (s.regs.rbx.toBitVec + 80))
          ⋆ Eq (sig.At (s.regs.rbx.toBitVec + 88))
          ⋆ Eq (sl.At (s.regs.rbx.toBitVec + 184))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 48).At (s.regs.rax.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 48).At (s.regs.rax.toBitVec + 24))
          ⋆ Eq ((Int.toBytes 8 p2.toInt).At (s.regs.rax.toBitVec + 32))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 40))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 48))
          ⋆ Eq (amt.At (s.regs.rax.toBitVec + 56))
          ⋆ Eq ((Int.toBytes 8 p3.toInt).At (s.regs.rax.toBitVec + 64))
          ⋆ Eq ((Int.toBytes 8 96).At (s.regs.rax.toBitVec + 72))
          ⋆ Eq ((Int.toBytes 8 96).At (s.regs.rax.toBitVec + 80))
          ⋆ Eq (sl.At (s.regs.rax.toBitVec + 88))
          ⋆ Eq (pk.At p1)
          ⋆ Eq (wc.At p2)
          ⋆ Eq (sig.At p3)
          ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec)
          ⋆ R) st0.data.dmem) →
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ (p1 p2 p3 : BitVec 64) (x0 x1 : List UInt8), x0.length = 24 ∧ x1.length = S + 8 ∧ 
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec + 32))
          ⋆ Eq (x0.At (s.regs.rsp.toBitVec - 72))
          ⋆ Eq ((Int.toBytes 8 p3.toInt).At (s.regs.rsp.toBitVec - 32))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 131)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 80))
          ⋆ Eq (x1.At (s.regs.rsp.toBitVec - 88 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Heap (avail - 176)
          ⋆ Eq (pk.At s.regs.rbx.toBitVec)
          ⋆ Eq (wc.At (s.regs.rbx.toBitVec + 48))
          ⋆ Eq (amt.At (s.regs.rbx.toBitVec + 80))
          ⋆ Eq (sig.At (s.regs.rbx.toBitVec + 88))
          ⋆ Eq (sl.At (s.regs.rbx.toBitVec + 184))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 48).At (s.regs.rax.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 48).At (s.regs.rax.toBitVec + 24))
          ⋆ Eq ((Int.toBytes 8 p2.toInt).At (s.regs.rax.toBitVec + 32))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 40))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 48))
          ⋆ Eq (amt.At (s.regs.rax.toBitVec + 56))
          ⋆ Eq ((Int.toBytes 8 p3.toInt).At (s.regs.rax.toBitVec + 64))
          ⋆ Eq ((Int.toBytes 8 96).At (s.regs.rax.toBitVec + 72))
          ⋆ Eq ((Int.toBytes 8 96).At (s.regs.rax.toBitVec + 80))
          ⋆ Eq (sl.At (s.regs.rax.toBitVec + 88))
          ⋆ Eq (pk.At p1)
          ⋆ Eq (wc.At p2)
          ⋆ Eq (sig.At p3)
          ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec)
          ⋆ R) st.data.dmem)
      st0 := by
  intro k hk hf kS hkS hfS pk wc amt sig sl hpk hwc hamt hsig hsl s ra guard fp s1 s2 s4 sp0 sp1 sp2 l28 rslot lo ast aP0 aL0 aC0 aP1 aL1 aC1 aN2 aP3 aL3 aC3 aN4 hfp hs1 hs2 hs4 hsp0 hsp1 hsp2 hl28 hrslot hast haP0 haL0 haC0 haP1 haL1 haC1 haN2 haP3 haL3 haC3 haN4 R S hS hlo Heap avail
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at ⊢
  rintro ⟨d, pc⟩ ⟨hpc, hrsp, hrbp, hr14, hrrax, hrrbx, p1, p2, p3, x0, x1, hx0, hx1, Hm⟩
  dsimp only at hpc hrsp hrbp hr14 hrrax hrrbx Hm
  subst hpc
  obtain ⟨⟨rax1, rbx1, rcx1, rdx1, rsi1, rdi1, rsp1, rbp1, r81, r91, r101, r111, r121, r131, r141, r151⟩, zmms1, flags1, mem1⟩ := d
  simp only [Reg64s.get64] at hrsp hrbp hr14 hrrax hrrbx Hm
  subst rsp1 rbp1 r141
  obtain rfl : (0 : UInt64) = rax1 := (UInt64.toBitVec_inj.mp (show rax1.toBitVec = (0 : UInt64).toBitVec from hrrax)).symm
  obtain rfl : (0 : UInt64) = rbx1 := (UInt64.toBitVec_inj.mp (show rbx1.toBitVec = (0 : UInt64).toBitVec from hrrbx)).symm
  refine eventually_trans _ _ _ _ (decepi_n 64 _ (k + 161) (k + 162) (window_infix_at hk 161 1) (by rfl) (by rfl)
    _ (window_infix_at hk 162 2) (by rfl) (rsp.toBitVec - 72) (rsp.toBitVec - 8) rsp.toBitVec
    (by simp only [Int64.toBitVec_ofNat] <;> bv_omega) (by bv_omega) rbp ra _ _ (by rfl) (by ecancel)) ?_
  rintro ⟨d', pc'⟩ ⟨hpc', hrax', hrbx', hrsp', hrbp', hr14', hmem'⟩
  dsimp only at hpc' hrax' hrbx' hrsp' hrbp' hr14' hmem'
  apply Eventually.done
  refine ⟨hpc', hrax', hrbx', ?_, hrbp', hr14', p1, p2, p3, x0, x1, hx0, hx1, ?_⟩
  · rw [hrsp']; apply UInt64.toBitVec_inj.mp
    first
      | (simp only [UInt64.toBitVec_add, UInt64.toBitVec_ofNat]; done)
      | (simp only [UInt64.toBitVec_add, UInt64.toBitVec_ofNat]; bv_omega)
  · dsimp only; rw [hmem']; ecancel
theorem Decode.example_epi_kind : ∀ (h : Host), type_of% (@Decode.example_epi h)
    = @Codec.decEpilogueKindAnyFrame h Code.unmarshalSSZ (Codec.layoutMixedFrame40 [Prysm.Slot.Code.unmarshalSSZ] 131 2) [.bytes 48, .bytes 32, .u64, .bytes 96, .u64]
    ⟨161, 5, [(.rax, .zero), (.rbx, .zero)],
      [.at (.below 8) (.reg .rbp), .at (.above 8) (.reg .rax), .at (.above 16) (.reg .rbx), .at (.above 32) (.reg .rdi), .at (.below 72) (.existential 0), .at (.below 32) (.ptr 2), .at (.below 80) (.ret 131), .low (.existential 1)],
      [.fixed 24, .low]⟩ := by
  intro h; rfl

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
/-- **Accept path of `(*v1alpha1.PendingDeposit).UnmarshalSSZ` (Go 1.26.10), generated-style proof**: head, one theorem per
field, epilogue, chained by `eventually_trans`. Statement = the kind instance (`_kind`). -/
theorem Decode.example_accept : ∀ (k : Nat) (hk : Code.unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh Code.unmarshalSSZ k)
    (kS : Nat) (hkS : Prysm.Slot.Code.unmarshalSSZ.IsInfixAt Host.prog kS) (hfS : LabelsFresh Prysm.Slot.Code.unmarshalSSZ kS)
    (pk wc amt sig sl : List UInt8) (hpk : pk.length = 48) (hwc : wc.length = 32) (hamt : amt.length = 8) (hsig : sig.length = 96) (hsl : sl.length = 8)
    (s : MachineData) (ra guard : UInt64)
    (fp s1 s2 s4 sp0 sp1 sp2 l28 rslot lo ast aP0 aL0 aC0 aP1 aL1 aC1 aN2 aP3 aL3 aC3 aN4 : List UInt8)
    (hfp : fp.length = 8) (hs1 : s1.length = 8) (hs2 : s2.length = 8) (hs4 : s4.length = 8) (hsp0 : sp0.length = 8) (hsp1 : sp1.length = 8) (hsp2 : sp2.length = 8) (hl28 : l28.length = 8) (hrslot : rslot.length = 8) (hast : ast.length = 8) (haP0 : aP0.length = 8) (haL0 : aL0.length = 8) (haC0 : aC0.length = 8) (haP1 : aP1.length = 8) (haL1 : aL1.length = 8) (haC1 : aC1.length = 8) (haN2 : aN2.length = 8) (haP3 : aP3.length = 8) (haL3 : aL3.length = 8) (haC3 : aC3.length = 8) (haN4 : aN4.length = 8)
    (R : DataMem → Prop) (S : Nat) (hS : S < 2 ^ 60) (hlo : lo.length = S + 8)
    (Heap : Nat → DataMem → Prop) (avail : Nat)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8))
      ⋆ Eq (s1.At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq (s4.At (s.regs.rsp.toBitVec + 32))
      ⋆ Eq (sp0.At (s.regs.rsp.toBitVec - 72))
      ⋆ Eq (sp1.At (s.regs.rsp.toBitVec - 64))
      ⋆ Eq (sp2.At (s.regs.rsp.toBitVec - 56))
      ⋆ Eq (l28.At (s.regs.rsp.toBitVec - 32))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 80))
      ⋆ Eq (lo.At (s.regs.rsp.toBitVec - 88 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Heap avail
      ⋆ Eq (pk.At s.regs.rbx.toBitVec)
      ⋆ Eq (wc.At (s.regs.rbx.toBitVec + 48))
      ⋆ Eq (amt.At (s.regs.rbx.toBitVec + 80))
      ⋆ Eq (sig.At (s.regs.rbx.toBitVec + 88))
      ⋆ Eq (sl.At (s.regs.rbx.toBitVec + 184))
      ⋆ Eq (ast.At s.regs.rax.toBitVec)
      ⋆ Eq (aP0.At (s.regs.rax.toBitVec + 8))
      ⋆ Eq (aL0.At (s.regs.rax.toBitVec + 16))
      ⋆ Eq (aC0.At (s.regs.rax.toBitVec + 24))
      ⋆ Eq (aP1.At (s.regs.rax.toBitVec + 32))
      ⋆ Eq (aL1.At (s.regs.rax.toBitVec + 40))
      ⋆ Eq (aC1.At (s.regs.rax.toBitVec + 48))
      ⋆ Eq (aN2.At (s.regs.rax.toBitVec + 56))
      ⋆ Eq (aP3.At (s.regs.rax.toBitVec + 64))
      ⋆ Eq (aL3.At (s.regs.rax.toBitVec + 72))
      ⋆ Eq (aC3.At (s.regs.rax.toBitVec + 80))
      ⋆ Eq (aN4.At (s.regs.rax.toBitVec + 88))
      ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec)
      ⋆ R)
    (hguard : guard.toNat + 80 < s.regs.rsp.toNat) (hlen : s.regs.rcx = 192) (hav : 176 ≤ avail)
    (hms : MakesliceContract Heap ElfData.PrysmTarget.typeUint8_addr 1 (S + 8)) (hmm : MemmoveContract (S + 8)),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ (p1 p2 p3 : BitVec 64) (x0 x1 : List UInt8), x0.length = 24 ∧ x1.length = S + 8 ∧ 
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec + 32))
          ⋆ Eq (x0.At (s.regs.rsp.toBitVec - 72))
          ⋆ Eq ((Int.toBytes 8 p3.toInt).At (s.regs.rsp.toBitVec - 32))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 131)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 80))
          ⋆ Eq (x1.At (s.regs.rsp.toBitVec - 88 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Heap (avail - 176)
          ⋆ Eq (pk.At s.regs.rbx.toBitVec)
          ⋆ Eq (wc.At (s.regs.rbx.toBitVec + 48))
          ⋆ Eq (amt.At (s.regs.rbx.toBitVec + 80))
          ⋆ Eq (sig.At (s.regs.rbx.toBitVec + 88))
          ⋆ Eq (sl.At (s.regs.rbx.toBitVec + 184))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 48).At (s.regs.rax.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 48).At (s.regs.rax.toBitVec + 24))
          ⋆ Eq ((Int.toBytes 8 p2.toInt).At (s.regs.rax.toBitVec + 32))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 40))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 48))
          ⋆ Eq (amt.At (s.regs.rax.toBitVec + 56))
          ⋆ Eq ((Int.toBytes 8 p3.toInt).At (s.regs.rax.toBitVec + 64))
          ⋆ Eq ((Int.toBytes 8 96).At (s.regs.rax.toBitVec + 72))
          ⋆ Eq ((Int.toBytes 8 96).At (s.regs.rax.toBitVec + 80))
          ⋆ Eq (sl.At (s.regs.rax.toBitVec + 88))
          ⋆ Eq (pk.At p1)
          ⋆ Eq (wc.At p2)
          ⋆ Eq (sig.At p3)
          ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec)
          ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  intro k hk hf kS hkS hfS pk wc amt sig sl hpk hwc hamt hsig hsl s ra guard fp s1 s2 s4 sp0 sp1 sp2 l28 rslot lo ast aP0 aL0 aC0 aP1 aL1 aC1 aN2 aP3 aL3 aC3 aN4 hfp hs1 hs2 hs4 hsp0 hsp1 hsp2 hl28 hrslot hast haP0 haL0 haC0 haP1 haL1 haC1 haN2 haP3 haL3 haC3 haN4 R S hS hlo Heap avail h_mem hguard hlen hav hms hmm
  refine eventually_trans _ _ _ _ (Decode.example_head k hk hf kS hkS hfS pk wc amt sig sl hpk hwc hamt hsig hsl s ra guard fp s1 s2 s4 sp0 sp1 sp2 l28 rslot lo ast aP0 aL0 aC0 aP1 aL1 aC1 aN2 aP3 aL3 aC3 aN4 hfp hs1 hs2 hs4 hsp0 hsp1 hsp2 hl28 hrslot hast haP0 haL0 haC0 haP1 haL1 haC1 haN2 haP3 haL3 haC3 haN4 R S hS hlo Heap avail h_mem hguard hlen hav hms hmm) ?_
  intro st0 h0
  refine eventually_trans _ _ _ _ (Decode.example_f1 k hk hf kS hkS hfS pk wc amt sig sl hpk hwc hamt hsig hsl s ra guard fp s1 s2 s4 sp0 sp1 sp2 l28 rslot lo ast aP0 aL0 aC0 aP1 aL1 aC1 aN2 aP3 aL3 aC3 aN4 hfp hs1 hs2 hs4 hsp0 hsp1 hsp2 hl28 hrslot hast haP0 haL0 haC0 haP1 haL1 haC1 haN2 haP3 haL3 haC3 haN4 R S hS hlo Heap avail hguard hav hms hmm st0 h0) ?_
  intro st1 h1
  refine eventually_trans _ _ _ _ (Decode.example_f2 k hk hf kS hkS hfS pk wc amt sig sl hpk hwc hamt hsig hsl s ra guard fp s1 s2 s4 sp0 sp1 sp2 l28 rslot lo ast aP0 aL0 aC0 aP1 aL1 aC1 aN2 aP3 aL3 aC3 aN4 hfp hs1 hs2 hs4 hsp0 hsp1 hsp2 hl28 hrslot hast haP0 haL0 haC0 haP1 haL1 haC1 haN2 haP3 haL3 haC3 haN4 R S hS hlo Heap avail hguard hav hms hmm st1 h1) ?_
  intro st2 h2
  refine eventually_trans _ _ _ _ (Decode.example_f3 k hk hf kS hkS hfS pk wc amt sig sl hpk hwc hamt hsig hsl s ra guard fp s1 s2 s4 sp0 sp1 sp2 l28 rslot lo ast aP0 aL0 aC0 aP1 aL1 aC1 aN2 aP3 aL3 aC3 aN4 hfp hs1 hs2 hs4 hsp0 hsp1 hsp2 hl28 hrslot hast haP0 haL0 haC0 haP1 haL1 haC1 haN2 haP3 haL3 haC3 haN4 R S hS hlo Heap avail hguard hav hms hmm st2 h2) ?_
  intro st3 h3
  refine eventually_trans _ _ _ _ (Decode.example_f4 k hk hf kS hkS hfS pk wc amt sig sl hpk hwc hamt hsig hsl s ra guard fp s1 s2 s4 sp0 sp1 sp2 l28 rslot lo ast aP0 aL0 aC0 aP1 aL1 aC1 aN2 aP3 aL3 aC3 aN4 hfp hs1 hs2 hs4 hsp0 hsp1 hsp2 hl28 hrslot hast haP0 haL0 haC0 haP1 haL1 haC1 haN2 haP3 haL3 haC3 haN4 R S hS hlo Heap avail hguard hav hms hmm st3 h3) ?_
  intro st4 h4
  refine eventually_trans _ _ _ _ (Decode.example_f5 k hk hf kS hkS hfS pk wc amt sig sl hpk hwc hamt hsig hsl s ra guard fp s1 s2 s4 sp0 sp1 sp2 l28 rslot lo ast aP0 aL0 aC0 aP1 aL1 aC1 aN2 aP3 aL3 aC3 aN4 hfp hs1 hs2 hs4 hsp0 hsp1 hsp2 hl28 hrslot hast haP0 haL0 haC0 haP1 haL1 haC1 haN2 haP3 haL3 haC3 haN4 R S hS hlo Heap avail hguard hav hms hmm st4 h4) ?_
  intro st5 h5
  exact Decode.example_epi k hk hf kS hkS hfS pk wc amt sig sl hpk hwc hamt hsig hsl s ra guard fp s1 s2 s4 sp0 sp1 sp2 l28 rslot lo ast aP0 aL0 aC0 aP1 aL1 aC1 aN2 aP3 aL3 aC3 aN4 hfp hs1 hs2 hs4 hsp0 hsp1 hsp2 hl28 hrslot hast haP0 haL0 haC0 haP1 haL1 haC1 haN2 haP3 haL3 haC3 haN4 R S hS hlo Heap avail st5 h5
theorem Decode.example_accept_kind : ∀ (h : Host), type_of% (@Decode.example_accept h)
    = @Codec.decAcceptKindAnyFrame h Code.unmarshalSSZ (Codec.layoutMixedFrame40 [Prysm.Slot.Code.unmarshalSSZ] 131 2) [.bytes 48, .bytes 32, .u64, .bytes 96, .u64] := by
  intro h; rfl

/-- The generated-style theorem proves the committed hand statement `Prysm.PendingDeposit.Decode.accept_statement` (unchanged). -/
theorem Decode.example_accept_same_statement : Prysm.PendingDeposit.Decode.accept_statement := Decode.example_accept

end Prysm.PendingDeposit
