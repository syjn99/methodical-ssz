import E2eScal.AcceptTies
import E2eScal.FieldComp
import E2eScal.ViSpec
import E2e.Epoch
import E2eAd.Prims
import E2eScal.Gen4SmDec

/-!
# GEN5 worked example: `(*v1alpha1.SyncCommitteeMessage).UnmarshalSSZ`, accept theorem in generated style

Text produced from one description of the type (frame facts, field list, boundary states, chain theorem names)
by the recipe of the G5-L hand-over; every theorem has a `_kind` line (`decHeadKindN`, `decFieldKindN`,
`decEpiKindN`, `decAcceptKindN`). The GEN4 chain theorems (`E2eScal.Gen.*`) are used as emitted.
-/

open Fk E2e E2eAd E2eAd.Code E2eScal.H6Code E2eScal.H5Code E2eScal.BhCode E2eScal
variable [Host]

namespace E2eScal.Gen5

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Head: directives 0–14 (prologue, spills, nil check); entry → boundary state 0. -/
theorem sm_g5_head : ∀ (k : Nat) (hk : SmUnmarshal.IsInfixAt Host.prog k) (hf : LabelsFresh SmUnmarshal k)
    (kS : Nat) (hkS : E2eAd.Code.SlUnmarshal.IsInfixAt Host.prog kS) (hfS : LabelsFresh E2eAd.Code.SlUnmarshal kS)
    (kV : Nat) (hkV : E2eScal.BhCode.ViUnmarshal.IsInfixAt Host.prog kV) (hfV : LabelsFresh E2eScal.BhCode.ViUnmarshal kV)
    (in0 rt in1 sig : List UInt8) (hin0 : in0.length = 8) (hrt : rt.length = 32) (hin1 : in1.length = 8) (hsig : sig.length = 96)
    (s : MachineData) (ra guard : UInt64)
    (fp s1 s2 s4 sp0 sp1 sp2 s28 s30 l38 rslot lo ast aN0 aP1 aL1 aC1 aN2 aP3 aL3 aC3 : List UInt8)
    (hfp : fp.length = 8) (hs1 : s1.length = 8) (hs2 : s2.length = 8) (hs4 : s4.length = 8) (hsp0 : sp0.length = 8) (hsp1 : sp1.length = 8) (hsp2 : sp2.length = 8) (hs28 : s28.length = 8) (hs30 : s30.length = 8) (hl38 : l38.length = 8) (hrslot : rslot.length = 8) (hast : ast.length = 8) (haN0 : aN0.length = 8) (haP1 : aP1.length = 8) (haL1 : aL1.length = 8) (haC1 : aC1.length = 8) (haN2 : aN2.length = 8) (haP3 : aP3.length = 8) (haL3 : aL3.length = 8) (haC3 : aC3.length = 8)
    (R : DataMem → Prop) (S : Nat) (hS : S < 2 ^ 60) (hlo : lo.length = S + 8)
    (Heap : Nat → DataMem → Prop) (avail : Nat)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8))
      ⋆ Eq (s1.At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq (s4.At (s.regs.rsp.toBitVec + 32))
      ⋆ Eq (sp0.At (s.regs.rsp.toBitVec - 104))
      ⋆ Eq (sp1.At (s.regs.rsp.toBitVec - 96))
      ⋆ Eq (sp2.At (s.regs.rsp.toBitVec - 88))
      ⋆ Eq (s28.At (s.regs.rsp.toBitVec - 64))
      ⋆ Eq (s30.At (s.regs.rsp.toBitVec - 56))
      ⋆ Eq (l38.At (s.regs.rsp.toBitVec - 48))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 112))
      ⋆ Eq (lo.At (s.regs.rsp.toBitVec - 120 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Heap avail
      ⋆ Eq (in0.At s.regs.rbx.toBitVec)
      ⋆ Eq (rt.At (s.regs.rbx.toBitVec + 8))
      ⋆ Eq (in1.At (s.regs.rbx.toBitVec + 40))
      ⋆ Eq (sig.At (s.regs.rbx.toBitVec + 48))
      ⋆ Eq (ast.At s.regs.rax.toBitVec)
      ⋆ Eq (aN0.At (s.regs.rax.toBitVec + 8))
      ⋆ Eq (aP1.At (s.regs.rax.toBitVec + 16))
      ⋆ Eq (aL1.At (s.regs.rax.toBitVec + 24))
      ⋆ Eq (aC1.At (s.regs.rax.toBitVec + 32))
      ⋆ Eq (aN2.At (s.regs.rax.toBitVec + 40))
      ⋆ Eq (aP3.At (s.regs.rax.toBitVec + 48))
      ⋆ Eq (aL3.At (s.regs.rax.toBitVec + 56))
      ⋆ Eq (aC3.At (s.regs.rax.toBitVec + 64))
      ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec)
      ⋆ R)
    (hguard : guard.toNat + 112 < s.regs.rsp.toNat) (hlen : s.regs.rcx = 144) (hav : 128 ≤ avail)
    (hms : MakesliceC Heap E2e.Data.e2eU8Type_addr 1 (S + 8)) (hmm : MemmoveC (S + 8)),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 15)
        ∧ st.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - 104 }
        ∧ st.data.regs.rbp = { toBitVec := s.regs.rsp.toBitVec - 8 }
        ∧ st.data.regs.r14 = s.regs.r14
        ∧ st.data.regs.get64 Reg64.rax = s.regs.rax.toBitVec
        ∧ st.data.regs.get64 Reg64.rbx = s.regs.rbx.toBitVec ∧
        
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec + 32))
          ⋆ Eq (sp0.At (s.regs.rsp.toBitVec - 104))
          ⋆ Eq (sp1.At (s.regs.rsp.toBitVec - 96))
          ⋆ Eq (sp2.At (s.regs.rsp.toBitVec - 88))
          ⋆ Eq (s28.At (s.regs.rsp.toBitVec - 64))
          ⋆ Eq (s30.At (s.regs.rsp.toBitVec - 56))
          ⋆ Eq (l38.At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 112))
          ⋆ Eq (lo.At (s.regs.rsp.toBitVec - 120 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Heap avail
          ⋆ Eq (in0.At s.regs.rbx.toBitVec)
          ⋆ Eq (rt.At (s.regs.rbx.toBitVec + 8))
          ⋆ Eq (in1.At (s.regs.rbx.toBitVec + 40))
          ⋆ Eq (sig.At (s.regs.rbx.toBitVec + 48))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq (aN0.At (s.regs.rax.toBitVec + 8))
          ⋆ Eq (aP1.At (s.regs.rax.toBitVec + 16))
          ⋆ Eq (aL1.At (s.regs.rax.toBitVec + 24))
          ⋆ Eq (aC1.At (s.regs.rax.toBitVec + 32))
          ⋆ Eq (aN2.At (s.regs.rax.toBitVec + 40))
          ⋆ Eq (aP3.At (s.regs.rax.toBitVec + 48))
          ⋆ Eq (aL3.At (s.regs.rax.toBitVec + 56))
          ⋆ Eq (aC3.At (s.regs.rax.toBitVec + 64))
          ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec)
          ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  intro k hk hf kS hkS hfS kV hkV hfV in0 rt in1 sig hin0 hrt hin1 hsig s ra guard fp s1 s2 s4 sp0 sp1 sp2 s28 s30 l38 rslot lo ast aN0 aP1 aL1 aC1 aN2 aP3 aL3 aC3 hfp hs1 hs2 hs4 hsp0 hsp1 hsp2 hs28 hs30 hl38 hrslot hast haN0 haP1 haL1 haC1 haN2 haP3 haL3 haC3 R S hS hlo Heap avail h_mem hguard hlen hav hms hmm
  have hcs : Eq (ast.At s.regs.rax.toBitVec) =
      Eq ((ast.take 1).At s.regs.rax.toBitVec) ⋆ Eq ((ast.drop 1).At (s.regs.rax.toBitVec + 1)) := by
    conv => lhs; rw [← List.take_append_drop 1 ast]
    exact at_app _ _ (by rw [List.length_take, hast]; rfl) (by simp [hast])
  rw [hcs] at h_mem
  refine eventually_trans _ _ _ _ (decpro_seg _ _ _ _ 96 120 144 _ k (k + 11) (win hk 0 11) (by rfl) (by rfl)
    s ra guard (s.regs.rsp.toBitVec - 104) (s.regs.rsp.toBitVec + 16)
    (by simp only [Int64.toBitVec_ofNat] <;> bv_omega) (by simp only [Int64.toBitVec_ofNat] <;> bv_omega)
    fp s2 hfp hs2 _ (by ecancel) (Nat.lt_of_le_of_lt (Nat.le_add_right _ 112) hguard) (by rw [hlen]; rfl)) ?_
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
  apply kstep_st Reg64.rax Reg64.rsp 112 _ (k + 11) (k + 12) (win hk 11 1) (by rfl) (by rfl)
    (s.regs.rsp.toBitVec - 104) (s.regs.rsp.toBitVec + 8) (by simp only [Int64.toBitVec_ofNat] <;> bv_omega)
    s1 hs1 _ _ _ (by rfl) (by ecancel)
  intro m11 H11; kn; simp only [Reg64s.get64] at H11
  apply kstep_st Reg64.rdi Reg64.rsp 136 _ (k + 12) (k + 13) (win hk 12 1) (by rfl) (by rfl)
    (s.regs.rsp.toBitVec - 104) (s.regs.rsp.toBitVec + 32) (by simp only [Int64.toBitVec_ofNat] <;> bv_omega)
    s4 hs4 _ _ _ (by rfl) (by ecancel)
  intro m12 H12; kn; simp only [Reg64s.get64] at H12
  apply kstep_st Reg64.rbx Reg64.rsp 120 _ (k + 13) (k + 14) (win hk 13 1) (by rfl) (by rfl)
    (s.regs.rsp.toBitVec - 104) (s.regs.rsp.toBitVec + 16) (by simp only [Int64.toBitVec_ofNat] <;> bv_omega)
    (Int.toBytes 8 s.regs.rbx.toBitVec.toInt) (Int.toBytes_length 8 _) _ _ _ (by rfl) (by ecancel)
  intro m13 H13; kn; simp only [Reg64s.get64] at H13
  apply kstep_nilchk Reg64.rax _ (k + 14) (k + 15) (win hk 14 1) (by rfl) (by rfl)
    s.regs.rax.toBitVec (ast.take 1) (by simp [hast]) _ _ _ (by rfl) (by ecancel)
  intro fl; kn
  apply Eventually.done
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  dsimp only
  rw [hcs]; simp only [Std.ExtHashMap.sep_assoc]
  ecancel
theorem sm_g5_head_kind : ∀ (h : Host), type_of% (@sm_g5_head h)
    = @E2eScal.decHeadKindN h SmUnmarshal (E2eScal.layMix60 [E2eAd.Code.SlUnmarshal, E2eScal.BhCode.ViUnmarshal] 141 1) [.u64, .bytes 32, .u64, .bytes 96]
    ⟨15, 0, [(.rax, .rcv), (.rbx, .bf)],
      [.at (.dn 8) (.reg .rbp), .at (.up 8) (.reg .rax), .at (.up 16) (.reg .rbx), .at (.up 32) (.reg .rdi), .at (.dn 104) (.orig 4), .at (.dn 96) (.orig 5), .at (.dn 88) (.orig 6), .at (.dn 64) (.orig 7), .at (.dn 56) (.orig 8), .at (.dn 48) (.orig 9), .at (.dn 112) (.orig 10), .lo (.orig 11)],
      []⟩ := by
  intro h; rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Field 1 `Slot` (call): boundary state 0 (directive 15) → boundary state 1 (directive 47). -/
theorem sm_g5_f1 : ∀ (k : Nat) (hk : SmUnmarshal.IsInfixAt Host.prog k) (hf : LabelsFresh SmUnmarshal k)
    (kS : Nat) (hkS : E2eAd.Code.SlUnmarshal.IsInfixAt Host.prog kS) (hfS : LabelsFresh E2eAd.Code.SlUnmarshal kS)
    (kV : Nat) (hkV : E2eScal.BhCode.ViUnmarshal.IsInfixAt Host.prog kV) (hfV : LabelsFresh E2eScal.BhCode.ViUnmarshal kV)
    (in0 rt in1 sig : List UInt8) (hin0 : in0.length = 8) (hrt : rt.length = 32) (hin1 : in1.length = 8) (hsig : sig.length = 96)
    (s : MachineData) (ra guard : UInt64)
    (fp s1 s2 s4 sp0 sp1 sp2 s28 s30 l38 rslot lo ast aN0 aP1 aL1 aC1 aN2 aP3 aL3 aC3 : List UInt8)
    (hfp : fp.length = 8) (hs1 : s1.length = 8) (hs2 : s2.length = 8) (hs4 : s4.length = 8) (hsp0 : sp0.length = 8) (hsp1 : sp1.length = 8) (hsp2 : sp2.length = 8) (hs28 : s28.length = 8) (hs30 : s30.length = 8) (hl38 : l38.length = 8) (hrslot : rslot.length = 8) (hast : ast.length = 8) (haN0 : aN0.length = 8) (haP1 : aP1.length = 8) (haL1 : aL1.length = 8) (haC1 : aC1.length = 8) (haN2 : aN2.length = 8) (haP3 : aP3.length = 8) (haL3 : aL3.length = 8) (haC3 : aC3.length = 8)
    (R : DataMem → Prop) (S : Nat) (hS : S < 2 ^ 60) (hlo : lo.length = S + 8)
    (Heap : Nat → DataMem → Prop) (avail : Nat)
    (hguard : guard.toNat + 112 < s.regs.rsp.toNat) (hav : 128 ≤ avail)
    (hms : MakesliceC Heap E2e.Data.e2eU8Type_addr 1 (S + 8)) (hmm : MemmoveC (S + 8)) (st0 : MachineState),
    (st0.pc = Host.addrOf (k + 15)
        ∧ st0.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - 104 }
        ∧ st0.data.regs.rbp = { toBitVec := s.regs.rsp.toBitVec - 8 }
        ∧ st0.data.regs.r14 = s.regs.r14
        ∧ st0.data.regs.get64 Reg64.rax = s.regs.rax.toBitVec
        ∧ st0.data.regs.get64 Reg64.rbx = s.regs.rbx.toBitVec ∧
        
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec + 32))
          ⋆ Eq (sp0.At (s.regs.rsp.toBitVec - 104))
          ⋆ Eq (sp1.At (s.regs.rsp.toBitVec - 96))
          ⋆ Eq (sp2.At (s.regs.rsp.toBitVec - 88))
          ⋆ Eq (s28.At (s.regs.rsp.toBitVec - 64))
          ⋆ Eq (s30.At (s.regs.rsp.toBitVec - 56))
          ⋆ Eq (l38.At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 112))
          ⋆ Eq (lo.At (s.regs.rsp.toBitVec - 120 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Heap avail
          ⋆ Eq (in0.At s.regs.rbx.toBitVec)
          ⋆ Eq (rt.At (s.regs.rbx.toBitVec + 8))
          ⋆ Eq (in1.At (s.regs.rbx.toBitVec + 40))
          ⋆ Eq (sig.At (s.regs.rbx.toBitVec + 48))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq (aN0.At (s.regs.rax.toBitVec + 8))
          ⋆ Eq (aP1.At (s.regs.rax.toBitVec + 16))
          ⋆ Eq (aL1.At (s.regs.rax.toBitVec + 24))
          ⋆ Eq (aC1.At (s.regs.rax.toBitVec + 32))
          ⋆ Eq (aN2.At (s.regs.rax.toBitVec + 40))
          ⋆ Eq (aP3.At (s.regs.rax.toBitVec + 48))
          ⋆ Eq (aL3.At (s.regs.rax.toBitVec + 56))
          ⋆ Eq (aC3.At (s.regs.rax.toBitVec + 64))
          ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec)
          ⋆ R) st0.data.dmem) →
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 47)
        ∧ st.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - 104 }
        ∧ st.data.regs.rbp = { toBitVec := s.regs.rsp.toBitVec - 8 }
        ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ (x0 x1 : List UInt8), x0.length = 8 ∧ x1.length = S + 8 ∧ 
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec + 32))
          ⋆ Eq (sp0.At (s.regs.rsp.toBitVec - 104))
          ⋆ Eq (x0.At (s.regs.rsp.toBitVec - 96))
          ⋆ Eq (sp2.At (s.regs.rsp.toBitVec - 88))
          ⋆ Eq (s28.At (s.regs.rsp.toBitVec - 64))
          ⋆ Eq (s30.At (s.regs.rsp.toBitVec - 56))
          ⋆ Eq (l38.At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 18)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 112))
          ⋆ Eq (x1.At (s.regs.rsp.toBitVec - 120 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Heap avail
          ⋆ Eq (in0.At s.regs.rbx.toBitVec)
          ⋆ Eq (rt.At (s.regs.rbx.toBitVec + 8))
          ⋆ Eq (in1.At (s.regs.rbx.toBitVec + 40))
          ⋆ Eq (sig.At (s.regs.rbx.toBitVec + 48))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq (in0.At (s.regs.rax.toBitVec + 8))
          ⋆ Eq (aP1.At (s.regs.rax.toBitVec + 16))
          ⋆ Eq (aL1.At (s.regs.rax.toBitVec + 24))
          ⋆ Eq (aC1.At (s.regs.rax.toBitVec + 32))
          ⋆ Eq (aN2.At (s.regs.rax.toBitVec + 40))
          ⋆ Eq (aP3.At (s.regs.rax.toBitVec + 48))
          ⋆ Eq (aL3.At (s.regs.rax.toBitVec + 56))
          ⋆ Eq (aC3.At (s.regs.rax.toBitVec + 64))
          ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec)
          ⋆ R) st.data.dmem)
      st0 := by
  intro k hk hf kS hkS hfS kV hkV hfV in0 rt in1 sig hin0 hrt hin1 hsig s ra guard fp s1 s2 s4 sp0 sp1 sp2 s28 s30 l38 rslot lo ast aN0 aP1 aL1 aC1 aN2 aP3 aL3 aC3 hfp hs1 hs2 hs4 hsp0 hsp1 hsp2 hs28 hs30 hl38 hrslot hast haN0 haP1 haL1 haC1 haN2 haP3 haL3 haC3 R S hS hlo Heap avail hguard hav hms hmm
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at hguard ⊢
  rintro ⟨d, pc⟩ ⟨hpc, hrsp, hrbp, hr14, hrrax, hrrbx, Hm⟩
  dsimp only at hpc hrsp hrbp hr14 hrrax hrrbx Hm
  subst hpc
  obtain ⟨⟨rax1, rbx1, rcx1, rdx1, rsi1, rdi1, rsp1, rbp1, r81, r91, r101, r111, r121, r131, r141, r151⟩, zmms1, flags1, mem1⟩ := d
  simp only [Reg64s.get64] at hrsp hrbp hr14 hrrax hrrbx Hm
  subst rsp1 rbp1 r141
  obtain rfl : rax = rax1 := (UInt64.toBitVec_inj.mp hrrax).symm
  obtain rfl : rbx = rbx1 := (UInt64.toBitVec_inj.mp hrrbx).symm
  have hC := sl_uacc_holds kS hkS hfS
  have hg : guard.toNat < (rsp.toBitVec - 112).toNat := by
    have hgd : guard.toNat + 112 < rsp.toBitVec.toNat := hguard
    bv_omega
  have hlS : (lo.take S).length = S := by simp [hlo]
  have hl8 : (lo.drop S).length = 8 := by simp [hlo]
  have hLs : lo = lo.take S ++ lo.drop S := (List.take_append_drop S lo).symm
  rw [hLs, g5_lo8 (rsp.toBitVec - 120) S hS _ _ hlS hl8] at Hm
  apply Gen.sm_g4dec_s15 k hk hf
  intro fl15; kn
  apply Gen.sm_g4dec_s16 k hk hf
  kn
  refine eventually_trans _ _ _ _ (Gen.sm_g4dec_Slot_call k hk hf hC (rsp.toBitVec - 104) (rax.toBitVec + 8) rbx.toBitVec
    (rsp.toBitVec - 112) (rsp.toBitVec - 120) (rsp.toBitVec - 96) (by bv_omega) (by bv_omega) (by bv_omega)
    { toBitVec := rsp.toBitVec - 8#64 } r14 guard in0 rslot (lo.drop S) sp1 aN0
    hin0 hrslot hl8 hsp1 haN0 hg _ _
    (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by first | rfl | decide) (by ecancel)) ?_
  rintro ⟨d', pc'⟩ ⟨hpc', hrax', hrbx', hrsp', hrbp', hr14', Hm'⟩
  dsimp only at hpc' hrax' hrbx' hrsp' hrbp' hr14' Hm'
  apply Eventually.done
  refine ⟨hpc', hrsp', hrbp', hr14', (Int.toBytes 8 rbx.toBitVec.toInt), (lo.take S ++ Int.toBytes 8 (rsp.toBitVec - 8#64).toInt),
    (Int.toBytes_length 8 _), (by simp only [List.length_append, hlS, Int.toBytes_length]), ?_⟩
  dsimp only
  rw [g5_lo8 (rsp.toBitVec - 120) S hS _ _ hlS (Int.toBytes_length 8 _)]
  rw [show k + 17 + 1 = k + 18 from rfl] at Hm'
  ecancel
theorem sm_g5_f1_kind : ∀ (h : Host), type_of% (@sm_g5_f1 h)
    = @E2eScal.decFieldKindN h SmUnmarshal (E2eScal.layMix60 [E2eAd.Code.SlUnmarshal, E2eScal.BhCode.ViUnmarshal] 141 1) [.u64, .bytes 32, .u64, .bytes 96]
    ⟨15, 0, [(.rax, .rcv), (.rbx, .bf)],
      [.at (.dn 8) (.reg .rbp), .at (.up 8) (.reg .rax), .at (.up 16) (.reg .rbx), .at (.up 32) (.reg .rdi), .at (.dn 104) (.orig 4), .at (.dn 96) (.orig 5), .at (.dn 88) (.orig 6), .at (.dn 64) (.orig 7), .at (.dn 56) (.orig 8), .at (.dn 48) (.orig 9), .at (.dn 112) (.orig 10), .lo (.orig 11)],
      []⟩
    ⟨47, 1, [],
      [.at (.dn 8) (.reg .rbp), .at (.up 8) (.reg .rax), .at (.up 16) (.reg .rbx), .at (.up 32) (.reg .rdi), .at (.dn 104) (.orig 4), .at (.dn 96) (.ex 0), .at (.dn 88) (.orig 6), .at (.dn 64) (.orig 7), .at (.dn 56) (.orig 8), .at (.dn 48) (.orig 9), .at (.dn 112) (.ret 18), .lo (.ex 1)],
      [.n 8, .lo]⟩ := by
  intro h; rfl

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
/-- Field 2 `BlockRoot` (bytes): boundary state 1 (directive 47) → boundary state 2 (directive 82). -/
theorem sm_g5_f2 : ∀ (k : Nat) (hk : SmUnmarshal.IsInfixAt Host.prog k) (hf : LabelsFresh SmUnmarshal k)
    (kS : Nat) (hkS : E2eAd.Code.SlUnmarshal.IsInfixAt Host.prog kS) (hfS : LabelsFresh E2eAd.Code.SlUnmarshal kS)
    (kV : Nat) (hkV : E2eScal.BhCode.ViUnmarshal.IsInfixAt Host.prog kV) (hfV : LabelsFresh E2eScal.BhCode.ViUnmarshal kV)
    (in0 rt in1 sig : List UInt8) (hin0 : in0.length = 8) (hrt : rt.length = 32) (hin1 : in1.length = 8) (hsig : sig.length = 96)
    (s : MachineData) (ra guard : UInt64)
    (fp s1 s2 s4 sp0 sp1 sp2 s28 s30 l38 rslot lo ast aN0 aP1 aL1 aC1 aN2 aP3 aL3 aC3 : List UInt8)
    (hfp : fp.length = 8) (hs1 : s1.length = 8) (hs2 : s2.length = 8) (hs4 : s4.length = 8) (hsp0 : sp0.length = 8) (hsp1 : sp1.length = 8) (hsp2 : sp2.length = 8) (hs28 : s28.length = 8) (hs30 : s30.length = 8) (hl38 : l38.length = 8) (hrslot : rslot.length = 8) (hast : ast.length = 8) (haN0 : aN0.length = 8) (haP1 : aP1.length = 8) (haL1 : aL1.length = 8) (haC1 : aC1.length = 8) (haN2 : aN2.length = 8) (haP3 : aP3.length = 8) (haL3 : aL3.length = 8) (haC3 : aC3.length = 8)
    (R : DataMem → Prop) (S : Nat) (hS : S < 2 ^ 60) (hlo : lo.length = S + 8)
    (Heap : Nat → DataMem → Prop) (avail : Nat)
    (hguard : guard.toNat + 112 < s.regs.rsp.toNat) (hav : 128 ≤ avail)
    (hms : MakesliceC Heap E2e.Data.e2eU8Type_addr 1 (S + 8)) (hmm : MemmoveC (S + 8)) (st0 : MachineState),
    (st0.pc = Host.addrOf (k + 47)
        ∧ st0.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - 104 }
        ∧ st0.data.regs.rbp = { toBitVec := s.regs.rsp.toBitVec - 8 }
        ∧ st0.data.regs.r14 = s.regs.r14 ∧
        ∃ (x0 x1 : List UInt8), x0.length = 8 ∧ x1.length = S + 8 ∧ 
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec + 32))
          ⋆ Eq (sp0.At (s.regs.rsp.toBitVec - 104))
          ⋆ Eq (x0.At (s.regs.rsp.toBitVec - 96))
          ⋆ Eq (sp2.At (s.regs.rsp.toBitVec - 88))
          ⋆ Eq (s28.At (s.regs.rsp.toBitVec - 64))
          ⋆ Eq (s30.At (s.regs.rsp.toBitVec - 56))
          ⋆ Eq (l38.At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 18)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 112))
          ⋆ Eq (x1.At (s.regs.rsp.toBitVec - 120 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Heap avail
          ⋆ Eq (in0.At s.regs.rbx.toBitVec)
          ⋆ Eq (rt.At (s.regs.rbx.toBitVec + 8))
          ⋆ Eq (in1.At (s.regs.rbx.toBitVec + 40))
          ⋆ Eq (sig.At (s.regs.rbx.toBitVec + 48))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq (in0.At (s.regs.rax.toBitVec + 8))
          ⋆ Eq (aP1.At (s.regs.rax.toBitVec + 16))
          ⋆ Eq (aL1.At (s.regs.rax.toBitVec + 24))
          ⋆ Eq (aC1.At (s.regs.rax.toBitVec + 32))
          ⋆ Eq (aN2.At (s.regs.rax.toBitVec + 40))
          ⋆ Eq (aP3.At (s.regs.rax.toBitVec + 48))
          ⋆ Eq (aL3.At (s.regs.rax.toBitVec + 56))
          ⋆ Eq (aC3.At (s.regs.rax.toBitVec + 64))
          ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec)
          ⋆ R) st0.data.dmem) →
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 82)
        ∧ st.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - 104 }
        ∧ st.data.regs.rbp = { toBitVec := s.regs.rsp.toBitVec - 8 }
        ∧ st.data.regs.r14 = s.regs.r14
        ∧ st.data.regs.get64 Reg64.rax = s.regs.rax.toBitVec ∧
        ∃ (p1 : BitVec 64) (x0 x1 : List UInt8), x0.length = 24 ∧ x1.length = S + 8 ∧ 
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec + 32))
          ⋆ Eq (x0.At (s.regs.rsp.toBitVec - 104))
          ⋆ Eq (s28.At (s.regs.rsp.toBitVec - 64))
          ⋆ Eq (s30.At (s.regs.rsp.toBitVec - 56))
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 67)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 112))
          ⋆ Eq (x1.At (s.regs.rsp.toBitVec - 120 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Heap (avail - 32)
          ⋆ Eq (in0.At s.regs.rbx.toBitVec)
          ⋆ Eq (rt.At (s.regs.rbx.toBitVec + 8))
          ⋆ Eq (in1.At (s.regs.rbx.toBitVec + 40))
          ⋆ Eq (sig.At (s.regs.rbx.toBitVec + 48))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq (in0.At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 24))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 32))
          ⋆ Eq (aN2.At (s.regs.rax.toBitVec + 40))
          ⋆ Eq (aP3.At (s.regs.rax.toBitVec + 48))
          ⋆ Eq (aL3.At (s.regs.rax.toBitVec + 56))
          ⋆ Eq (aC3.At (s.regs.rax.toBitVec + 64))
          ⋆ Eq (rt.At p1)
          ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec)
          ⋆ R) st.data.dmem)
      st0 := by
  intro k hk hf kS hkS hfS kV hkV hfV in0 rt in1 sig hin0 hrt hin1 hsig s ra guard fp s1 s2 s4 sp0 sp1 sp2 s28 s30 l38 rslot lo ast aN0 aP1 aL1 aC1 aN2 aP3 aL3 aC3 hfp hs1 hs2 hs4 hsp0 hsp1 hsp2 hs28 hs30 hl38 hrslot hast haN0 haP1 haL1 haC1 haN2 haP3 haL3 haC3 R S hS hlo Heap avail hguard hav hms hmm
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at hguard ⊢
  rintro ⟨d, pc⟩ ⟨hpc, hrsp, hrbp, hr14, x0, x1, hx0, hx1, Hm⟩
  dsimp only at hpc hrsp hrbp hr14  Hm
  subst hpc
  refine eventually_trans _ _ _ _ (Gen.sm_g4dec_BlockRoot_seg k hk hf (rsp.toBitVec - 104) rax.toBitVec rbx.toBitVec
    (rsp.toBitVec + 8) (rsp.toBitVec + 16) (rsp.toBitVec - 48) (rsp.toBitVec - 112)
    (rsp.toBitVec - 120 - BitVec.ofNat 64 S) (rax.toBitVec + 16) (rax.toBitVec + 24) (rax.toBitVec + 32) (rbx.toBitVec + 8) (S + 8)
    (by simp only [Int64.toBitVec_ofNat] <;> bv_omega) (by simp only [Int64.toBitVec_ofNat] <;> bv_omega) (by simp only [Int64.toBitVec_ofNat] <;> bv_omega) (by bv_omega) (g5_lo _ 104 120 S (by decide))
    (by simp only [Int64.toBitVec_ofNat] <;> bv_omega) (by simp only [Int64.toBitVec_ofNat] <;> bv_omega) (by simp only [Int64.toBitVec_ofNat] <;> bv_omega) (by simp only [Int64.toBitVec_ofNat] <;> bv_omega)
    { toBitVec := rsp.toBitVec - 8#64 } r14 rt hrt
    (sp0 ++ (x0 ++ sp2)) (Int.toBytes 8 (Host.addrOf (k + 18)).toBitVec.toInt) x1 l38 aP1 aL1 aC1
    (by simp only [List.length_append, Int.toBytes_length, hsp0, hx0, hsp2]) (Int.toBytes_length 8 _) hx1 hl38 haP1 haL1 haC1
    _ Heap avail (by omega) d hrsp hrbp hr14
      (by rw [g5_j3 (rsp.toBitVec - 104) (rsp.toBitVec - 96) (rsp.toBitVec - 88) _ _ _ hsp0 hx0 hsp2 (by bv_omega) (by bv_omega)]; ecancel) hms hmm) ?_
  rintro ⟨d', pc'⟩ ⟨hpc', hrsp', hrbp', hr14', p1, spl', lo', hspl', hlo', hrY, Hm'⟩
  dsimp only at hpc' hrsp' hrbp' hr14' hrY Hm'
  subst hpc'
  obtain ⟨⟨rax2, rbx2, rcx2, rdx2, rsi2, rdi2, rsp2, rbp2, r82, r92, r102, r112, r122, r132, r142, r152⟩, zmms2, flags2, mem2⟩ := d'
  simp only at hrsp' hrbp' hr14' hrY Hm'
  subst rsp2 rbp2 r142
  apply Gen.sm_g4dec_s72 k hk hf (rsp.toBitVec - 104) (rsp.toBitVec - 48) p1 (by simp only [Int64.toBitVec_ofNat] <;> bv_omega) _ _ _ (by rfl) (by ecancel)
  kn
  apply Gen.sm_g4dec_s73 k hk hf
  apply Gen.sm_g4dec_s80 k hk hf
  apply Gen.sm_g4dec_s81 k hk hf rax.toBitVec (rax.toBitVec + 16) (by simp only [Int64.toBitVec_ofNat] <;> bv_omega) (Int.toBytes 8 p1.toInt) (Int.toBytes_length 8 _) _ _ _
    (by exact hrY) (by ecancel)
  intro m' H
  kn
  simp only [Reg64s.get64] at H
  apply Eventually.done
  refine ⟨rfl, rfl, rfl, rfl, hrY, p1, spl', lo', hspl', hlo', ?_⟩
  dsimp only
  rw [show k + 66 + 1 = k + 67 from rfl] at H
  ecancel
theorem sm_g5_f2_kind : ∀ (h : Host), type_of% (@sm_g5_f2 h)
    = @E2eScal.decFieldKindN h SmUnmarshal (E2eScal.layMix60 [E2eAd.Code.SlUnmarshal, E2eScal.BhCode.ViUnmarshal] 141 1) [.u64, .bytes 32, .u64, .bytes 96]
    ⟨47, 1, [],
      [.at (.dn 8) (.reg .rbp), .at (.up 8) (.reg .rax), .at (.up 16) (.reg .rbx), .at (.up 32) (.reg .rdi), .at (.dn 104) (.orig 4), .at (.dn 96) (.ex 0), .at (.dn 88) (.orig 6), .at (.dn 64) (.orig 7), .at (.dn 56) (.orig 8), .at (.dn 48) (.orig 9), .at (.dn 112) (.ret 18), .lo (.ex 1)],
      [.n 8, .lo]⟩
    ⟨82, 2, [(.rax, .rcv)],
      [.at (.dn 8) (.reg .rbp), .at (.up 8) (.reg .rax), .at (.up 16) (.reg .rbx), .at (.up 32) (.reg .rdi), .at (.dn 104) (.ex 0), .at (.dn 64) (.orig 7), .at (.dn 56) (.orig 8), .at (.dn 48) (.ptr 0), .at (.dn 112) (.ret 67), .lo (.ex 1)],
      [.n 24, .lo]⟩ := by
  intro h; rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Field 3 `ValidatorIndex` (call): boundary state 2 (directive 82) → boundary state 3 (directive 118). -/
theorem sm_g5_f3 : ∀ (k : Nat) (hk : SmUnmarshal.IsInfixAt Host.prog k) (hf : LabelsFresh SmUnmarshal k)
    (kS : Nat) (hkS : E2eAd.Code.SlUnmarshal.IsInfixAt Host.prog kS) (hfS : LabelsFresh E2eAd.Code.SlUnmarshal kS)
    (kV : Nat) (hkV : E2eScal.BhCode.ViUnmarshal.IsInfixAt Host.prog kV) (hfV : LabelsFresh E2eScal.BhCode.ViUnmarshal kV)
    (in0 rt in1 sig : List UInt8) (hin0 : in0.length = 8) (hrt : rt.length = 32) (hin1 : in1.length = 8) (hsig : sig.length = 96)
    (s : MachineData) (ra guard : UInt64)
    (fp s1 s2 s4 sp0 sp1 sp2 s28 s30 l38 rslot lo ast aN0 aP1 aL1 aC1 aN2 aP3 aL3 aC3 : List UInt8)
    (hfp : fp.length = 8) (hs1 : s1.length = 8) (hs2 : s2.length = 8) (hs4 : s4.length = 8) (hsp0 : sp0.length = 8) (hsp1 : sp1.length = 8) (hsp2 : sp2.length = 8) (hs28 : s28.length = 8) (hs30 : s30.length = 8) (hl38 : l38.length = 8) (hrslot : rslot.length = 8) (hast : ast.length = 8) (haN0 : aN0.length = 8) (haP1 : aP1.length = 8) (haL1 : aL1.length = 8) (haC1 : aC1.length = 8) (haN2 : aN2.length = 8) (haP3 : aP3.length = 8) (haL3 : aL3.length = 8) (haC3 : aC3.length = 8)
    (R : DataMem → Prop) (S : Nat) (hS : S < 2 ^ 60) (hlo : lo.length = S + 8)
    (Heap : Nat → DataMem → Prop) (avail : Nat)
    (hguard : guard.toNat + 112 < s.regs.rsp.toNat) (hav : 128 ≤ avail)
    (hms : MakesliceC Heap E2e.Data.e2eU8Type_addr 1 (S + 8)) (hmm : MemmoveC (S + 8)) (st0 : MachineState),
    (st0.pc = Host.addrOf (k + 82)
        ∧ st0.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - 104 }
        ∧ st0.data.regs.rbp = { toBitVec := s.regs.rsp.toBitVec - 8 }
        ∧ st0.data.regs.r14 = s.regs.r14
        ∧ st0.data.regs.get64 Reg64.rax = s.regs.rax.toBitVec ∧
        ∃ (p1 : BitVec 64) (x0 x1 : List UInt8), x0.length = 24 ∧ x1.length = S + 8 ∧ 
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec + 32))
          ⋆ Eq (x0.At (s.regs.rsp.toBitVec - 104))
          ⋆ Eq (s28.At (s.regs.rsp.toBitVec - 64))
          ⋆ Eq (s30.At (s.regs.rsp.toBitVec - 56))
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 67)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 112))
          ⋆ Eq (x1.At (s.regs.rsp.toBitVec - 120 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Heap (avail - 32)
          ⋆ Eq (in0.At s.regs.rbx.toBitVec)
          ⋆ Eq (rt.At (s.regs.rbx.toBitVec + 8))
          ⋆ Eq (in1.At (s.regs.rbx.toBitVec + 40))
          ⋆ Eq (sig.At (s.regs.rbx.toBitVec + 48))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq (in0.At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 24))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 32))
          ⋆ Eq (aN2.At (s.regs.rax.toBitVec + 40))
          ⋆ Eq (aP3.At (s.regs.rax.toBitVec + 48))
          ⋆ Eq (aL3.At (s.regs.rax.toBitVec + 56))
          ⋆ Eq (aC3.At (s.regs.rax.toBitVec + 64))
          ⋆ Eq (rt.At p1)
          ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec)
          ⋆ R) st0.data.dmem) →
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 118)
        ∧ st.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - 104 }
        ∧ st.data.regs.rbp = { toBitVec := s.regs.rsp.toBitVec - 8 }
        ∧ st.data.regs.r14 = s.regs.r14
        ∧ st.data.regs.get64 Reg64.rax = 0
        ∧ st.data.regs.get64 Reg64.rbx = 0 ∧
        ∃ (p1 : BitVec 64) (x0 x1 : List UInt8), x0.length = 24 ∧ x1.length = S + 8 ∧ 
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec + 32))
          ⋆ Eq (x0.At (s.regs.rsp.toBitVec - 104))
          ⋆ Eq (s28.At (s.regs.rsp.toBitVec - 64))
          ⋆ Eq (s30.At (s.regs.rsp.toBitVec - 56))
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 89)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 112))
          ⋆ Eq (x1.At (s.regs.rsp.toBitVec - 120 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Heap (avail - 32)
          ⋆ Eq (in0.At s.regs.rbx.toBitVec)
          ⋆ Eq (rt.At (s.regs.rbx.toBitVec + 8))
          ⋆ Eq (in1.At (s.regs.rbx.toBitVec + 40))
          ⋆ Eq (sig.At (s.regs.rbx.toBitVec + 48))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq (in0.At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 24))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 32))
          ⋆ Eq (in1.At (s.regs.rax.toBitVec + 40))
          ⋆ Eq (aP3.At (s.regs.rax.toBitVec + 48))
          ⋆ Eq (aL3.At (s.regs.rax.toBitVec + 56))
          ⋆ Eq (aC3.At (s.regs.rax.toBitVec + 64))
          ⋆ Eq (rt.At p1)
          ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec)
          ⋆ R) st.data.dmem)
      st0 := by
  intro k hk hf kS hkS hfS kV hkV hfV in0 rt in1 sig hin0 hrt hin1 hsig s ra guard fp s1 s2 s4 sp0 sp1 sp2 s28 s30 l38 rslot lo ast aN0 aP1 aL1 aC1 aN2 aP3 aL3 aC3 hfp hs1 hs2 hs4 hsp0 hsp1 hsp2 hs28 hs30 hl38 hrslot hast haN0 haP1 haL1 haC1 haN2 haP3 haL3 haC3 R S hS hlo Heap avail hguard hav hms hmm
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at hguard ⊢
  rintro ⟨d, pc⟩ ⟨hpc, hrsp, hrbp, hr14, hrrax, p1, x0, x1, hx0, hx1, Hm⟩
  dsimp only at hpc hrsp hrbp hr14 hrrax Hm
  subst hpc
  obtain ⟨⟨rax1, rbx1, rcx1, rdx1, rsi1, rdi1, rsp1, rbp1, r81, r91, r101, r111, r121, r131, r141, r151⟩, zmms1, flags1, mem1⟩ := d
  simp only [Reg64s.get64] at hrsp hrbp hr14 hrrax Hm
  subst rsp1 rbp1 r141
  obtain rfl : rax = rax1 := (UInt64.toBitVec_inj.mp hrrax).symm
  have hC := vi_uacc_holds kV hkV hfV
  have hg : guard.toNat < (rsp.toBitVec - 112).toNat := by
    have hgd : guard.toNat + 112 < rsp.toBitVec.toNat := hguard
    bv_omega
  have hq0 : (x0.take 8).length = 8 := by simp [hx0]
  have hq1 : ((x0.drop 8).take 8).length = 8 := by simp [hx0]
  have hq2 : ((x0.drop 8).drop 8).length = 8 := by simp [hx0]
  have hXs : x0 = x0.take 8 ++ ((x0.drop 8).take 8 ++ (x0.drop 8).drop 8) := by
    rw [List.take_append_drop, List.take_append_drop]
  have hlS : (x1.take S).length = S := by simp [hx1]
  have hl8 : (x1.drop S).length = 8 := by simp [hx1]
  have hLs : x1 = x1.take S ++ x1.drop S := (List.take_append_drop S x1).symm
  rw [hXs, hLs, g5_j3 (rsp.toBitVec - 104) (rsp.toBitVec - 96) (rsp.toBitVec - 88) _ _ _ hq0 hq1 hq2 (by bv_omega) (by bv_omega), g5_lo8 (rsp.toBitVec - 120) S hS _ _ hlS hl8] at Hm
  apply Gen.sm_g4dec_s82 k hk hf (rsp.toBitVec - 104) (rsp.toBitVec + 16) rbx.toBitVec (by simp only [Int64.toBitVec_ofNat] <;> bv_omega) _ _ _ (by rfl) (by ecancel)
  kn
  apply Gen.sm_g4dec_s83 k hk hf
  intro fl83; kn
  apply Gen.sm_g4dec_s84 k hk hf (rsp.toBitVec - 104) (rsp.toBitVec + 32) (by simp only [Int64.toBitVec_ofNat] <;> bv_omega) (Int.toBytes 8 rdi.toBitVec.toInt) (Int.toBytes_length 8 _) _ _ _ (by rfl) (by ecancel)
  kn
  apply Gen.sm_g4dec_s85 k hk hf
  intro fl85; kn
  apply Gen.sm_g4dec_s86 k hk hf
  intro fl86; kn
  apply Gen.sm_g4dec_s87 k hk hf
  kn
  refine eventually_trans _ _ _ _ (Gen.sm_g4dec_ValidatorIndex_call k hk hf hC (rsp.toBitVec - 104) (rax.toBitVec + 40) (rbx.toBitVec + 40)
    (rsp.toBitVec - 112) (rsp.toBitVec - 120) (rsp.toBitVec - 96) (by bv_omega) (by bv_omega) (by bv_omega)
    { toBitVec := rsp.toBitVec - 8#64 } r14 guard in1 (Int.toBytes 8 (Host.addrOf (k + 67)).toBitVec.toInt) (x1.drop S) ((x0.drop 8).take 8) aN2
    hin1 (Int.toBytes_length 8 _) hl8 hq1 haN2 hg _ _
    (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by first | rfl | decide) (by ecancel)) ?_
  rintro ⟨d', pc'⟩ ⟨hpc', hrax', hrbx', hrsp', hrbp', hr14', Hm'⟩
  dsimp only at hpc' hrax' hrbx' hrsp' hrbp' hr14' Hm'
  apply Eventually.done
  refine ⟨hpc', hrsp', hrbp', hr14', (congrArg UInt64.toBitVec hrax'), (congrArg UInt64.toBitVec hrbx'), p1, (x0.take 8 ++ (Int.toBytes 8 (rbx.toBitVec + 40).toInt ++ (x0.drop 8).drop 8)), (x1.take S ++ Int.toBytes 8 (rsp.toBitVec - 8#64).toInt),
    (by simp only [List.length_append, hq0, hq2, Int.toBytes_length]), (by simp only [List.length_append, hlS, Int.toBytes_length]), ?_⟩
  dsimp only
  rw [g5_j3 (rsp.toBitVec - 104) (rsp.toBitVec - 96) (rsp.toBitVec - 88) _ _ _ hq0 (Int.toBytes_length 8 _) hq2 (by bv_omega) (by bv_omega), g5_lo8 (rsp.toBitVec - 120) S hS _ _ hlS (Int.toBytes_length 8 _)]
  rw [show k + 88 + 1 = k + 89 from rfl] at Hm'
  ecancel
theorem sm_g5_f3_kind : ∀ (h : Host), type_of% (@sm_g5_f3 h)
    = @E2eScal.decFieldKindN h SmUnmarshal (E2eScal.layMix60 [E2eAd.Code.SlUnmarshal, E2eScal.BhCode.ViUnmarshal] 141 1) [.u64, .bytes 32, .u64, .bytes 96]
    ⟨82, 2, [(.rax, .rcv)],
      [.at (.dn 8) (.reg .rbp), .at (.up 8) (.reg .rax), .at (.up 16) (.reg .rbx), .at (.up 32) (.reg .rdi), .at (.dn 104) (.ex 0), .at (.dn 64) (.orig 7), .at (.dn 56) (.orig 8), .at (.dn 48) (.ptr 0), .at (.dn 112) (.ret 67), .lo (.ex 1)],
      [.n 24, .lo]⟩
    ⟨118, 3, [(.rax, .zero), (.rbx, .zero)],
      [.at (.dn 8) (.reg .rbp), .at (.up 8) (.reg .rax), .at (.up 16) (.reg .rbx), .at (.up 32) (.reg .rdi), .at (.dn 104) (.ex 0), .at (.dn 64) (.orig 7), .at (.dn 56) (.orig 8), .at (.dn 48) (.ptr 0), .at (.dn 112) (.ret 89), .lo (.ex 1)],
      [.n 24, .lo]⟩ := by
  intro h; rfl

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
/-- Field 4 `Signature` (bytes): boundary state 3 (directive 118) → boundary state 4 (directive 156). -/
theorem sm_g5_f4 : ∀ (k : Nat) (hk : SmUnmarshal.IsInfixAt Host.prog k) (hf : LabelsFresh SmUnmarshal k)
    (kS : Nat) (hkS : E2eAd.Code.SlUnmarshal.IsInfixAt Host.prog kS) (hfS : LabelsFresh E2eAd.Code.SlUnmarshal kS)
    (kV : Nat) (hkV : E2eScal.BhCode.ViUnmarshal.IsInfixAt Host.prog kV) (hfV : LabelsFresh E2eScal.BhCode.ViUnmarshal kV)
    (in0 rt in1 sig : List UInt8) (hin0 : in0.length = 8) (hrt : rt.length = 32) (hin1 : in1.length = 8) (hsig : sig.length = 96)
    (s : MachineData) (ra guard : UInt64)
    (fp s1 s2 s4 sp0 sp1 sp2 s28 s30 l38 rslot lo ast aN0 aP1 aL1 aC1 aN2 aP3 aL3 aC3 : List UInt8)
    (hfp : fp.length = 8) (hs1 : s1.length = 8) (hs2 : s2.length = 8) (hs4 : s4.length = 8) (hsp0 : sp0.length = 8) (hsp1 : sp1.length = 8) (hsp2 : sp2.length = 8) (hs28 : s28.length = 8) (hs30 : s30.length = 8) (hl38 : l38.length = 8) (hrslot : rslot.length = 8) (hast : ast.length = 8) (haN0 : aN0.length = 8) (haP1 : aP1.length = 8) (haL1 : aL1.length = 8) (haC1 : aC1.length = 8) (haN2 : aN2.length = 8) (haP3 : aP3.length = 8) (haL3 : aL3.length = 8) (haC3 : aC3.length = 8)
    (R : DataMem → Prop) (S : Nat) (hS : S < 2 ^ 60) (hlo : lo.length = S + 8)
    (Heap : Nat → DataMem → Prop) (avail : Nat)
    (hguard : guard.toNat + 112 < s.regs.rsp.toNat) (hav : 128 ≤ avail)
    (hms : MakesliceC Heap E2e.Data.e2eU8Type_addr 1 (S + 8)) (hmm : MemmoveC (S + 8)) (st0 : MachineState),
    (st0.pc = Host.addrOf (k + 118)
        ∧ st0.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - 104 }
        ∧ st0.data.regs.rbp = { toBitVec := s.regs.rsp.toBitVec - 8 }
        ∧ st0.data.regs.r14 = s.regs.r14
        ∧ st0.data.regs.get64 Reg64.rax = 0
        ∧ st0.data.regs.get64 Reg64.rbx = 0 ∧
        ∃ (p1 : BitVec 64) (x0 x1 : List UInt8), x0.length = 24 ∧ x1.length = S + 8 ∧ 
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec + 32))
          ⋆ Eq (x0.At (s.regs.rsp.toBitVec - 104))
          ⋆ Eq (s28.At (s.regs.rsp.toBitVec - 64))
          ⋆ Eq (s30.At (s.regs.rsp.toBitVec - 56))
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 89)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 112))
          ⋆ Eq (x1.At (s.regs.rsp.toBitVec - 120 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Heap (avail - 32)
          ⋆ Eq (in0.At s.regs.rbx.toBitVec)
          ⋆ Eq (rt.At (s.regs.rbx.toBitVec + 8))
          ⋆ Eq (in1.At (s.regs.rbx.toBitVec + 40))
          ⋆ Eq (sig.At (s.regs.rbx.toBitVec + 48))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq (in0.At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 24))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 32))
          ⋆ Eq (in1.At (s.regs.rax.toBitVec + 40))
          ⋆ Eq (aP3.At (s.regs.rax.toBitVec + 48))
          ⋆ Eq (aL3.At (s.regs.rax.toBitVec + 56))
          ⋆ Eq (aC3.At (s.regs.rax.toBitVec + 64))
          ⋆ Eq (rt.At p1)
          ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec)
          ⋆ R) st0.data.dmem) →
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 156)
        ∧ st.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - 104 }
        ∧ st.data.regs.rbp = { toBitVec := s.regs.rsp.toBitVec - 8 }
        ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ (p1 p2 : BitVec 64) (x0 x1 : List UInt8), x0.length = 24 ∧ x1.length = S + 8 ∧ 
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec + 32))
          ⋆ Eq (x0.At (s.regs.rsp.toBitVec - 104))
          ⋆ Eq ((Int.toBytes 8 (0 : UInt64).toBitVec.toInt).At (s.regs.rsp.toBitVec - 64))
          ⋆ Eq ((Int.toBytes 8 (0 : UInt64).toBitVec.toInt).At (s.regs.rsp.toBitVec - 56))
          ⋆ Eq ((Int.toBytes 8 p2.toInt).At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 141)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 112))
          ⋆ Eq (x1.At (s.regs.rsp.toBitVec - 120 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Heap (avail - 128)
          ⋆ Eq (in0.At s.regs.rbx.toBitVec)
          ⋆ Eq (rt.At (s.regs.rbx.toBitVec + 8))
          ⋆ Eq (in1.At (s.regs.rbx.toBitVec + 40))
          ⋆ Eq (sig.At (s.regs.rbx.toBitVec + 48))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq (in0.At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 24))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 32))
          ⋆ Eq (in1.At (s.regs.rax.toBitVec + 40))
          ⋆ Eq ((Int.toBytes 8 p2.toInt).At (s.regs.rax.toBitVec + 48))
          ⋆ Eq ((Int.toBytes 8 96).At (s.regs.rax.toBitVec + 56))
          ⋆ Eq ((Int.toBytes 8 96).At (s.regs.rax.toBitVec + 64))
          ⋆ Eq (rt.At p1)
          ⋆ Eq (sig.At p2)
          ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec)
          ⋆ R) st.data.dmem)
      st0 := by
  intro k hk hf kS hkS hfS kV hkV hfV in0 rt in1 sig hin0 hrt hin1 hsig s ra guard fp s1 s2 s4 sp0 sp1 sp2 s28 s30 l38 rslot lo ast aN0 aP1 aL1 aC1 aN2 aP3 aL3 aC3 hfp hs1 hs2 hs4 hsp0 hsp1 hsp2 hs28 hs30 hl38 hrslot hast haN0 haP1 haL1 haC1 haN2 haP3 haL3 haC3 R S hS hlo Heap avail hguard hav hms hmm
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at hguard ⊢
  rintro ⟨d, pc⟩ ⟨hpc, hrsp, hrbp, hr14, hrrax, hrrbx, p1, x0, x1, hx0, hx1, Hm⟩
  dsimp only at hpc hrsp hrbp hr14 hrrax hrrbx Hm
  subst hpc
  obtain ⟨⟨rax1, rbx1, rcx1, rdx1, rsi1, rdi1, rsp1, rbp1, r81, r91, r101, r111, r121, r131, r141, r151⟩, zmms1, flags1, mem1⟩ := d
  simp only [Reg64s.get64] at hrsp hrbp hr14 hrrax hrrbx Hm
  subst rsp1 rbp1 r141
  obtain rfl : (0 : UInt64) = rax1 := (UInt64.toBitVec_inj.mp (show rax1.toBitVec = (0 : UInt64).toBitVec from hrrax)).symm
  obtain rfl : (0 : UInt64) = rbx1 := (UInt64.toBitVec_inj.mp (show rbx1.toBitVec = (0 : UInt64).toBitVec from hrrbx)).symm
  apply Gen.sm_g4dec_s118 k hk hf (rsp.toBitVec - 104) (rsp.toBitVec - 56) (by simp only [Int64.toBitVec_ofNat] <;> bv_omega) s30 hs30 _ _ _ (by rfl) (by ecancel)
  intro m118 H118; kn; simp only [Reg64s.get64] at H118
  apply Gen.sm_g4dec_s119 k hk hf (rsp.toBitVec - 104) (rsp.toBitVec - 64) (by simp only [Int64.toBitVec_ofNat] <;> bv_omega) s28 hs28 _ _ _ (by rfl) (by ecancel)
  intro m119 H119; kn; simp only [Reg64s.get64] at H119
  refine eventually_trans _ _ _ _ (Gen.sm_g4dec_Signature_seg k hk hf (rsp.toBitVec - 104) rax.toBitVec rbx.toBitVec
    (rsp.toBitVec + 8) (rsp.toBitVec + 16) (rsp.toBitVec - 48) (rsp.toBitVec - 112)
    (rsp.toBitVec - 120 - BitVec.ofNat 64 S) (rax.toBitVec + 48) (rax.toBitVec + 56) (rax.toBitVec + 64) (rbx.toBitVec + 48) (S + 8)
    (by simp only [Int64.toBitVec_ofNat] <;> bv_omega) (by simp only [Int64.toBitVec_ofNat] <;> bv_omega) (by simp only [Int64.toBitVec_ofNat] <;> bv_omega) (by bv_omega) (g5_lo _ 104 120 S (by decide))
    (by simp only [Int64.toBitVec_ofNat] <;> bv_omega) (by simp only [Int64.toBitVec_ofNat] <;> bv_omega) (by simp only [Int64.toBitVec_ofNat] <;> bv_omega) (by simp only [Int64.toBitVec_ofNat] <;> bv_omega)
    { toBitVec := rsp.toBitVec - 8#64 } r14 sig hsig
    x0 (Int.toBytes 8 (Host.addrOf (k + 89)).toBitVec.toInt) x1 (Int.toBytes 8 p1.toInt) aP3 aL3 aC3
    hx0 (Int.toBytes_length 8 _) hx1 (Int.toBytes_length 8 _) haP3 haL3 haC3
    _ Heap (avail - 32) (by omega) _ (by rfl) (by rfl) (by rfl)
      (by ecancel) hms hmm) ?_
  rintro ⟨d', pc'⟩ ⟨hpc', hrsp', hrbp', hr14', p2, spl', lo', hspl', hlo', hrY, Hm'⟩
  dsimp only at hpc' hrsp' hrbp' hr14' hrY Hm'
  subst hpc'
  obtain ⟨⟨rax2, rbx2, rcx2, rdx2, rsi2, rdi2, rsp2, rbp2, r82, r92, r102, r112, r122, r132, r142, r152⟩, zmms2, flags2, mem2⟩ := d'
  simp only at hrsp' hrbp' hr14' hrY Hm'
  subst rsp2 rbp2 r142
  apply Gen.sm_g4dec_s146 k hk hf (rsp.toBitVec - 104) (rsp.toBitVec - 48) p2 (by simp only [Int64.toBitVec_ofNat] <;> bv_omega) _ _ _ (by rfl) (by ecancel)
  kn
  apply Gen.sm_g4dec_s147 k hk hf
  apply Gen.sm_g4dec_s154 k hk hf
  apply Gen.sm_g4dec_s155 k hk hf rax.toBitVec (rax.toBitVec + 48) (by simp only [Int64.toBitVec_ofNat] <;> bv_omega) (Int.toBytes 8 p2.toInt) (Int.toBytes_length 8 _) _ _ _
    (by exact hrY) (by ecancel)
  intro m' H
  kn
  simp only [Reg64s.get64] at H
  apply Eventually.done
  refine ⟨rfl, rfl, rfl, rfl, p1, p2, spl', lo', hspl', hlo', ?_⟩
  dsimp only
  rw [show k + 140 + 1 = k + 141 from rfl] at H
  rw [show avail - 32 - 96 = avail - 128 by omega] at H
  ecancel
theorem sm_g5_f4_kind : ∀ (h : Host), type_of% (@sm_g5_f4 h)
    = @E2eScal.decFieldKindN h SmUnmarshal (E2eScal.layMix60 [E2eAd.Code.SlUnmarshal, E2eScal.BhCode.ViUnmarshal] 141 1) [.u64, .bytes 32, .u64, .bytes 96]
    ⟨118, 3, [(.rax, .zero), (.rbx, .zero)],
      [.at (.dn 8) (.reg .rbp), .at (.up 8) (.reg .rax), .at (.up 16) (.reg .rbx), .at (.up 32) (.reg .rdi), .at (.dn 104) (.ex 0), .at (.dn 64) (.orig 7), .at (.dn 56) (.orig 8), .at (.dn 48) (.ptr 0), .at (.dn 112) (.ret 89), .lo (.ex 1)],
      [.n 24, .lo]⟩
    ⟨156, 4, [],
      [.at (.dn 8) (.reg .rbp), .at (.up 8) (.reg .rax), .at (.up 16) (.reg .rbx), .at (.up 32) (.reg .rdi), .at (.dn 104) (.ex 0), .at (.dn 64) .zero, .at (.dn 56) .zero, .at (.dn 48) (.ptr 1), .at (.dn 112) (.ret 141), .lo (.ex 1)],
      [.n 24, .lo]⟩ := by
  intro h; rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Epilogue: boundary state 4 (directive 156) → return. -/
theorem sm_g5_epi : ∀ (k : Nat) (hk : SmUnmarshal.IsInfixAt Host.prog k) (hf : LabelsFresh SmUnmarshal k)
    (kS : Nat) (hkS : E2eAd.Code.SlUnmarshal.IsInfixAt Host.prog kS) (hfS : LabelsFresh E2eAd.Code.SlUnmarshal kS)
    (kV : Nat) (hkV : E2eScal.BhCode.ViUnmarshal.IsInfixAt Host.prog kV) (hfV : LabelsFresh E2eScal.BhCode.ViUnmarshal kV)
    (in0 rt in1 sig : List UInt8) (hin0 : in0.length = 8) (hrt : rt.length = 32) (hin1 : in1.length = 8) (hsig : sig.length = 96)
    (s : MachineData) (ra guard : UInt64)
    (fp s1 s2 s4 sp0 sp1 sp2 s28 s30 l38 rslot lo ast aN0 aP1 aL1 aC1 aN2 aP3 aL3 aC3 : List UInt8)
    (hfp : fp.length = 8) (hs1 : s1.length = 8) (hs2 : s2.length = 8) (hs4 : s4.length = 8) (hsp0 : sp0.length = 8) (hsp1 : sp1.length = 8) (hsp2 : sp2.length = 8) (hs28 : s28.length = 8) (hs30 : s30.length = 8) (hl38 : l38.length = 8) (hrslot : rslot.length = 8) (hast : ast.length = 8) (haN0 : aN0.length = 8) (haP1 : aP1.length = 8) (haL1 : aL1.length = 8) (haC1 : aC1.length = 8) (haN2 : aN2.length = 8) (haP3 : aP3.length = 8) (haL3 : aL3.length = 8) (haC3 : aC3.length = 8)
    (R : DataMem → Prop) (S : Nat) (hS : S < 2 ^ 60) (hlo : lo.length = S + 8)
    (Heap : Nat → DataMem → Prop) (avail : Nat)
    (st0 : MachineState),
    (st0.pc = Host.addrOf (k + 156)
        ∧ st0.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - 104 }
        ∧ st0.data.regs.rbp = { toBitVec := s.regs.rsp.toBitVec - 8 }
        ∧ st0.data.regs.r14 = s.regs.r14 ∧
        ∃ (p1 p2 : BitVec 64) (x0 x1 : List UInt8), x0.length = 24 ∧ x1.length = S + 8 ∧ 
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec + 32))
          ⋆ Eq (x0.At (s.regs.rsp.toBitVec - 104))
          ⋆ Eq ((Int.toBytes 8 (0 : UInt64).toBitVec.toInt).At (s.regs.rsp.toBitVec - 64))
          ⋆ Eq ((Int.toBytes 8 (0 : UInt64).toBitVec.toInt).At (s.regs.rsp.toBitVec - 56))
          ⋆ Eq ((Int.toBytes 8 p2.toInt).At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 141)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 112))
          ⋆ Eq (x1.At (s.regs.rsp.toBitVec - 120 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Heap (avail - 128)
          ⋆ Eq (in0.At s.regs.rbx.toBitVec)
          ⋆ Eq (rt.At (s.regs.rbx.toBitVec + 8))
          ⋆ Eq (in1.At (s.regs.rbx.toBitVec + 40))
          ⋆ Eq (sig.At (s.regs.rbx.toBitVec + 48))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq (in0.At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 24))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 32))
          ⋆ Eq (in1.At (s.regs.rax.toBitVec + 40))
          ⋆ Eq ((Int.toBytes 8 p2.toInt).At (s.regs.rax.toBitVec + 48))
          ⋆ Eq ((Int.toBytes 8 96).At (s.regs.rax.toBitVec + 56))
          ⋆ Eq ((Int.toBytes 8 96).At (s.regs.rax.toBitVec + 64))
          ⋆ Eq (rt.At p1)
          ⋆ Eq (sig.At p2)
          ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec)
          ⋆ R) st0.data.dmem) →
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ (p1 p2 : BitVec 64) (x0 x1 : List UInt8), x0.length = 24 ∧ x1.length = S + 8 ∧ 
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec + 32))
          ⋆ Eq (x0.At (s.regs.rsp.toBitVec - 104))
          ⋆ Eq ((Int.toBytes 8 (0 : UInt64).toBitVec.toInt).At (s.regs.rsp.toBitVec - 64))
          ⋆ Eq ((Int.toBytes 8 (0 : UInt64).toBitVec.toInt).At (s.regs.rsp.toBitVec - 56))
          ⋆ Eq ((Int.toBytes 8 p2.toInt).At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 141)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 112))
          ⋆ Eq (x1.At (s.regs.rsp.toBitVec - 120 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Heap (avail - 128)
          ⋆ Eq (in0.At s.regs.rbx.toBitVec)
          ⋆ Eq (rt.At (s.regs.rbx.toBitVec + 8))
          ⋆ Eq (in1.At (s.regs.rbx.toBitVec + 40))
          ⋆ Eq (sig.At (s.regs.rbx.toBitVec + 48))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq (in0.At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 24))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 32))
          ⋆ Eq (in1.At (s.regs.rax.toBitVec + 40))
          ⋆ Eq ((Int.toBytes 8 p2.toInt).At (s.regs.rax.toBitVec + 48))
          ⋆ Eq ((Int.toBytes 8 96).At (s.regs.rax.toBitVec + 56))
          ⋆ Eq ((Int.toBytes 8 96).At (s.regs.rax.toBitVec + 64))
          ⋆ Eq (rt.At p1)
          ⋆ Eq (sig.At p2)
          ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec)
          ⋆ R) st.data.dmem)
      st0 := by
  intro k hk hf kS hkS hfS kV hkV hfV in0 rt in1 sig hin0 hrt hin1 hsig s ra guard fp s1 s2 s4 sp0 sp1 sp2 s28 s30 l38 rslot lo ast aN0 aP1 aL1 aC1 aN2 aP3 aL3 aC3 hfp hs1 hs2 hs4 hsp0 hsp1 hsp2 hs28 hs30 hl38 hrslot hast haN0 haP1 haL1 haC1 haN2 haP3 haL3 haC3 R S hS hlo Heap avail
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at ⊢
  rintro ⟨d, pc⟩ ⟨hpc, hrsp, hrbp, hr14, p1, p2, x0, x1, hx0, hx1, Hm⟩
  dsimp only at hpc hrsp hrbp hr14  Hm
  subst hpc
  obtain ⟨⟨rax1, rbx1, rcx1, rdx1, rsi1, rdi1, rsp1, rbp1, r81, r91, r101, r111, r121, r131, r141, r151⟩, zmms1, flags1, mem1⟩ := d
  simp only [Reg64s.get64] at hrsp hrbp hr14  Hm
  subst rsp1 rbp1 r141
  apply kstep_ldv Reg64.rax Reg64.rsp 40 _ (k + 156) (k + 157) (win hk 156 1) (by rfl) (by rfl)
    (rsp.toBitVec - 104) (rsp.toBitVec - 64) (0 : UInt64).toBitVec (by simp only [Int64.toBitVec_ofNat] <;> bv_omega) _ _ _ (by rfl) (by ecancel)
  kn
  apply kstep_ldv Reg64.rbx Reg64.rsp 48 _ (k + 157) (k + 158) (win hk 157 1) (by rfl) (by rfl)
    (rsp.toBitVec - 104) (rsp.toBitVec - 56) (0 : UInt64).toBitVec (by simp only [Int64.toBitVec_ofNat] <;> bv_omega) _ _ _ (by rfl) (by ecancel)
  kn
  refine eventually_trans _ _ _ _ (decepi_n 96 _ (k + 158) (k + 159) (win hk 158 1) (by rfl) (by rfl)
    _ (win hk 159 2) (by rfl) (rsp.toBitVec - 104) (rsp.toBitVec - 8) rsp.toBitVec
    (by simp only [Int64.toBitVec_ofNat] <;> bv_omega) (by bv_omega) rbp ra _ _ (by rfl) (by ecancel)) ?_
  rintro ⟨d', pc'⟩ ⟨hpc', hrax', hrbx', hrsp', hrbp', hr14', hmem'⟩
  dsimp only at hpc' hrax' hrbx' hrsp' hrbp' hr14' hmem'
  apply Eventually.done
  refine ⟨hpc', hrax', hrbx', ?_, hrbp', hr14', p1, p2, x0, x1, hx0, hx1, ?_⟩
  · rw [hrsp']; apply UInt64.toBitVec_inj.mp
    first
      | (simp only [UInt64.toBitVec_add, UInt64.toBitVec_ofNat]; done)
      | (simp only [UInt64.toBitVec_add, UInt64.toBitVec_ofNat]; bv_omega)
  · dsimp only; rw [hmem']; ecancel
theorem sm_g5_epi_kind : ∀ (h : Host), type_of% (@sm_g5_epi h)
    = @E2eScal.decEpiKindN h SmUnmarshal (E2eScal.layMix60 [E2eAd.Code.SlUnmarshal, E2eScal.BhCode.ViUnmarshal] 141 1) [.u64, .bytes 32, .u64, .bytes 96]
    ⟨156, 4, [],
      [.at (.dn 8) (.reg .rbp), .at (.up 8) (.reg .rax), .at (.up 16) (.reg .rbx), .at (.up 32) (.reg .rdi), .at (.dn 104) (.ex 0), .at (.dn 64) .zero, .at (.dn 56) .zero, .at (.dn 48) (.ptr 1), .at (.dn 112) (.ret 141), .lo (.ex 1)],
      [.n 24, .lo]⟩ := by
  intro h; rfl

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
/-- **Accept path of `(*v1alpha1.SyncCommitteeMessage).UnmarshalSSZ` (Go 1.26.10), generated-style proof**: head, one theorem per
field, epilogue, chained by `eventually_trans`. Statement = the kind instance (`_kind`). -/
theorem sm_e2e_accept_g5 : ∀ (k : Nat) (hk : SmUnmarshal.IsInfixAt Host.prog k) (hf : LabelsFresh SmUnmarshal k)
    (kS : Nat) (hkS : E2eAd.Code.SlUnmarshal.IsInfixAt Host.prog kS) (hfS : LabelsFresh E2eAd.Code.SlUnmarshal kS)
    (kV : Nat) (hkV : E2eScal.BhCode.ViUnmarshal.IsInfixAt Host.prog kV) (hfV : LabelsFresh E2eScal.BhCode.ViUnmarshal kV)
    (in0 rt in1 sig : List UInt8) (hin0 : in0.length = 8) (hrt : rt.length = 32) (hin1 : in1.length = 8) (hsig : sig.length = 96)
    (s : MachineData) (ra guard : UInt64)
    (fp s1 s2 s4 sp0 sp1 sp2 s28 s30 l38 rslot lo ast aN0 aP1 aL1 aC1 aN2 aP3 aL3 aC3 : List UInt8)
    (hfp : fp.length = 8) (hs1 : s1.length = 8) (hs2 : s2.length = 8) (hs4 : s4.length = 8) (hsp0 : sp0.length = 8) (hsp1 : sp1.length = 8) (hsp2 : sp2.length = 8) (hs28 : s28.length = 8) (hs30 : s30.length = 8) (hl38 : l38.length = 8) (hrslot : rslot.length = 8) (hast : ast.length = 8) (haN0 : aN0.length = 8) (haP1 : aP1.length = 8) (haL1 : aL1.length = 8) (haC1 : aC1.length = 8) (haN2 : aN2.length = 8) (haP3 : aP3.length = 8) (haL3 : aL3.length = 8) (haC3 : aC3.length = 8)
    (R : DataMem → Prop) (S : Nat) (hS : S < 2 ^ 60) (hlo : lo.length = S + 8)
    (Heap : Nat → DataMem → Prop) (avail : Nat)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8))
      ⋆ Eq (s1.At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq (s4.At (s.regs.rsp.toBitVec + 32))
      ⋆ Eq (sp0.At (s.regs.rsp.toBitVec - 104))
      ⋆ Eq (sp1.At (s.regs.rsp.toBitVec - 96))
      ⋆ Eq (sp2.At (s.regs.rsp.toBitVec - 88))
      ⋆ Eq (s28.At (s.regs.rsp.toBitVec - 64))
      ⋆ Eq (s30.At (s.regs.rsp.toBitVec - 56))
      ⋆ Eq (l38.At (s.regs.rsp.toBitVec - 48))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 112))
      ⋆ Eq (lo.At (s.regs.rsp.toBitVec - 120 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Heap avail
      ⋆ Eq (in0.At s.regs.rbx.toBitVec)
      ⋆ Eq (rt.At (s.regs.rbx.toBitVec + 8))
      ⋆ Eq (in1.At (s.regs.rbx.toBitVec + 40))
      ⋆ Eq (sig.At (s.regs.rbx.toBitVec + 48))
      ⋆ Eq (ast.At s.regs.rax.toBitVec)
      ⋆ Eq (aN0.At (s.regs.rax.toBitVec + 8))
      ⋆ Eq (aP1.At (s.regs.rax.toBitVec + 16))
      ⋆ Eq (aL1.At (s.regs.rax.toBitVec + 24))
      ⋆ Eq (aC1.At (s.regs.rax.toBitVec + 32))
      ⋆ Eq (aN2.At (s.regs.rax.toBitVec + 40))
      ⋆ Eq (aP3.At (s.regs.rax.toBitVec + 48))
      ⋆ Eq (aL3.At (s.regs.rax.toBitVec + 56))
      ⋆ Eq (aC3.At (s.regs.rax.toBitVec + 64))
      ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec)
      ⋆ R)
    (hguard : guard.toNat + 112 < s.regs.rsp.toNat) (hlen : s.regs.rcx = 144) (hav : 128 ≤ avail)
    (hms : MakesliceC Heap E2e.Data.e2eU8Type_addr 1 (S + 8)) (hmm : MemmoveC (S + 8)),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ (p1 p2 : BitVec 64) (x0 x1 : List UInt8), x0.length = 24 ∧ x1.length = S + 8 ∧ 
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec + 32))
          ⋆ Eq (x0.At (s.regs.rsp.toBitVec - 104))
          ⋆ Eq ((Int.toBytes 8 (0 : UInt64).toBitVec.toInt).At (s.regs.rsp.toBitVec - 64))
          ⋆ Eq ((Int.toBytes 8 (0 : UInt64).toBitVec.toInt).At (s.regs.rsp.toBitVec - 56))
          ⋆ Eq ((Int.toBytes 8 p2.toInt).At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 141)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 112))
          ⋆ Eq (x1.At (s.regs.rsp.toBitVec - 120 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Heap (avail - 128)
          ⋆ Eq (in0.At s.regs.rbx.toBitVec)
          ⋆ Eq (rt.At (s.regs.rbx.toBitVec + 8))
          ⋆ Eq (in1.At (s.regs.rbx.toBitVec + 40))
          ⋆ Eq (sig.At (s.regs.rbx.toBitVec + 48))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq (in0.At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 24))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 32))
          ⋆ Eq (in1.At (s.regs.rax.toBitVec + 40))
          ⋆ Eq ((Int.toBytes 8 p2.toInt).At (s.regs.rax.toBitVec + 48))
          ⋆ Eq ((Int.toBytes 8 96).At (s.regs.rax.toBitVec + 56))
          ⋆ Eq ((Int.toBytes 8 96).At (s.regs.rax.toBitVec + 64))
          ⋆ Eq (rt.At p1)
          ⋆ Eq (sig.At p2)
          ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec)
          ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  intro k hk hf kS hkS hfS kV hkV hfV in0 rt in1 sig hin0 hrt hin1 hsig s ra guard fp s1 s2 s4 sp0 sp1 sp2 s28 s30 l38 rslot lo ast aN0 aP1 aL1 aC1 aN2 aP3 aL3 aC3 hfp hs1 hs2 hs4 hsp0 hsp1 hsp2 hs28 hs30 hl38 hrslot hast haN0 haP1 haL1 haC1 haN2 haP3 haL3 haC3 R S hS hlo Heap avail h_mem hguard hlen hav hms hmm
  refine eventually_trans _ _ _ _ (sm_g5_head k hk hf kS hkS hfS kV hkV hfV in0 rt in1 sig hin0 hrt hin1 hsig s ra guard fp s1 s2 s4 sp0 sp1 sp2 s28 s30 l38 rslot lo ast aN0 aP1 aL1 aC1 aN2 aP3 aL3 aC3 hfp hs1 hs2 hs4 hsp0 hsp1 hsp2 hs28 hs30 hl38 hrslot hast haN0 haP1 haL1 haC1 haN2 haP3 haL3 haC3 R S hS hlo Heap avail h_mem hguard hlen hav hms hmm) ?_
  intro st0 h0
  refine eventually_trans _ _ _ _ (sm_g5_f1 k hk hf kS hkS hfS kV hkV hfV in0 rt in1 sig hin0 hrt hin1 hsig s ra guard fp s1 s2 s4 sp0 sp1 sp2 s28 s30 l38 rslot lo ast aN0 aP1 aL1 aC1 aN2 aP3 aL3 aC3 hfp hs1 hs2 hs4 hsp0 hsp1 hsp2 hs28 hs30 hl38 hrslot hast haN0 haP1 haL1 haC1 haN2 haP3 haL3 haC3 R S hS hlo Heap avail hguard hav hms hmm st0 h0) ?_
  intro st1 h1
  refine eventually_trans _ _ _ _ (sm_g5_f2 k hk hf kS hkS hfS kV hkV hfV in0 rt in1 sig hin0 hrt hin1 hsig s ra guard fp s1 s2 s4 sp0 sp1 sp2 s28 s30 l38 rslot lo ast aN0 aP1 aL1 aC1 aN2 aP3 aL3 aC3 hfp hs1 hs2 hs4 hsp0 hsp1 hsp2 hs28 hs30 hl38 hrslot hast haN0 haP1 haL1 haC1 haN2 haP3 haL3 haC3 R S hS hlo Heap avail hguard hav hms hmm st1 h1) ?_
  intro st2 h2
  refine eventually_trans _ _ _ _ (sm_g5_f3 k hk hf kS hkS hfS kV hkV hfV in0 rt in1 sig hin0 hrt hin1 hsig s ra guard fp s1 s2 s4 sp0 sp1 sp2 s28 s30 l38 rslot lo ast aN0 aP1 aL1 aC1 aN2 aP3 aL3 aC3 hfp hs1 hs2 hs4 hsp0 hsp1 hsp2 hs28 hs30 hl38 hrslot hast haN0 haP1 haL1 haC1 haN2 haP3 haL3 haC3 R S hS hlo Heap avail hguard hav hms hmm st2 h2) ?_
  intro st3 h3
  refine eventually_trans _ _ _ _ (sm_g5_f4 k hk hf kS hkS hfS kV hkV hfV in0 rt in1 sig hin0 hrt hin1 hsig s ra guard fp s1 s2 s4 sp0 sp1 sp2 s28 s30 l38 rslot lo ast aN0 aP1 aL1 aC1 aN2 aP3 aL3 aC3 hfp hs1 hs2 hs4 hsp0 hsp1 hsp2 hs28 hs30 hl38 hrslot hast haN0 haP1 haL1 haC1 haN2 haP3 haL3 haC3 R S hS hlo Heap avail hguard hav hms hmm st3 h3) ?_
  intro st4 h4
  exact sm_g5_epi k hk hf kS hkS hfS kV hkV hfV in0 rt in1 sig hin0 hrt hin1 hsig s ra guard fp s1 s2 s4 sp0 sp1 sp2 s28 s30 l38 rslot lo ast aN0 aP1 aL1 aC1 aN2 aP3 aL3 aC3 hfp hs1 hs2 hs4 hsp0 hsp1 hsp2 hs28 hs30 hl38 hrslot hast haN0 haP1 haL1 haC1 haN2 haP3 haL3 haC3 R S hS hlo Heap avail st4 h4
theorem sm_e2e_accept_g5_kind : ∀ (h : Host), type_of% (@sm_e2e_accept_g5 h)
    = @E2eScal.decAcceptKindN h SmUnmarshal (E2eScal.layMix60 [E2eAd.Code.SlUnmarshal, E2eScal.BhCode.ViUnmarshal] 141 1) [.u64, .bytes 32, .u64, .bytes 96] := by
  intro h; rfl

/-- The generated-style theorem proves the committed hand statement `E2eScal.H5.sm_accept_stmt` (unchanged). -/
theorem sm_e2e_accept_g5_stmt : E2eScal.H5.sm_accept_stmt := sm_e2e_accept_g5

end E2eScal.Gen5
