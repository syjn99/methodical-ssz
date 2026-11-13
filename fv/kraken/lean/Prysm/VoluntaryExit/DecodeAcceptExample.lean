import Codec.Kind.DecodeAcceptAnyFrameInstances
import Codec.FieldFrame
import Prysm.ValidatorIndex.DecodeAcceptFunctionSpec
import Prysm.Epoch.DecodeAccept
import Prysm.Slot.DecodeAccept
import Prysm.VoluntaryExit.GeneratedDecodeSteps

/-!
# Worked example: `(*v1alpha1.VoluntaryExit).UnmarshalSSZ`, accept theorem in generated style

Text produced from one description of the type (frame facts, field list, boundary states, chain theorem names)
by a scratch emitter (not in the tree); every theorem has a `_kind` line (`decHeadKindN`, `decFieldKindN`,
`decEpiKindN`, `decAcceptKindN`). The `decoder --steps` chain theorems (`Decode.generated_step_*`) are used as emitted.
This type has no hand accept statement: the statement is the kind instance of the frame class of
PendingConsolidation / PendingPartialWithdrawal (`layCal`), whose two hand statements are `rfl`-tied.
-/

open Machine Runtime Prysm.AttestationData.Code Prysm.VoluntaryExit.Code Codec
variable [Host]

namespace Prysm.VoluntaryExit

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Head: directives 0–14 (prologue, spills, nil check); entry → boundary state 0. -/
theorem Decode.example_head : ∀ (k : Nat) (hk : Code.unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh Code.unmarshalSSZ k)
    (kE : Nat) (hkE : Prysm.Epoch.Code.unmarshalSSZ.IsInfixAt Host.prog kE) (hfE : LabelsFresh Prysm.Epoch.Code.unmarshalSSZ kE)
    (kV : Nat) (hkV : Prysm.ValidatorIndex.Code.unmarshalSSZ.IsInfixAt Host.prog kV) (hfV : LabelsFresh Prysm.ValidatorIndex.Code.unmarshalSSZ kV)
    (in0 in1 : List UInt8) (hin0 : in0.length = 8) (hin1 : in1.length = 8)
    (s : MachineData) (ra guard : UInt64)
    (fp s1 s2 s4 sp1 rslot lo ast aN0 aN1 : List UInt8)
    (hfp : fp.length = 8) (hs1 : s1.length = 8) (hs2 : s2.length = 8) (hs4 : s4.length = 8) (hsp1 : sp1.length = 8) (hrslot : rslot.length = 8) (hlo : lo.length = 8) (hast : ast.length = 8) (haN0 : aN0.length = 8) (haN1 : aN1.length = 8)
    (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8))
      ⋆ Eq (s1.At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq (s4.At (s.regs.rsp.toBitVec + 32))
      ⋆ Eq (sp1.At (s.regs.rsp.toBitVec - 72))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 88))
      ⋆ Eq (lo.At (s.regs.rsp.toBitVec - 96))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq (in0.At s.regs.rbx.toBitVec)
      ⋆ Eq (in1.At (s.regs.rbx.toBitVec + 8))
      ⋆ Eq (ast.At s.regs.rax.toBitVec)
      ⋆ Eq (aN0.At (s.regs.rax.toBitVec + 8))
      ⋆ Eq (aN1.At (s.regs.rax.toBitVec + 16))
      ⋆ R)
    (hguard : guard.toNat + 88 < s.regs.rsp.toNat) (hlen : s.regs.rcx = 16),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 15)
        ∧ st.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - 80 }
        ∧ st.data.regs.rbp = { toBitVec := s.regs.rsp.toBitVec - 8 }
        ∧ st.data.regs.r14 = s.regs.r14
        ∧ st.data.regs.get64 Reg64.rax = s.regs.rax.toBitVec
        ∧ st.data.regs.get64 Reg64.rbx = s.regs.rbx.toBitVec ∧
        
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec + 32))
          ⋆ Eq (sp1.At (s.regs.rsp.toBitVec - 72))
          ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 88))
          ⋆ Eq (lo.At (s.regs.rsp.toBitVec - 96))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (in0.At s.regs.rbx.toBitVec)
          ⋆ Eq (in1.At (s.regs.rbx.toBitVec + 8))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq (aN0.At (s.regs.rax.toBitVec + 8))
          ⋆ Eq (aN1.At (s.regs.rax.toBitVec + 16))
          ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  intro k hk hf kE hkE hfE kV hkV hfV in0 in1 hin0 hin1 s ra guard fp s1 s2 s4 sp1 rslot lo ast aN0 aN1 hfp hs1 hs2 hs4 hsp1 hrslot hlo hast haN0 haN1 R h_mem hguard hlen
  have hcs : Eq (ast.At s.regs.rax.toBitVec) =
      Eq ((ast.take 1).At s.regs.rax.toBitVec) ⋆ Eq ((ast.drop 1).At (s.regs.rax.toBitVec + 1)) := by
    conv => lhs; rw [← List.take_append_drop 1 ast]
    exact at_app _ _ (by rw [List.length_take, hast]; rfl) (by simp [hast])
  rw [hcs] at h_mem
  refine eventually_trans _ _ _ _ (decpro_seg _ _ _ _ 72 96 16 _ k (k + 11) (win hk 0 11) (by rfl) (by rfl)
    s ra guard (s.regs.rsp.toBitVec - 80) (s.regs.rsp.toBitVec + 16)
    (by simp only [Int64.toBitVec_ofNat] <;> bv_omega) (by simp only [Int64.toBitVec_ofNat] <;> bv_omega)
    fp s2 hfp hs2 _ (by ecancel) (Nat.lt_of_le_of_lt (Nat.le_add_right _ 88) hguard) (by rw [hlen]; rfl)) ?_
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
  apply kstep_st Reg64.rax Reg64.rsp 88 _ (k + 11) (k + 12) (win hk 11 1) (by rfl) (by rfl)
    (s.regs.rsp.toBitVec - 80) (s.regs.rsp.toBitVec + 8) (by simp only [Int64.toBitVec_ofNat] <;> bv_omega)
    s1 hs1 _ _ _ (by rfl) (by ecancel)
  intro m11 H11; kn; simp only [Reg64s.get64] at H11
  apply kstep_st Reg64.rbx Reg64.rsp 96 _ (k + 12) (k + 13) (win hk 12 1) (by rfl) (by rfl)
    (s.regs.rsp.toBitVec - 80) (s.regs.rsp.toBitVec + 16) (by simp only [Int64.toBitVec_ofNat] <;> bv_omega)
    (Int.toBytes 8 s.regs.rbx.toBitVec.toInt) (Int.toBytes_length 8 _) _ _ _ (by rfl) (by ecancel)
  intro m12 H12; kn; simp only [Reg64s.get64] at H12
  apply kstep_st Reg64.rdi Reg64.rsp 112 _ (k + 13) (k + 14) (win hk 13 1) (by rfl) (by rfl)
    (s.regs.rsp.toBitVec - 80) (s.regs.rsp.toBitVec + 32) (by simp only [Int64.toBitVec_ofNat] <;> bv_omega)
    s4 hs4 _ _ _ (by rfl) (by ecancel)
  intro m13 H13; kn; simp only [Reg64s.get64] at H13
  apply kstep_nilchk Reg64.rax _ (k + 14) (k + 15) (win hk 14 1) (by rfl) (by rfl)
    s.regs.rax.toBitVec (ast.take 1) (by simp [hast]) _ _ _ (by rfl) (by ecancel)
  intro fl; kn
  apply Eventually.done
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  dsimp only
  rw [hcs]; simp only [Std.ExtHashMap.sep_assoc]
  ecancel
theorem Decode.example_head_kind : ∀ (h : Host), type_of% (@Decode.example_head h)
    = @Codec.decHeadKindN h Code.unmarshalSSZ (Codec.layCal [Prysm.Epoch.Code.unmarshalSSZ, Prysm.ValidatorIndex.Code.unmarshalSSZ] 56) [.u64, .u64]
    ⟨15, 0, [(.rax, .rcv), (.rbx, .bf)],
      [.at (.dn 8) (.reg .rbp), .at (.up 8) (.reg .rax), .at (.up 16) (.reg .rbx), .at (.up 32) (.reg .rdi), .at (.dn 72) (.orig 4), .at (.dn 88) (.orig 5), .at (.dn 96) (.orig 6)],
      []⟩ := by
  intro h; rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Field 1 `Epoch` (call): boundary state 0 (directive 15) → boundary state 1 (directive 48). -/
theorem Decode.example_f1 : ∀ (k : Nat) (hk : Code.unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh Code.unmarshalSSZ k)
    (kE : Nat) (hkE : Prysm.Epoch.Code.unmarshalSSZ.IsInfixAt Host.prog kE) (hfE : LabelsFresh Prysm.Epoch.Code.unmarshalSSZ kE)
    (kV : Nat) (hkV : Prysm.ValidatorIndex.Code.unmarshalSSZ.IsInfixAt Host.prog kV) (hfV : LabelsFresh Prysm.ValidatorIndex.Code.unmarshalSSZ kV)
    (in0 in1 : List UInt8) (hin0 : in0.length = 8) (hin1 : in1.length = 8)
    (s : MachineData) (ra guard : UInt64)
    (fp s1 s2 s4 sp1 rslot lo ast aN0 aN1 : List UInt8)
    (hfp : fp.length = 8) (hs1 : s1.length = 8) (hs2 : s2.length = 8) (hs4 : s4.length = 8) (hsp1 : sp1.length = 8) (hrslot : rslot.length = 8) (hlo : lo.length = 8) (hast : ast.length = 8) (haN0 : aN0.length = 8) (haN1 : aN1.length = 8)
    (R : DataMem → Prop)
    (hguard : guard.toNat + 88 < s.regs.rsp.toNat) (st0 : MachineState),
    (st0.pc = Host.addrOf (k + 15)
        ∧ st0.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - 80 }
        ∧ st0.data.regs.rbp = { toBitVec := s.regs.rsp.toBitVec - 8 }
        ∧ st0.data.regs.r14 = s.regs.r14
        ∧ st0.data.regs.get64 Reg64.rax = s.regs.rax.toBitVec
        ∧ st0.data.regs.get64 Reg64.rbx = s.regs.rbx.toBitVec ∧
        
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec + 32))
          ⋆ Eq (sp1.At (s.regs.rsp.toBitVec - 72))
          ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 88))
          ⋆ Eq (lo.At (s.regs.rsp.toBitVec - 96))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (in0.At s.regs.rbx.toBitVec)
          ⋆ Eq (in1.At (s.regs.rbx.toBitVec + 8))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq (aN0.At (s.regs.rax.toBitVec + 8))
          ⋆ Eq (aN1.At (s.regs.rax.toBitVec + 16))
          ⋆ R) st0.data.dmem) →
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 48)
        ∧ st.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - 80 }
        ∧ st.data.regs.rbp = { toBitVec := s.regs.rsp.toBitVec - 8 }
        ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ (x0 x1 : List UInt8), x0.length = 8 ∧ x1.length = 8 ∧ 
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec + 32))
          ⋆ Eq (x0.At (s.regs.rsp.toBitVec - 72))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 18)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 88))
          ⋆ Eq (x1.At (s.regs.rsp.toBitVec - 96))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (in0.At s.regs.rbx.toBitVec)
          ⋆ Eq (in1.At (s.regs.rbx.toBitVec + 8))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq (in0.At (s.regs.rax.toBitVec + 8))
          ⋆ Eq (aN1.At (s.regs.rax.toBitVec + 16))
          ⋆ R) st.data.dmem)
      st0 := by
  intro k hk hf kE hkE hfE kV hkV hfV in0 in1 hin0 hin1 s ra guard fp s1 s2 s4 sp1 rslot lo ast aN0 aN1 hfp hs1 hs2 hs4 hsp1 hrslot hlo hast haN0 haN1 R hguard
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
  have hC := Prysm.Epoch.Decode.accept_function_spec_holds kE hkE hfE
  have hg : guard.toNat < (rsp.toBitVec - 88).toNat := by
    have hgd : guard.toNat + 88 < rsp.toBitVec.toNat := hguard
    bv_omega
  apply Decode.generated_step_s15 k hk hf
  intro fl15; kn
  apply Decode.generated_step_s16 k hk hf
  kn
  refine eventually_trans _ _ _ _ (Decode.generated_step_Epoch_call k hk hf hC (rsp.toBitVec - 80) (rax.toBitVec + 8) rbx.toBitVec
    (rsp.toBitVec - 88) (rsp.toBitVec - 96) (rsp.toBitVec - 72) (by bv_omega) (by bv_omega) (by bv_omega)
    { toBitVec := rsp.toBitVec - 8#64 } r14 guard in0 rslot lo sp1 aN0
    hin0 hrslot hlo hsp1 haN0 hg _ _
    (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by first | rfl | decide) (by ecancel)) ?_
  rintro ⟨d', pc'⟩ ⟨hpc', hrax', hrbx', hrsp', hrbp', hr14', Hm'⟩
  dsimp only at hpc' hrax' hrbx' hrsp' hrbp' hr14' Hm'
  apply Eventually.done
  refine ⟨hpc', hrsp', hrbp', hr14', (Int.toBytes 8 rbx.toBitVec.toInt), (Int.toBytes 8 (rsp.toBitVec - 8#64).toInt),
    (Int.toBytes_length 8 _), (Int.toBytes_length 8 _), ?_⟩
  dsimp only
  rw [show k + 17 + 1 = k + 18 from rfl] at Hm'
  ecancel
theorem Decode.example_f1_kind : ∀ (h : Host), type_of% (@Decode.example_f1 h)
    = @Codec.decFieldKindN h Code.unmarshalSSZ (Codec.layCal [Prysm.Epoch.Code.unmarshalSSZ, Prysm.ValidatorIndex.Code.unmarshalSSZ] 56) [.u64, .u64]
    ⟨15, 0, [(.rax, .rcv), (.rbx, .bf)],
      [.at (.dn 8) (.reg .rbp), .at (.up 8) (.reg .rax), .at (.up 16) (.reg .rbx), .at (.up 32) (.reg .rdi), .at (.dn 72) (.orig 4), .at (.dn 88) (.orig 5), .at (.dn 96) (.orig 6)],
      []⟩
    ⟨48, 1, [],
      [.at (.dn 8) (.reg .rbp), .at (.up 8) (.reg .rax), .at (.up 16) (.reg .rbx), .at (.up 32) (.reg .rdi), .at (.dn 72) (.ex 0), .at (.dn 88) (.ret 18), .at (.dn 96) (.ex 1)],
      [.n 8, .n 8]⟩ := by
  intro h; rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Field 2 `ValidatorIndex` (call): boundary state 1 (directive 48) → boundary state 2 (directive 86). -/
theorem Decode.example_f2 : ∀ (k : Nat) (hk : Code.unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh Code.unmarshalSSZ k)
    (kE : Nat) (hkE : Prysm.Epoch.Code.unmarshalSSZ.IsInfixAt Host.prog kE) (hfE : LabelsFresh Prysm.Epoch.Code.unmarshalSSZ kE)
    (kV : Nat) (hkV : Prysm.ValidatorIndex.Code.unmarshalSSZ.IsInfixAt Host.prog kV) (hfV : LabelsFresh Prysm.ValidatorIndex.Code.unmarshalSSZ kV)
    (in0 in1 : List UInt8) (hin0 : in0.length = 8) (hin1 : in1.length = 8)
    (s : MachineData) (ra guard : UInt64)
    (fp s1 s2 s4 sp1 rslot lo ast aN0 aN1 : List UInt8)
    (hfp : fp.length = 8) (hs1 : s1.length = 8) (hs2 : s2.length = 8) (hs4 : s4.length = 8) (hsp1 : sp1.length = 8) (hrslot : rslot.length = 8) (hlo : lo.length = 8) (hast : ast.length = 8) (haN0 : aN0.length = 8) (haN1 : aN1.length = 8)
    (R : DataMem → Prop)
    (hguard : guard.toNat + 88 < s.regs.rsp.toNat) (st0 : MachineState),
    (st0.pc = Host.addrOf (k + 48)
        ∧ st0.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - 80 }
        ∧ st0.data.regs.rbp = { toBitVec := s.regs.rsp.toBitVec - 8 }
        ∧ st0.data.regs.r14 = s.regs.r14 ∧
        ∃ (x0 x1 : List UInt8), x0.length = 8 ∧ x1.length = 8 ∧ 
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec + 32))
          ⋆ Eq (x0.At (s.regs.rsp.toBitVec - 72))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 18)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 88))
          ⋆ Eq (x1.At (s.regs.rsp.toBitVec - 96))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (in0.At s.regs.rbx.toBitVec)
          ⋆ Eq (in1.At (s.regs.rbx.toBitVec + 8))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq (in0.At (s.regs.rax.toBitVec + 8))
          ⋆ Eq (aN1.At (s.regs.rax.toBitVec + 16))
          ⋆ R) st0.data.dmem) →
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 86)
        ∧ st.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - 80 }
        ∧ st.data.regs.rbp = { toBitVec := s.regs.rsp.toBitVec - 8 }
        ∧ st.data.regs.r14 = s.regs.r14
        ∧ st.data.regs.get64 Reg64.rax = 0
        ∧ st.data.regs.get64 Reg64.rbx = 0 ∧
        ∃ (x0 x1 : List UInt8), x0.length = 8 ∧ x1.length = 8 ∧ 
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec + 32))
          ⋆ Eq (x0.At (s.regs.rsp.toBitVec - 72))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 56)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 88))
          ⋆ Eq (x1.At (s.regs.rsp.toBitVec - 96))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (in0.At s.regs.rbx.toBitVec)
          ⋆ Eq (in1.At (s.regs.rbx.toBitVec + 8))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq (in0.At (s.regs.rax.toBitVec + 8))
          ⋆ Eq (in1.At (s.regs.rax.toBitVec + 16))
          ⋆ R) st.data.dmem)
      st0 := by
  intro k hk hf kE hkE hfE kV hkV hfV in0 in1 hin0 hin1 s ra guard fp s1 s2 s4 sp1 rslot lo ast aN0 aN1 hfp hs1 hs2 hs4 hsp1 hrslot hlo hast haN0 haN1 R hguard
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at hguard ⊢
  rintro ⟨d, pc⟩ ⟨hpc, hrsp, hrbp, hr14, x0, x1, hx0, hx1, Hm⟩
  dsimp only at hpc hrsp hrbp hr14  Hm
  subst hpc
  obtain ⟨⟨rax1, rbx1, rcx1, rdx1, rsi1, rdi1, rsp1, rbp1, r81, r91, r101, r111, r121, r131, r141, r151⟩, zmms1, flags1, mem1⟩ := d
  simp only [Reg64s.get64] at hrsp hrbp hr14  Hm
  subst rsp1 rbp1 r141
  have hC := Prysm.ValidatorIndex.Decode.accept_function_spec_holds kV hkV hfV
  have hg : guard.toNat < (rsp.toBitVec - 88).toNat := by
    have hgd : guard.toNat + 88 < rsp.toBitVec.toNat := hguard
    bv_omega
  apply Decode.generated_step_s48 k hk hf (rsp.toBitVec - 80) (rsp.toBitVec + 16) rbx.toBitVec (by simp only [Int64.toBitVec_ofNat] <;> bv_omega) _ _ _ (by rfl) (by ecancel)
  kn
  apply Decode.generated_step_s49 k hk hf
  intro fl49; kn
  apply Decode.generated_step_s50 k hk hf (rsp.toBitVec - 80) (rsp.toBitVec + 32) (by simp only [Int64.toBitVec_ofNat] <;> bv_omega) (Int.toBytes 8 rdi.toBitVec.toInt) (Int.toBytes_length 8 _) _ _ _ (by rfl) (by ecancel)
  kn
  apply Decode.generated_step_s51 k hk hf
  intro fl51; kn
  apply Decode.generated_step_s52 k hk hf (rsp.toBitVec - 80) (rsp.toBitVec + 8) rax.toBitVec (by simp only [Int64.toBitVec_ofNat] <;> bv_omega) _ _ _ (by rfl) (by ecancel)
  kn
  apply Decode.generated_step_s53 k hk hf
  intro fl53; kn
  apply Decode.generated_step_s54 k hk hf
  kn
  refine eventually_trans _ _ _ _ (Decode.generated_step_ValidatorIndex_call k hk hf hC (rsp.toBitVec - 80) (rax.toBitVec + 16) (rbx.toBitVec + 8)
    (rsp.toBitVec - 88) (rsp.toBitVec - 96) (rsp.toBitVec - 72) (by bv_omega) (by bv_omega) (by bv_omega)
    { toBitVec := rsp.toBitVec - 8#64 } r14 guard in1 (Int.toBytes 8 (Host.addrOf (k + 18)).toBitVec.toInt) x1 x0 aN1
    hin1 (Int.toBytes_length 8 _) hx1 hx0 haN1 hg _ _
    (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by first | rfl | decide) (by ecancel)) ?_
  rintro ⟨d', pc'⟩ ⟨hpc', hrax', hrbx', hrsp', hrbp', hr14', Hm'⟩
  dsimp only at hpc' hrax' hrbx' hrsp' hrbp' hr14' Hm'
  apply Eventually.done
  refine ⟨hpc', hrsp', hrbp', hr14', (congrArg UInt64.toBitVec hrax'), (congrArg UInt64.toBitVec hrbx'), (Int.toBytes 8 (rbx.toBitVec + 8).toInt), (Int.toBytes 8 (rsp.toBitVec - 8#64).toInt),
    (Int.toBytes_length 8 _), (Int.toBytes_length 8 _), ?_⟩
  dsimp only
  rw [show k + 55 + 1 = k + 56 from rfl] at Hm'
  ecancel
theorem Decode.example_f2_kind : ∀ (h : Host), type_of% (@Decode.example_f2 h)
    = @Codec.decFieldKindN h Code.unmarshalSSZ (Codec.layCal [Prysm.Epoch.Code.unmarshalSSZ, Prysm.ValidatorIndex.Code.unmarshalSSZ] 56) [.u64, .u64]
    ⟨48, 1, [],
      [.at (.dn 8) (.reg .rbp), .at (.up 8) (.reg .rax), .at (.up 16) (.reg .rbx), .at (.up 32) (.reg .rdi), .at (.dn 72) (.ex 0), .at (.dn 88) (.ret 18), .at (.dn 96) (.ex 1)],
      [.n 8, .n 8]⟩
    ⟨86, 2, [(.rax, .zero), (.rbx, .zero)],
      [.at (.dn 8) (.reg .rbp), .at (.up 8) (.reg .rax), .at (.up 16) (.reg .rbx), .at (.up 32) (.reg .rdi), .at (.dn 72) (.ex 0), .at (.dn 88) (.ret 56), .at (.dn 96) (.ex 1)],
      [.n 8, .n 8]⟩ := by
  intro h; rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Epilogue: boundary state 2 (directive 86) → return. -/
theorem Decode.example_epi : ∀ (k : Nat) (hk : Code.unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh Code.unmarshalSSZ k)
    (kE : Nat) (hkE : Prysm.Epoch.Code.unmarshalSSZ.IsInfixAt Host.prog kE) (hfE : LabelsFresh Prysm.Epoch.Code.unmarshalSSZ kE)
    (kV : Nat) (hkV : Prysm.ValidatorIndex.Code.unmarshalSSZ.IsInfixAt Host.prog kV) (hfV : LabelsFresh Prysm.ValidatorIndex.Code.unmarshalSSZ kV)
    (in0 in1 : List UInt8) (hin0 : in0.length = 8) (hin1 : in1.length = 8)
    (s : MachineData) (ra guard : UInt64)
    (fp s1 s2 s4 sp1 rslot lo ast aN0 aN1 : List UInt8)
    (hfp : fp.length = 8) (hs1 : s1.length = 8) (hs2 : s2.length = 8) (hs4 : s4.length = 8) (hsp1 : sp1.length = 8) (hrslot : rslot.length = 8) (hlo : lo.length = 8) (hast : ast.length = 8) (haN0 : aN0.length = 8) (haN1 : aN1.length = 8)
    (R : DataMem → Prop)
    (st0 : MachineState),
    (st0.pc = Host.addrOf (k + 86)
        ∧ st0.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - 80 }
        ∧ st0.data.regs.rbp = { toBitVec := s.regs.rsp.toBitVec - 8 }
        ∧ st0.data.regs.r14 = s.regs.r14
        ∧ st0.data.regs.get64 Reg64.rax = 0
        ∧ st0.data.regs.get64 Reg64.rbx = 0 ∧
        ∃ (x0 x1 : List UInt8), x0.length = 8 ∧ x1.length = 8 ∧ 
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec + 32))
          ⋆ Eq (x0.At (s.regs.rsp.toBitVec - 72))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 56)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 88))
          ⋆ Eq (x1.At (s.regs.rsp.toBitVec - 96))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (in0.At s.regs.rbx.toBitVec)
          ⋆ Eq (in1.At (s.regs.rbx.toBitVec + 8))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq (in0.At (s.regs.rax.toBitVec + 8))
          ⋆ Eq (in1.At (s.regs.rax.toBitVec + 16))
          ⋆ R) st0.data.dmem) →
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ (x0 x1 : List UInt8), x0.length = 8 ∧ x1.length = 8 ∧ 
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec + 32))
          ⋆ Eq (x0.At (s.regs.rsp.toBitVec - 72))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 56)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 88))
          ⋆ Eq (x1.At (s.regs.rsp.toBitVec - 96))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (in0.At s.regs.rbx.toBitVec)
          ⋆ Eq (in1.At (s.regs.rbx.toBitVec + 8))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq (in0.At (s.regs.rax.toBitVec + 8))
          ⋆ Eq (in1.At (s.regs.rax.toBitVec + 16))
          ⋆ R) st.data.dmem)
      st0 := by
  intro k hk hf kE hkE hfE kV hkV hfV in0 in1 hin0 hin1 s ra guard fp s1 s2 s4 sp1 rslot lo ast aN0 aN1 hfp hs1 hs2 hs4 hsp1 hrslot hlo hast haN0 haN1 R
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at ⊢
  rintro ⟨d, pc⟩ ⟨hpc, hrsp, hrbp, hr14, hrrax, hrrbx, x0, x1, hx0, hx1, Hm⟩
  dsimp only at hpc hrsp hrbp hr14 hrrax hrrbx Hm
  subst hpc
  obtain ⟨⟨rax1, rbx1, rcx1, rdx1, rsi1, rdi1, rsp1, rbp1, r81, r91, r101, r111, r121, r131, r141, r151⟩, zmms1, flags1, mem1⟩ := d
  simp only [Reg64s.get64] at hrsp hrbp hr14 hrrax hrrbx Hm
  subst rsp1 rbp1 r141
  obtain rfl : (0 : UInt64) = rax1 := (UInt64.toBitVec_inj.mp (show rax1.toBitVec = (0 : UInt64).toBitVec from hrrax)).symm
  obtain rfl : (0 : UInt64) = rbx1 := (UInt64.toBitVec_inj.mp (show rbx1.toBitVec = (0 : UInt64).toBitVec from hrrbx)).symm
  refine eventually_trans _ _ _ _ (decepi_n 72 _ (k + 86) (k + 87) (win hk 86 1) (by rfl) (by rfl)
    _ (win hk 87 2) (by rfl) (rsp.toBitVec - 80) (rsp.toBitVec - 8) rsp.toBitVec
    (by simp only [Int64.toBitVec_ofNat] <;> bv_omega) (by bv_omega) rbp ra _ _ (by rfl) (by ecancel)) ?_
  rintro ⟨d', pc'⟩ ⟨hpc', hrax', hrbx', hrsp', hrbp', hr14', hmem'⟩
  dsimp only at hpc' hrax' hrbx' hrsp' hrbp' hr14' hmem'
  apply Eventually.done
  refine ⟨hpc', hrax', hrbx', ?_, hrbp', hr14', x0, x1, hx0, hx1, ?_⟩
  · rw [hrsp']; apply UInt64.toBitVec_inj.mp
    first
      | (simp only [UInt64.toBitVec_add, UInt64.toBitVec_ofNat]; done)
      | (simp only [UInt64.toBitVec_add, UInt64.toBitVec_ofNat]; bv_omega)
  · dsimp only; rw [hmem']; ecancel
theorem Decode.example_epi_kind : ∀ (h : Host), type_of% (@Decode.example_epi h)
    = @Codec.decEpiKindN h Code.unmarshalSSZ (Codec.layCal [Prysm.Epoch.Code.unmarshalSSZ, Prysm.ValidatorIndex.Code.unmarshalSSZ] 56) [.u64, .u64]
    ⟨86, 2, [(.rax, .zero), (.rbx, .zero)],
      [.at (.dn 8) (.reg .rbp), .at (.up 8) (.reg .rax), .at (.up 16) (.reg .rbx), .at (.up 32) (.reg .rdi), .at (.dn 72) (.ex 0), .at (.dn 88) (.ret 56), .at (.dn 96) (.ex 1)],
      [.n 8, .n 8]⟩ := by
  intro h; rfl

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
/-- **Accept path of `(*v1alpha1.VoluntaryExit).UnmarshalSSZ` (Go 1.26.10), generated-style proof**: head, one theorem per
field, epilogue, chained by `eventually_trans`. Statement = the kind instance (`_kind`). -/
theorem Decode.example_accept : ∀ (k : Nat) (hk : Code.unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh Code.unmarshalSSZ k)
    (kE : Nat) (hkE : Prysm.Epoch.Code.unmarshalSSZ.IsInfixAt Host.prog kE) (hfE : LabelsFresh Prysm.Epoch.Code.unmarshalSSZ kE)
    (kV : Nat) (hkV : Prysm.ValidatorIndex.Code.unmarshalSSZ.IsInfixAt Host.prog kV) (hfV : LabelsFresh Prysm.ValidatorIndex.Code.unmarshalSSZ kV)
    (in0 in1 : List UInt8) (hin0 : in0.length = 8) (hin1 : in1.length = 8)
    (s : MachineData) (ra guard : UInt64)
    (fp s1 s2 s4 sp1 rslot lo ast aN0 aN1 : List UInt8)
    (hfp : fp.length = 8) (hs1 : s1.length = 8) (hs2 : s2.length = 8) (hs4 : s4.length = 8) (hsp1 : sp1.length = 8) (hrslot : rslot.length = 8) (hlo : lo.length = 8) (hast : ast.length = 8) (haN0 : aN0.length = 8) (haN1 : aN1.length = 8)
    (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8))
      ⋆ Eq (s1.At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq (s4.At (s.regs.rsp.toBitVec + 32))
      ⋆ Eq (sp1.At (s.regs.rsp.toBitVec - 72))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 88))
      ⋆ Eq (lo.At (s.regs.rsp.toBitVec - 96))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq (in0.At s.regs.rbx.toBitVec)
      ⋆ Eq (in1.At (s.regs.rbx.toBitVec + 8))
      ⋆ Eq (ast.At s.regs.rax.toBitVec)
      ⋆ Eq (aN0.At (s.regs.rax.toBitVec + 8))
      ⋆ Eq (aN1.At (s.regs.rax.toBitVec + 16))
      ⋆ R)
    (hguard : guard.toNat + 88 < s.regs.rsp.toNat) (hlen : s.regs.rcx = 16),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ (x0 x1 : List UInt8), x0.length = 8 ∧ x1.length = 8 ∧ 
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec + 32))
          ⋆ Eq (x0.At (s.regs.rsp.toBitVec - 72))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 56)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 88))
          ⋆ Eq (x1.At (s.regs.rsp.toBitVec - 96))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (in0.At s.regs.rbx.toBitVec)
          ⋆ Eq (in1.At (s.regs.rbx.toBitVec + 8))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq (in0.At (s.regs.rax.toBitVec + 8))
          ⋆ Eq (in1.At (s.regs.rax.toBitVec + 16))
          ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  intro k hk hf kE hkE hfE kV hkV hfV in0 in1 hin0 hin1 s ra guard fp s1 s2 s4 sp1 rslot lo ast aN0 aN1 hfp hs1 hs2 hs4 hsp1 hrslot hlo hast haN0 haN1 R h_mem hguard hlen
  refine eventually_trans _ _ _ _ (Decode.example_head k hk hf kE hkE hfE kV hkV hfV in0 in1 hin0 hin1 s ra guard fp s1 s2 s4 sp1 rslot lo ast aN0 aN1 hfp hs1 hs2 hs4 hsp1 hrslot hlo hast haN0 haN1 R h_mem hguard hlen) ?_
  intro st0 h0
  refine eventually_trans _ _ _ _ (Decode.example_f1 k hk hf kE hkE hfE kV hkV hfV in0 in1 hin0 hin1 s ra guard fp s1 s2 s4 sp1 rslot lo ast aN0 aN1 hfp hs1 hs2 hs4 hsp1 hrslot hlo hast haN0 haN1 R hguard st0 h0) ?_
  intro st1 h1
  refine eventually_trans _ _ _ _ (Decode.example_f2 k hk hf kE hkE hfE kV hkV hfV in0 in1 hin0 hin1 s ra guard fp s1 s2 s4 sp1 rslot lo ast aN0 aN1 hfp hs1 hs2 hs4 hsp1 hrslot hlo hast haN0 haN1 R hguard st1 h1) ?_
  intro st2 h2
  exact Decode.example_epi k hk hf kE hkE hfE kV hkV hfV in0 in1 hin0 hin1 s ra guard fp s1 s2 s4 sp1 rslot lo ast aN0 aN1 hfp hs1 hs2 hs4 hsp1 hrslot hlo hast haN0 haN1 R st2 h2
theorem Decode.example_accept_kind : ∀ (h : Host), type_of% (@Decode.example_accept h)
    = @Codec.decAcceptKindN h Code.unmarshalSSZ (Codec.layCal [Prysm.Epoch.Code.unmarshalSSZ, Prysm.ValidatorIndex.Code.unmarshalSSZ] 56) [.u64, .u64] := by
  intro h; rfl

end Prysm.VoluntaryExit
