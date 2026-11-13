import Prysm.BeaconBlockHeader.DecodeAccept
import Prysm.BeaconBlockHeader.DecodeHeadFromCallSegments
import Prysm.BeaconBlockHeader.GeneratedDecodeCallSegments

/-!
# BeaconBlockHeader accept path from the GENERATED `decoder --call-segments` theorems (reuse demonstration)

Hand composition (not generator output). `Decode.head_from_generated_call_segments`: the chain of `Prysm/BeaconBlockHeader/DecodeHeadFromCallSegments.lean` with the four
call-site lemma instances replaced by the generated theorems of `Prysm/BeaconBlockHeader/GeneratedDecodeCallSegments.lean` (`decoder --call-segments`, raw output):
`bh_g3dec_Slot_arg` / `_call`, `bh_g3dec_ProposerIndex_arg` / `_call`; `Decode.head0` (0–14) and `Decode.spill2`
(86–87) stay hand steps. `Decode.accept_from_generated_call_segments`: the proof text of `Prysm/BeaconBlockHeader/DecodeAccept.lean` with `Decode.head` replaced
by `Decode.head_from_generated_call_segments` and the three hand root segments by the generated ones (`bh_g3dec_*_seg`, same statements); the
instance directives between the roots and the epilogue stay hand steps. Both declared types equal the existing
hand theorems by `rfl` (`_type`). In-sample (development data).
-/

open Machine Runtime Prysm.AttestationData.Code Prysm.BeaconBlockHeader.Code Codec
variable [Host]

namespace Prysm.BeaconBlockHeader

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
/-- Segment 1 of the BeaconBlockHeader decoder accept path from the GENERATED call-field theorems
(statement text of `Decode.head`). -/
theorem Decode.head_from_generated_call_segments (k : Nat) (hk : Code.unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh Code.unmarshalSSZ k)
    (hsl : Prysm.Slot.Decode.accept_function_spec) (hvi : Prysm.ValidatorIndex.Decode.accept_function_spec)
    (in0 in1 : List UInt8) (hin0 : in0.length = 8) (hin1 : in1.length = 8)
    (s : MachineData) (ra guard : UInt64)
    (fp s1 s2 s4 sp1 rslot lf ast a8 a16 s28 s30 : List UInt8)
    (hfp : fp.length = 8) (h1 : s1.length = 8) (h2 : s2.length = 8) (h4 : s4.length = 8)
    (hsp1 : sp1.length = 8) (hrs : rslot.length = 8) (hlf : lf.length = 8)
    (hast : ast.length = 8) (ha8 : a8.length = 8) (ha16 : a16.length = 8)
    (hs28 : s28.length = 8) (hs30 : s30.length = 8)
    (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s1.At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16)) ⋆ Eq (s4.At (s.regs.rsp.toBitVec + 32))
      ⋆ Eq (sp1.At (s.regs.rsp.toBitVec - 96)) ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 112))
      ⋆ Eq (lf.At (s.regs.rsp.toBitVec - 120))
      ⋆ Eq (s28.At (s.regs.rsp.toBitVec - 64)) ⋆ Eq (s30.At (s.regs.rsp.toBitVec - 56))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq (in0.At s.regs.rbx.toBitVec) ⋆ Eq (in1.At (s.regs.rbx.toBitVec + 8))
      ⋆ Eq (ast.At s.regs.rax.toBitVec) ⋆ Eq (a8.At (s.regs.rax.toBitVec + 8))
      ⋆ Eq (a16.At (s.regs.rax.toBitVec + 16)) ⋆ R)
    (hguard : guard.toNat + 112 < s.regs.rsp.toNat) (hlen : s.regs.rcx = 112) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 88) ∧ st.data.regs.rsp = s.regs.rsp - 104
        ∧ st.data.regs.rbp = s.regs.rsp - 8 ∧ st.data.regs.r14 = s.regs.r14 ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec + 32))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rbx.toBitVec + 8).toInt).At (s.regs.rsp.toBitVec - 96))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 56)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 112))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rsp.toBitVec - 8#64).toInt).At (s.regs.rsp.toBitVec - 120))
          ⋆ Eq ((Int.toBytes 8 (0 : UInt64).toBitVec.toInt).At (s.regs.rsp.toBitVec - 64))
          ⋆ Eq ((Int.toBytes 8 (0 : UInt64).toBitVec.toInt).At (s.regs.rsp.toBitVec - 56))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (in0.At s.regs.rbx.toBitVec) ⋆ Eq (in1.At (s.regs.rbx.toBitVec + 8))
          ⋆ Eq (ast.At s.regs.rax.toBitVec) ⋆ Eq (in0.At (s.regs.rax.toBitVec + 8))
          ⋆ Eq (in1.At (s.regs.rax.toBitVec + 16)) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  have hsl' : U64CalleeAccept Prysm.Slot.Code.unmarshalSSZLabel := hsl
  have hvi' : U64CalleeAccept Prysm.ValidatorIndex.Code.unmarshalLabel := hvi
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hguard hlen ⊢
  have hg : guard.toNat < (rsp.toBitVec - 112).toNat := Decode.accept_guard _ _ hguard
  -- head: entry → directive 15
  refine eventually_trans _ _ _ _ (Decode.head0 k hk _ ra guard fp s1 s2 s4 ast hfp h1 h2 h4 hast _
    (by dsimp only; ecancel) (Nat.lt_of_le_of_lt (Nat.le_add_right _ 112) hguard) hlen) ?_
  rintro ⟨d1, pc1⟩ ⟨hpc1, hrsp1, hrbp1, hr141, hrax1, hrbx1, Hm1⟩
  dsimp only at hpc1 hrsp1 hrbp1 hr141 hrax1 hrbx1 Hm1
  subst hpc1
  -- Slot: set-up 15–16
  refine eventually_trans _ _ _ _ (Decode.generated_call_Slot_arg k hk hf rax.toBitVec (rax.toBitVec + 8)
    (by simp only [Int64.toBitVec_ofNat]) d1 (by rw [hrax1])) ?_
  rintro ⟨d2, pc2⟩ ⟨hpc2, hrsp2, hrbp2, hr142, hrbx2, hrax2, hrcx2, hmem2⟩
  dsimp only at hpc2 hrsp2 hrbp2 hr142 hrbx2 hrax2 hrcx2 hmem2
  subst hpc2
  -- Slot: call block 17–19, label 46
  refine eventually_trans _ _ _ _ (Decode.generated_call_Slot_call k hk hf hsl'
    (rsp.toBitVec - 104) (rax.toBitVec + 8) rbx.toBitVec (rsp.toBitVec - 112) (rsp.toBitVec - 120) (rsp.toBitVec - 96)
    (by bv_omega) (by bv_omega) (by bv_omega)
    { toBitVec := rsp.toBitVec - 8#64 } r14 guard in0 rslot lf sp1 a8 hin0 hrs hlf hsp1 ha8 hg _ d2
    (hrsp2.trans hrsp1) (hrbp2.trans hrbp1) (hr142.trans hr141) hrax2 (by rw [hrbx2, hrbx1]) hrcx2
    (by rw [hmem2]; ecancel)) ?_
  rintro ⟨d3, pc3⟩ ⟨hpc3, hrax3, hrbx3, hrsp3, hrbp3, hr143, Hm3⟩
  dsimp only at hpc3 hrax3 hrbx3 hrsp3 hrbp3 hr143 Hm3
  subst hpc3
  -- ProposerIndex: set-up by reload 47–54 (with the padding nop)
  refine eventually_trans _ _ _ _ (Decode.generated_call_ProposerIndex_arg k hk hf
    (rsp.toBitVec - 104) rax.toBitVec rbx.toBitVec (rsp.toBitVec + 16) (rsp.toBitVec + 32) (rsp.toBitVec + 8)
    (rbx.toBitVec + 8) (rax.toBitVec + 16)
    (by simp only [Int64.toBitVec_ofNat]; bv_omega) (by simp only [Int64.toBitVec_ofNat]; bv_omega)
    (by simp only [Int64.toBitVec_ofNat]; bv_omega) (by simp only [Int64.toBitVec_ofNat])
    (by simp only [Int64.toBitVec_ofNat])
    (Int.toBytes 8 rdi.toBitVec.toInt) (Int.toBytes_length 8 _) _ d3 hrsp3 (by ecancel)) ?_
  rintro ⟨d4, pc4⟩ ⟨hpc4, hrsp4, hrbp4, hr144, hrbx4, hrax4, hrcx4, hmem4⟩
  dsimp only at hpc4 hrsp4 hrbp4 hr144 hrbx4 hrax4 hrcx4 hmem4
  subst hpc4
  -- ProposerIndex: call block 55–57, label 85
  refine eventually_trans _ _ _ _ (Decode.generated_call_ProposerIndex_call k hk hf hvi'
    (rsp.toBitVec - 104) (rax.toBitVec + 16) (rbx.toBitVec + 8) (rsp.toBitVec - 112) (rsp.toBitVec - 120)
    (rsp.toBitVec - 96) (by bv_omega) (by bv_omega) (by bv_omega)
    { toBitVec := rsp.toBitVec - 8#64 } r14 guard in1
    (Int.toBytes 8 (Host.addrOf (k + 17 + 1)).toBitVec.toInt) (Int.toBytes 8 (rsp.toBitVec - 8#64).toInt)
    (Int.toBytes 8 rbx.toBitVec.toInt) a16
    hin1 (Int.toBytes_length 8 _) (Int.toBytes_length 8 _) (Int.toBytes_length 8 _) ha16 hg _ d4
    (hrsp4.trans hrsp3) (hrbp4.trans hrbp3) (hr144.trans hr143) hrax4 hrbx4 hrcx4
    (by rw [hmem4]; ecancel)) ?_
  rintro ⟨d5, pc5⟩ ⟨hpc5, hrax5, hrbx5, hrsp5, hrbp5, hr145, Hm5⟩
  dsimp only at hpc5 hrax5 hrbx5 hrsp5 hrbp5 hr145 Hm5
  subst hpc5
  -- nil-error spills 86–87
  refine eventually_trans _ _ _ _ (Decode.spill2 k hk (rsp.toBitVec - 104) (rsp.toBitVec - 64) (rsp.toBitVec - 56)
    (by bv_omega) (by bv_omega) s28 s30 hs28 hs30 _ d5 hrsp5 (by ecancel)) ?_
  rintro ⟨d6, pc6⟩ ⟨hpc6, hrsp6, hrbp6, hr146, Hm6⟩
  dsimp only at hpc6 hrsp6 hrbp6 hr146 Hm6
  apply Eventually.done
  rw [hrax5, hrbx5] at Hm6
  rw [show k + 55 + 1 = k + 56 from rfl] at Hm6
  refine ⟨hpc6, ?_, ?_, hr146.trans hr145, ?_⟩
  · dsimp only; rw [hrsp6, hrsp5]; apply UInt64.toBitVec_inj.mp
    simp only [UInt64.toBitVec_sub, UInt64.toBitVec_ofNat]; rfl
  · dsimp only; rw [hrbp6, hrbp5]; apply UInt64.toBitVec_inj.mp
    simp only [UInt64.toBitVec_sub, UInt64.toBitVec_ofNat]
  · dsimp only; ecancel

/-- Same declared type as the existing hand theorem `Decode.head`. -/
theorem Decode.head_from_generated_call_segments_type : ∀ (h : Host),
    type_of% (@Decode.head_from_generated_call_segments h) = type_of% (@Decode.head h) := by
  intro h; with_reducible rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Accept path of `(*v1alpha1.BeaconBlockHeader).UnmarshalSSZ` from the GENERATED `decoder --call-segments` theorems (all five
fields); statement text of `Decode.accept`. -/
theorem Decode.accept_from_generated_call_segments (k : Nat) (hk : Code.unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh Code.unmarshalSSZ k)
    (kS : Nat) (hkS : Prysm.Slot.Code.unmarshalSSZ.IsInfixAt Host.prog kS) (hfS : LabelsFresh Prysm.Slot.Code.unmarshalSSZ kS)
    (kV : Nat) (hkV : Prysm.ValidatorIndex.Code.unmarshalSSZ.IsInfixAt Host.prog kV) (hfV : LabelsFresh Prysm.ValidatorIndex.Code.unmarshalSSZ kV)
    (in0 in1 r1 r2 r3 : List UInt8) (hin0 : in0.length = 8) (hin1 : in1.length = 8)
    (hr1 : r1.length = 32) (hr2 : r2.length = 32) (hr3 : r3.length = 32)
    (s : MachineData) (ra guard : UInt64)
    (fp s1 s2 s4 sp0 sp1 sp2 s28 s30 l38 rslot lo ast a8 a16 aP1 aL1 aC1 aP2 aL2 aC2 aP3 aL3 aC3 : List UInt8)
    (hfp : fp.length = 8) (h1 : s1.length = 8) (h2 : s2.length = 8) (h4 : s4.length = 8)
    (hsp0 : sp0.length = 8) (hsp1 : sp1.length = 8) (hsp2 : sp2.length = 8)
    (hs28 : s28.length = 8) (hs30 : s30.length = 8) (hl38 : l38.length = 8)
    (hrs : rslot.length = 8) (hast : ast.length = 8) (ha8 : a8.length = 8) (ha16 : a16.length = 8)
    (haP1 : aP1.length = 8) (haL1 : aL1.length = 8) (haC1 : aC1.length = 8)
    (haP2 : aP2.length = 8) (haL2 : aL2.length = 8) (haC2 : aC2.length = 8)
    (haP3 : aP3.length = 8) (haL3 : aL3.length = 8) (haC3 : aC3.length = 8)
    (R : DataMem → Prop) (S : Nat) (hS : S < 2 ^ 60) (hlo : lo.length = S + 8)
    (Heap : Nat → DataMem → Prop) (avail : Nat)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s1.At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16)) ⋆ Eq (s4.At (s.regs.rsp.toBitVec + 32))
      ⋆ Eq (sp0.At (s.regs.rsp.toBitVec - 104)) ⋆ Eq (sp1.At (s.regs.rsp.toBitVec - 96))
      ⋆ Eq (sp2.At (s.regs.rsp.toBitVec - 88))
      ⋆ Eq (s28.At (s.regs.rsp.toBitVec - 64)) ⋆ Eq (s30.At (s.regs.rsp.toBitVec - 56))
      ⋆ Eq (l38.At (s.regs.rsp.toBitVec - 48))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 112)) ⋆ Eq (lo.At (s.regs.rsp.toBitVec - 120 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Heap avail
      ⋆ Eq (in0.At s.regs.rbx.toBitVec) ⋆ Eq (in1.At (s.regs.rbx.toBitVec + 8))
      ⋆ Eq (r1.At (s.regs.rbx.toBitVec + 16)) ⋆ Eq (r2.At (s.regs.rbx.toBitVec + 48))
      ⋆ Eq (r3.At (s.regs.rbx.toBitVec + 80))
      ⋆ Eq (ast.At s.regs.rax.toBitVec) ⋆ Eq (a8.At (s.regs.rax.toBitVec + 8))
      ⋆ Eq (a16.At (s.regs.rax.toBitVec + 16))
      ⋆ Eq (aP1.At (s.regs.rax.toBitVec + 24)) ⋆ Eq (aL1.At (s.regs.rax.toBitVec + 32))
      ⋆ Eq (aC1.At (s.regs.rax.toBitVec + 40))
      ⋆ Eq (aP2.At (s.regs.rax.toBitVec + 48)) ⋆ Eq (aL2.At (s.regs.rax.toBitVec + 56))
      ⋆ Eq (aC2.At (s.regs.rax.toBitVec + 64))
      ⋆ Eq (aP3.At (s.regs.rax.toBitVec + 72)) ⋆ Eq (aL3.At (s.regs.rax.toBitVec + 80))
      ⋆ Eq (aC3.At (s.regs.rax.toBitVec + 88))
      ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R)
    (hguard : guard.toNat + 112 < s.regs.rsp.toNat) (hlen : s.regs.rcx = 112) (hav : 96 ≤ avail)
    (hms : MakesliceContract Heap ElfData.PrysmTarget.typeUint8_addr 1 (S + 8)) (hmm : MemmoveContract (S + 8)) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ (p1 p2 p3 : BitVec 64) (spl lo' : List UInt8), spl.length = 24 ∧ lo'.length = S + 8 ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec + 32))
          ⋆ Eq (spl.At (s.regs.rsp.toBitVec - 104))
          ⋆ Eq ((Int.toBytes 8 (0 : UInt64).toBitVec.toInt).At (s.regs.rsp.toBitVec - 64))
          ⋆ Eq ((Int.toBytes 8 (0 : UInt64).toBitVec.toInt).At (s.regs.rsp.toBitVec - 56))
          ⋆ Eq ((Int.toBytes 8 p3.toInt).At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 179)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 112))
          ⋆ Eq (lo'.At (s.regs.rsp.toBitVec - 120 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Heap (avail - 96)
          ⋆ Eq (in0.At s.regs.rbx.toBitVec) ⋆ Eq (in1.At (s.regs.rbx.toBitVec + 8))
          ⋆ Eq (r1.At (s.regs.rbx.toBitVec + 16)) ⋆ Eq (r2.At (s.regs.rbx.toBitVec + 48))
          ⋆ Eq (r3.At (s.regs.rbx.toBitVec + 80))
          ⋆ Eq (ast.At s.regs.rax.toBitVec) ⋆ Eq (in0.At (s.regs.rax.toBitVec + 8))
          ⋆ Eq (in1.At (s.regs.rax.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 24))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 32)) ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 40))
          ⋆ Eq ((Int.toBytes 8 p2.toInt).At (s.regs.rax.toBitVec + 48))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 56)) ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 64))
          ⋆ Eq ((Int.toBytes 8 p3.toInt).At (s.regs.rax.toBitVec + 72))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 80)) ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 88))
          ⋆ Eq (r1.At p1) ⋆ Eq (r2.At p2) ⋆ Eq (r3.At p3)
          ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  have hsl : Prysm.Slot.Decode.accept_function_spec := Prysm.Slot.Decode.accept_function_spec_holds kS hkS hfS
  have hvi : Prysm.ValidatorIndex.Decode.accept_function_spec := Prysm.ValidatorIndex.Decode.accept_function_spec_holds kV hkV hfV
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hguard hlen ⊢
  have hrsp_lt : rsp.toNat < 2 ^ 64 := rsp.toNat_lt_size
  have hlS : (lo.take S).length = S := by simp [hlo]
  have hl8 : (lo.drop S).length = 8 := by simp [hlo]
  have hlos : Eq (lo.At (rsp.toBitVec - 120 - BitVec.ofNat 64 S)) =
      Eq ((lo.take S).At (rsp.toBitVec - 120 - BitVec.ofNat 64 S)) ⋆ Eq ((lo.drop S).At (rsp.toBitVec - 120)) := by
    conv => lhs; rw [← List.take_append_drop S lo]
    exact Decode.low_stack_split _ S hS _ _ hlS hl8
  rw [hlos] at h_mem
  -- segment 1: entry → directive 88 (length check, Slot, ValidatorIndex, error spills)
  refine eventually_trans _ _ _ _ (Decode.head_from_generated_call_segments k hk hf hsl hvi in0 in1 hin0 hin1 _ ra guard fp s1 s2 s4 sp1 rslot
    (lo.drop S) ast a8 a16 s28 s30 hfp h1 h2 h4 hsp1 hrs hl8 hast ha8 ha16 hs28 hs30 _ (by dsimp only; ecancel)
    hguard hlen) ?_
  rintro ⟨d1, pc1⟩ ⟨hpc1, hrsp1, hrbp1, hr141, Hm1⟩
  dsimp only at hpc1 hrsp1 hrbp1 hr141 Hm1
  subst hpc1
  -- segment 2: ParentRoot (generated), 88 → 113
  refine eventually_trans _ _ _ _ (Decode.generated_call_ParentRoot_seg k hk hf (rsp.toBitVec - 104) rax.toBitVec rbx.toBitVec
    (rsp.toBitVec + 8) (rsp.toBitVec + 16) (rsp.toBitVec - 48) (rsp.toBitVec - 112)
    (rsp.toBitVec - 120 - BitVec.ofNat 64 S) (rax.toBitVec + 24) (rax.toBitVec + 32) (rax.toBitVec + 40)
    (rbx.toBitVec + 16) (S + 8)
    (by simp only [Int64.toBitVec_ofNat]; bv_omega) (by simp only [Int64.toBitVec_ofNat]; bv_omega)
    (by simp only [Int64.toBitVec_ofNat]; bv_omega) (by bv_omega) (Decode.stack_low_eq _ _)
    (by simp only [Int64.toBitVec_ofNat]) (by simp only [Int64.toBitVec_ofNat])
    (by simp only [Int64.toBitVec_ofNat]) (by simp only [Int64.toBitVec_ofNat])
    (rsp - 8) r14 r1 hr1
    (sp0 ++ (Int.toBytes 8 (rbx.toBitVec + 8).toInt ++ sp2)) (Int.toBytes 8 (Host.addrOf (k + 56)).toBitVec.toInt)
    (lo.take S ++ Int.toBytes 8 (rsp.toBitVec - 8#64).toInt) l38 aP1 aL1 aC1
    (by simp only [List.length_append, hsp0, hsp2, Int.toBytes_length]) (Int.toBytes_length 8 _)
    (by simp only [List.length_append, hlS, Int.toBytes_length]) hl38 haP1 haL1 haC1
    _ Heap avail (by omega) d1
    (by rw [hrsp1]; first | rfl | (apply UInt64.toBitVec_inj.mp; simp))
    (by rw [hrbp1]) hr141
    (by rw [Decode.split_three_words _ _ _ _ hsp0 (Int.toBytes_length 8 _) hsp2, Decode.low_stack_split _ S hS _ _ hlS (Int.toBytes_length 8 _)]
        ecancel) hms hmm) ?_
  rintro ⟨d2, pc2⟩ ⟨hpc2, hrsp2, hrbp2, hr142, p1, spl1, lo1, hspl1, hlo1, hrdx2, Hm2⟩
  dsimp only at hpc2 hrsp2 hrbp2 hr142 hrdx2 Hm2
  subst hpc2
  obtain ⟨⟨rax2, rbx2, rcx2, rdx2, rsi2, rdi2, rsp2, rbp2, r82, r92, r102, r112, r122, r132, r142, r152⟩,
    zmms2, flags2, mem2⟩ := d2
  simp only at hrsp2 hrbp2 hr142 hrdx2 Hm2
  subst hrsp2 hrbp2 hr142
  -- instance directives 113–115, L_1f7 (122), 123
  step_directive hk Code.unmarshalSSZ 113
  apply load_step_at _ _ (rsp.toBitVec - 48) _ _ (Int.toBytes 8 p1.toInt) _ _ (by beacon_block_header_addr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  unfold_step
  step_directive hk Code.unmarshalSSZ 114
  step_directive hk Code.unmarshalSSZ 115
  label_address hk hf Code.unmarshalSSZ 122
  step_directive hk Code.unmarshalSSZ 122
  step_directive hk Code.unmarshalSSZ 123
  apply store_step_at _ _ (rax.toBitVec + 24) _ _ _ (Int.toBytes 8 p1.toInt) _ _ (by rw [hrdx2]; try beacon_block_header_addr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  intro m3' H3
  simp only [Width.bytes, Width.bits] at H3
  unfold_step
  -- segment 3: StateRoot (generated), 124 → 149
  refine eventually_trans _ _ _ _ (Decode.generated_call_StateRoot_seg k hk hf (rsp.toBitVec - 104) rax.toBitVec rbx.toBitVec
    (rsp.toBitVec + 8) (rsp.toBitVec + 16) (rsp.toBitVec - 48) (rsp.toBitVec - 112)
    (rsp.toBitVec - 120 - BitVec.ofNat 64 S) (rax.toBitVec + 48) (rax.toBitVec + 56) (rax.toBitVec + 64)
    (rbx.toBitVec + 48) (S + 8)
    (by simp only [Int64.toBitVec_ofNat]; bv_omega) (by simp only [Int64.toBitVec_ofNat]; bv_omega)
    (by simp only [Int64.toBitVec_ofNat]; bv_omega) (by bv_omega) (Decode.stack_low_eq _ _)
    (by simp only [Int64.toBitVec_ofNat]) (by simp only [Int64.toBitVec_ofNat])
    (by simp only [Int64.toBitVec_ofNat]) (by simp only [Int64.toBitVec_ofNat])
    _ _ r2 hr2 spl1 (Int.toBytes 8 (Host.addrOf (k + 101 + 6 + 1)).toBitVec.toInt) lo1 (Int.toBytes 8 p1.toInt)
    aP2 aL2 aC2 hspl1 (Int.toBytes_length 8 _) hlo1 (Int.toBytes_length 8 _) haP2 haL2 haC2
    _ Heap (avail - 32) (by omega) _ rfl rfl rfl (by ecancel) hms hmm) ?_
  rintro ⟨d3, pc3⟩ ⟨hpc3, hrsp3, hrbp3, hr143, p2, spl2, lo2, hspl2, hlo2, hrdx3, Hm3⟩
  dsimp only at hpc3 hrsp3 hrbp3 hr143 hrdx3 Hm3
  subst hpc3
  obtain ⟨⟨rax3, rbx3, rcx3, rdx3, rsi3, rdi3, rsp3, rbp3, r83, r93, r103, r113, r123, r133, r143, r153⟩,
    zmms3, flags3, mem3⟩ := d3
  simp only at hrsp3 hrbp3 hr143 hrdx3 Hm3
  subst hrsp3 hrbp3 hr143
  -- instance directives 149–150, L_292 (157), 158
  step_directive hk Code.unmarshalSSZ 149
  apply load_step_at _ _ (rsp.toBitVec - 48) _ _ (Int.toBytes 8 p2.toInt) _ _ (by beacon_block_header_addr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  unfold_step
  step_directive hk Code.unmarshalSSZ 150
  label_address hk hf Code.unmarshalSSZ 157
  step_directive hk Code.unmarshalSSZ 157
  step_directive hk Code.unmarshalSSZ 158
  apply store_step_at _ _ (rax.toBitVec + 48) _ _ _ (Int.toBytes 8 p2.toInt) _ _ (by rw [hrdx3]; try beacon_block_header_addr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  intro m4' H4
  simp only [Width.bytes, Width.bits] at H4
  unfold_step
  -- segment 4: BodyRoot (generated), 159 → 184
  refine eventually_trans _ _ _ _ (Decode.generated_call_BodyRoot_seg k hk hf (rsp.toBitVec - 104) rax.toBitVec rbx.toBitVec
    (rsp.toBitVec + 8) (rsp.toBitVec + 16) (rsp.toBitVec - 48) (rsp.toBitVec - 112)
    (rsp.toBitVec - 120 - BitVec.ofNat 64 S) (rax.toBitVec + 72) (rax.toBitVec + 80) (rax.toBitVec + 88)
    (rbx.toBitVec + 80) (S + 8)
    (by simp only [Int64.toBitVec_ofNat]; bv_omega) (by simp only [Int64.toBitVec_ofNat]; bv_omega)
    (by simp only [Int64.toBitVec_ofNat]; bv_omega) (by bv_omega) (Decode.stack_low_eq _ _)
    (by simp only [Int64.toBitVec_ofNat]) (by simp only [Int64.toBitVec_ofNat])
    (by simp only [Int64.toBitVec_ofNat]) (by simp only [Int64.toBitVec_ofNat])
    _ _ r3 hr3 spl2 (Int.toBytes 8 (Host.addrOf (k + 137 + 6 + 1)).toBitVec.toInt) lo2 (Int.toBytes 8 p2.toInt)
    aP3 aL3 aC3 hspl2 (Int.toBytes_length 8 _) hlo2 (Int.toBytes_length 8 _) haP3 haL3 haC3
    _ Heap (avail - 32 - 32) (by omega) _ rfl rfl rfl (by ecancel) hms hmm) ?_
  rintro ⟨d4, pc4⟩ ⟨hpc4, hrsp4, hrbp4, hr144, p3, spl3, lo3, hspl3, hlo3, hrdx4, Hm4⟩
  dsimp only at hpc4 hrsp4 hrbp4 hr144 hrdx4 Hm4
  subst hpc4
  obtain ⟨⟨rax4, rbx4, rcx4, rdx4, rsi4, rdi4, rsp4, rbp4, r84, r94, r104, r114, r124, r134, r144, r154⟩,
    zmms4, flags4, mem4⟩ := d4
  simp only at hrsp4 hrbp4 hr144 hrdx4 Hm4
  subst hrsp4 hrbp4 hr144
  -- instance directives 184–185, L_331 (193), 194, epilogue 195–199
  step_directive hk Code.unmarshalSSZ 184
  apply load_step_at _ _ (rsp.toBitVec - 48) _ _ (Int.toBytes 8 p3.toInt) _ _ (by beacon_block_header_addr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  unfold_step
  step_directive hk Code.unmarshalSSZ 185
  label_address hk hf Code.unmarshalSSZ 193
  step_directive hk Code.unmarshalSSZ 193
  step_directive hk Code.unmarshalSSZ 194
  apply store_step_at _ _ (rax.toBitVec + 72) _ _ _ (Int.toBytes 8 p3.toInt) _ _ (by rw [hrdx4]; try beacon_block_header_addr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  intro m5' H5
  simp only [Width.bytes, Width.bits] at H5
  unfold_step
  step_directive hk Code.unmarshalSSZ 195
  apply load_step_at _ _ (rsp.toBitVec - 64) _ _ (Int.toBytes 8 (UInt64.toBitVec 0).toInt) _ _ (by beacon_block_header_addr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  unfold_step
  step_directive hk Code.unmarshalSSZ 196
  apply load_step_at _ _ (rsp.toBitVec - 56) _ _ (Int.toBytes 8 (UInt64.toBitVec 0).toInt) _ _ (by beacon_block_header_addr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  unfold_step
  step_directive hk Code.unmarshalSSZ 197
  step_directive hk Code.unmarshalSSZ 198
  apply load_step_at _ _ (rsp.toBitVec - 8) _ _ (Int.toBytes 8 rbp.toBitVec.toInt) _ _ (by beacon_block_header_addr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  unfold_step
  step_directive hk Code.unmarshalSSZ 199
  apply load_step_at _ _ rsp.toBitVec _ _ (Int.toBytes 8 ra.toBitVec.toInt) _ _ (by beacon_block_header_addr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  unfold_step
  apply Eventually.done
  rw [show UInt64.toBitVec 0 = 0#64 from rfl] at H5
  rw [show k + 172 + 6 + 1 = k + 179 from rfl] at H5
  rw [show avail - 32 - 32 - 32 = avail - 96 by omega] at H5
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, p1, p2, p3, spl3, lo3, hspl3, hlo3, ?_⟩
  rotate_right
  · ecancel
  all_goals first
    | exact trivial
    | with_reducible rfl
    | (apply UInt64.toBitVec_inj.mp
       simp only [UInt64.toBitVec_add, UInt64.toBitVec_ofNat, BitVec.ofNat_eq_ofNat, Width.bits]
       done)
    | (apply UInt64.toBitVec_inj.mp; beacon_block_header_addr)

/-- Same declared type as the existing hand theorem `Decode.accept`. -/
theorem Decode.accept_from_generated_call_segments_type : ∀ (h : Host),
    type_of% (@Decode.accept_from_generated_call_segments h) = type_of% (@Decode.accept h) := by
  intro h; with_reducible rfl

end Prysm.BeaconBlockHeader
