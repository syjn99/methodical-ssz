import E2eScal.AcceptTies
import Codec.FieldFrame
import E2eScal.ViSpec
import Prysm.Epoch.DecodeAccept
import E2eAd.Prims
import Codec.DecoderHeadEpilogue
import E2eScal.Gen4H6PbDec

/-!
# Worked example: `(*v1alpha1.PowBlock).UnmarshalSSZ`, accept theorem in generated style

Text produced from one description of the type (frame facts, field list, boundary states, chain theorem names)
by the recipe of the lemma hand-over; every theorem has a `_kind` line (`decHeadKindN`, `decFieldKindN`,
`decEpiKindN`, `decAcceptKindN`). The `p2dec --gen4` chain theorems (`E2eScal.Gen.*`) are used as emitted.
Frame `0x20`: the epilogue (`xor`, `xor`, `add $0x20`, `pop`, `retq`) is the lemma `decepi_seg`.
-/

open Machine Runtime TestTarget E2eAd E2eAd.Code E2eScal.H6Code E2eScal.H5Code E2eScal.BhCode E2eScal Codec
variable [Host]

namespace E2eScal.Gen5

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Head: directives 0–12 (prologue, spills); entry → boundary state 0. -/
theorem pb_g5_head : ∀ (k : Nat) (hk : PbUnmarshal.IsInfixAt Host.prog k) (hf : LabelsFresh PbUnmarshal k)
    (bh ph td : List UInt8) (hbh : bh.length = 32) (hph : ph.length = 32) (htd : td.length = 32)
    (s : MachineData) (ra guard : UInt64)
    (fp s1 s2 spl l18 rslot lo aP0 aL0 aC0 aP1 aL1 aC1 aP2 aL2 aC2 : List UInt8)
    (hfp : fp.length = 8) (hs1 : s1.length = 8) (hs2 : s2.length = 8) (hspl : spl.length = 24) (hl18 : l18.length = 8) (hrslot : rslot.length = 8) (haP0 : aP0.length = 8) (haL0 : aL0.length = 8) (haC0 : aC0.length = 8) (haP1 : aP1.length = 8) (haL1 : aL1.length = 8) (haC1 : aC1.length = 8) (haP2 : aP2.length = 8) (haL2 : aL2.length = 8) (haC2 : aC2.length = 8)
    (R : DataMem → Prop) (S : Nat) (hlo : lo.length = S)
    (Heap : Nat → DataMem → Prop) (avail : Nat)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8))
      ⋆ Eq (s1.At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq (spl.At (s.regs.rsp.toBitVec - 40))
      ⋆ Eq (l18.At (s.regs.rsp.toBitVec - 16))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 48))
      ⋆ Eq (lo.At (s.regs.rsp.toBitVec - 48 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Heap avail
      ⋆ Eq (bh.At s.regs.rbx.toBitVec)
      ⋆ Eq (ph.At (s.regs.rbx.toBitVec + 32))
      ⋆ Eq (td.At (s.regs.rbx.toBitVec + 64))
      ⋆ Eq (aP0.At s.regs.rax.toBitVec)
      ⋆ Eq (aL0.At (s.regs.rax.toBitVec + 8))
      ⋆ Eq (aC0.At (s.regs.rax.toBitVec + 16))
      ⋆ Eq (aP1.At (s.regs.rax.toBitVec + 24))
      ⋆ Eq (aL1.At (s.regs.rax.toBitVec + 32))
      ⋆ Eq (aC1.At (s.regs.rax.toBitVec + 40))
      ⋆ Eq (aP2.At (s.regs.rax.toBitVec + 48))
      ⋆ Eq (aL2.At (s.regs.rax.toBitVec + 56))
      ⋆ Eq (aC2.At (s.regs.rax.toBitVec + 64))
      ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec)
      ⋆ R)
    (hguard : guard.toNat < s.regs.rsp.toNat) (hlen : s.regs.rcx = 96) (hav : 96 ≤ avail)
    (hms : MakesliceC Heap ElfData.CheckpointAndEpoch.e2eU8Type_addr 1 S) (hmm : MemmoveC S),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 13)
        ∧ st.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - 40 }
        ∧ st.data.regs.rbp = { toBitVec := s.regs.rsp.toBitVec - 8 }
        ∧ st.data.regs.r14 = s.regs.r14 ∧
        
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq (spl.At (s.regs.rsp.toBitVec - 40))
          ⋆ Eq (l18.At (s.regs.rsp.toBitVec - 16))
          ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq (lo.At (s.regs.rsp.toBitVec - 48 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Heap avail
          ⋆ Eq (bh.At s.regs.rbx.toBitVec)
          ⋆ Eq (ph.At (s.regs.rbx.toBitVec + 32))
          ⋆ Eq (td.At (s.regs.rbx.toBitVec + 64))
          ⋆ Eq (aP0.At s.regs.rax.toBitVec)
          ⋆ Eq (aL0.At (s.regs.rax.toBitVec + 8))
          ⋆ Eq (aC0.At (s.regs.rax.toBitVec + 16))
          ⋆ Eq (aP1.At (s.regs.rax.toBitVec + 24))
          ⋆ Eq (aL1.At (s.regs.rax.toBitVec + 32))
          ⋆ Eq (aC1.At (s.regs.rax.toBitVec + 40))
          ⋆ Eq (aP2.At (s.regs.rax.toBitVec + 48))
          ⋆ Eq (aL2.At (s.regs.rax.toBitVec + 56))
          ⋆ Eq (aC2.At (s.regs.rax.toBitVec + 64))
          ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec)
          ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  intro k hk hf bh ph td hbh hph htd s ra guard fp s1 s2 spl l18 rslot lo aP0 aL0 aC0 aP1 aL1 aC1 aP2 aL2 aC2 hfp hs1 hs2 hspl hl18 hrslot haP0 haL0 haC0 haP1 haL1 haC1 haP2 haL2 haC2 R S hlo Heap avail h_mem hguard hlen hav hms hmm
  refine eventually_trans _ _ _ _ (decpro_seg _ _ _ _ 32 56 96 _ k (k + 11) (win hk 0 11) (by rfl) (by rfl)
    s ra guard (s.regs.rsp.toBitVec - 40) (s.regs.rsp.toBitVec + 16)
    (by simp only [Int64.toBitVec_ofNat] <;> bv_omega) (by simp only [Int64.toBitVec_ofNat] <;> bv_omega)
    fp s2 hfp hs2 _ (by ecancel) hguard (by rw [hlen]; rfl)) ?_
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
  apply kstep_st Reg64.rax Reg64.rsp 48 _ (k + 11) (k + 12) (win hk 11 1) (by rfl) (by rfl)
    (s.regs.rsp.toBitVec - 40) (s.regs.rsp.toBitVec + 8) (by simp only [Int64.toBitVec_ofNat] <;> bv_omega)
    s1 hs1 _ _ _ (by rfl) (by ecancel)
  intro m11 H11; kn; simp only [Reg64s.get64] at H11
  apply kstep_st Reg64.rbx Reg64.rsp 56 _ (k + 12) (k + 13) (win hk 12 1) (by rfl) (by rfl)
    (s.regs.rsp.toBitVec - 40) (s.regs.rsp.toBitVec + 16) (by simp only [Int64.toBitVec_ofNat] <;> bv_omega)
    (Int.toBytes 8 s.regs.rbx.toBitVec.toInt) (Int.toBytes_length 8 _) _ _ _ (by rfl) (by ecancel)
  intro m12 H12; kn; simp only [Reg64s.get64] at H12
  apply Eventually.done
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  dsimp only
  ecancel
theorem pb_g5_head_kind : ∀ (h : Host), type_of% (@pb_g5_head h)
    = @E2eScal.decHeadKindN h PbUnmarshal (E2eScal.layRt false 104 3) [.bytes 32, .bytes 32, .bytes 32]
    ⟨13, 0, [],
      [.at (.dn 8) (.reg .rbp), .at (.up 8) (.reg .rax), .at (.up 16) (.reg .rbx), .at (.dn 40) (.orig 3), .at (.dn 16) (.orig 4), .at (.dn 48) (.orig 5), .lo (.orig 6)],
      []⟩ := by
  intro h; rfl

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
/-- Field 1 `BlockHash` (bytes): boundary state 0 (directive 13) → boundary state 1 (directive 47). -/
theorem pb_g5_f1 : ∀ (k : Nat) (hk : PbUnmarshal.IsInfixAt Host.prog k) (hf : LabelsFresh PbUnmarshal k)
    (bh ph td : List UInt8) (hbh : bh.length = 32) (hph : ph.length = 32) (htd : td.length = 32)
    (s : MachineData) (ra guard : UInt64)
    (fp s1 s2 spl l18 rslot lo aP0 aL0 aC0 aP1 aL1 aC1 aP2 aL2 aC2 : List UInt8)
    (hfp : fp.length = 8) (hs1 : s1.length = 8) (hs2 : s2.length = 8) (hspl : spl.length = 24) (hl18 : l18.length = 8) (hrslot : rslot.length = 8) (haP0 : aP0.length = 8) (haL0 : aL0.length = 8) (haC0 : aC0.length = 8) (haP1 : aP1.length = 8) (haL1 : aL1.length = 8) (haC1 : aC1.length = 8) (haP2 : aP2.length = 8) (haL2 : aL2.length = 8) (haC2 : aC2.length = 8)
    (R : DataMem → Prop) (S : Nat) (hlo : lo.length = S)
    (Heap : Nat → DataMem → Prop) (avail : Nat)
    (hguard : guard.toNat < s.regs.rsp.toNat) (hav : 96 ≤ avail)
    (hms : MakesliceC Heap ElfData.CheckpointAndEpoch.e2eU8Type_addr 1 S) (hmm : MemmoveC S) (st0 : MachineState),
    (st0.pc = Host.addrOf (k + 13)
        ∧ st0.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - 40 }
        ∧ st0.data.regs.rbp = { toBitVec := s.regs.rsp.toBitVec - 8 }
        ∧ st0.data.regs.r14 = s.regs.r14 ∧
        
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq (spl.At (s.regs.rsp.toBitVec - 40))
          ⋆ Eq (l18.At (s.regs.rsp.toBitVec - 16))
          ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq (lo.At (s.regs.rsp.toBitVec - 48 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Heap avail
          ⋆ Eq (bh.At s.regs.rbx.toBitVec)
          ⋆ Eq (ph.At (s.regs.rbx.toBitVec + 32))
          ⋆ Eq (td.At (s.regs.rbx.toBitVec + 64))
          ⋆ Eq (aP0.At s.regs.rax.toBitVec)
          ⋆ Eq (aL0.At (s.regs.rax.toBitVec + 8))
          ⋆ Eq (aC0.At (s.regs.rax.toBitVec + 16))
          ⋆ Eq (aP1.At (s.regs.rax.toBitVec + 24))
          ⋆ Eq (aL1.At (s.regs.rax.toBitVec + 32))
          ⋆ Eq (aC1.At (s.regs.rax.toBitVec + 40))
          ⋆ Eq (aP2.At (s.regs.rax.toBitVec + 48))
          ⋆ Eq (aL2.At (s.regs.rax.toBitVec + 56))
          ⋆ Eq (aC2.At (s.regs.rax.toBitVec + 64))
          ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec)
          ⋆ R) st0.data.dmem) →
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 47)
        ∧ st.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - 40 }
        ∧ st.data.regs.rbp = { toBitVec := s.regs.rsp.toBitVec - 8 }
        ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ (p1 : BitVec 64) (x0 x1 : List UInt8), x0.length = 24 ∧ x1.length = S ∧ 
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq (x0.At (s.regs.rsp.toBitVec - 40))
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rsp.toBitVec - 16))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 32)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq (x1.At (s.regs.rsp.toBitVec - 48 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Heap (avail - 32)
          ⋆ Eq (bh.At s.regs.rbx.toBitVec)
          ⋆ Eq (ph.At (s.regs.rbx.toBitVec + 32))
          ⋆ Eq (td.At (s.regs.rbx.toBitVec + 64))
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At s.regs.rax.toBitVec)
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 16))
          ⋆ Eq (aP1.At (s.regs.rax.toBitVec + 24))
          ⋆ Eq (aL1.At (s.regs.rax.toBitVec + 32))
          ⋆ Eq (aC1.At (s.regs.rax.toBitVec + 40))
          ⋆ Eq (aP2.At (s.regs.rax.toBitVec + 48))
          ⋆ Eq (aL2.At (s.regs.rax.toBitVec + 56))
          ⋆ Eq (aC2.At (s.regs.rax.toBitVec + 64))
          ⋆ Eq (bh.At p1)
          ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec)
          ⋆ R) st.data.dmem)
      st0 := by
  intro k hk hf bh ph td hbh hph htd s ra guard fp s1 s2 spl l18 rslot lo aP0 aL0 aC0 aP1 aL1 aC1 aP2 aL2 aC2 hfp hs1 hs2 hspl hl18 hrslot haP0 haL0 haC0 haP1 haL1 haC1 haP2 haL2 haC2 R S hlo Heap avail hguard hav hms hmm
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at hguard ⊢
  rintro ⟨d, pc⟩ ⟨hpc, hrsp, hrbp, hr14, Hm⟩
  dsimp only at hpc hrsp hrbp hr14  Hm
  subst hpc
  refine eventually_trans _ _ _ _ (Gen.pb_g4dec_BlockHash_seg k hk hf (rsp.toBitVec - 40) rax.toBitVec rbx.toBitVec
    (rsp.toBitVec + 8) (rsp.toBitVec + 16) (rsp.toBitVec - 16) (rsp.toBitVec - 48)
    (rsp.toBitVec - 48 - BitVec.ofNat 64 S) rax.toBitVec (rax.toBitVec + 8) (rax.toBitVec + 16) S
    (by simp only [Int64.toBitVec_ofNat] <;> bv_omega) (by simp only [Int64.toBitVec_ofNat] <;> bv_omega) (by simp only [Int64.toBitVec_ofNat] <;> bv_omega) (by bv_omega) (frame_lo0 _ 40 48 S (by decide))
    (by simp only [Int64.toBitVec_ofNat]; exact BitVec.add_zero _) (by simp only [Int64.toBitVec_ofNat] <;> bv_omega) (by simp only [Int64.toBitVec_ofNat] <;> bv_omega)
    { toBitVec := rsp.toBitVec - 8#64 } r14 bh hbh
    spl rslot lo l18 aP0 aL0 aC0
    hspl hrslot hlo hl18 haP0 haL0 haC0
    _ Heap avail (by omega) d hrsp hrbp hr14
      (by ecancel) hms hmm) ?_
  rintro ⟨d', pc'⟩ ⟨hpc', hrsp', hrbp', hr14', p1, spl', lo', hspl', hlo', hrY, Hm'⟩
  dsimp only at hpc' hrsp' hrbp' hr14' hrY Hm'
  subst hpc'
  obtain ⟨⟨rax2, rbx2, rcx2, rdx2, rsi2, rdi2, rsp2, rbp2, r82, r92, r102, r112, r122, r132, r142, r152⟩, zmms2, flags2, mem2⟩ := d'
  simp only at hrsp' hrbp' hr14' hrY Hm'
  subst rsp2 rbp2 r142
  apply Gen.pb_g4dec_s37 k hk hf (rsp.toBitVec - 40) (rsp.toBitVec - 16) p1 (by simp only [Int64.toBitVec_ofNat] <;> bv_omega) _ _ _ (by rfl) (by ecancel)
  kn
  apply Gen.pb_g4dec_s38 k hk hf
  apply Gen.pb_g4dec_s45 k hk hf
  apply Gen.pb_g4dec_s46 k hk hf rax.toBitVec rax.toBitVec (by simp only [Int64.toBitVec_ofNat]; exact BitVec.add_zero _) (Int.toBytes 8 p1.toInt) (Int.toBytes_length 8 _) _ _ _
    (by exact hrY) (by ecancel)
  intro m' H
  kn
  simp only [Reg64s.get64] at H
  apply Eventually.done
  refine ⟨rfl, rfl, rfl, rfl, p1, spl', lo', hspl', hlo', ?_⟩
  dsimp only
  rw [show k + 31 + 1 = k + 32 from rfl] at H
  ecancel
theorem pb_g5_f1_kind : ∀ (h : Host), type_of% (@pb_g5_f1 h)
    = @E2eScal.decFieldKindN h PbUnmarshal (E2eScal.layRt false 104 3) [.bytes 32, .bytes 32, .bytes 32]
    ⟨13, 0, [],
      [.at (.dn 8) (.reg .rbp), .at (.up 8) (.reg .rax), .at (.up 16) (.reg .rbx), .at (.dn 40) (.orig 3), .at (.dn 16) (.orig 4), .at (.dn 48) (.orig 5), .lo (.orig 6)],
      []⟩
    ⟨47, 1, [],
      [.at (.dn 8) (.reg .rbp), .at (.up 8) (.reg .rax), .at (.up 16) (.reg .rbx), .at (.dn 40) (.ex 0), .at (.dn 16) (.ptr 0), .at (.dn 48) (.ret 32), .lo (.ex 1)],
      [.n 24, .lo]⟩ := by
  intro h; rfl

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
/-- Field 2 `ParentHash` (bytes): boundary state 1 (directive 47) → boundary state 2 (directive 83). -/
theorem pb_g5_f2 : ∀ (k : Nat) (hk : PbUnmarshal.IsInfixAt Host.prog k) (hf : LabelsFresh PbUnmarshal k)
    (bh ph td : List UInt8) (hbh : bh.length = 32) (hph : ph.length = 32) (htd : td.length = 32)
    (s : MachineData) (ra guard : UInt64)
    (fp s1 s2 spl l18 rslot lo aP0 aL0 aC0 aP1 aL1 aC1 aP2 aL2 aC2 : List UInt8)
    (hfp : fp.length = 8) (hs1 : s1.length = 8) (hs2 : s2.length = 8) (hspl : spl.length = 24) (hl18 : l18.length = 8) (hrslot : rslot.length = 8) (haP0 : aP0.length = 8) (haL0 : aL0.length = 8) (haC0 : aC0.length = 8) (haP1 : aP1.length = 8) (haL1 : aL1.length = 8) (haC1 : aC1.length = 8) (haP2 : aP2.length = 8) (haL2 : aL2.length = 8) (haC2 : aC2.length = 8)
    (R : DataMem → Prop) (S : Nat) (hlo : lo.length = S)
    (Heap : Nat → DataMem → Prop) (avail : Nat)
    (hguard : guard.toNat < s.regs.rsp.toNat) (hav : 96 ≤ avail)
    (hms : MakesliceC Heap ElfData.CheckpointAndEpoch.e2eU8Type_addr 1 S) (hmm : MemmoveC S) (st0 : MachineState),
    (st0.pc = Host.addrOf (k + 47)
        ∧ st0.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - 40 }
        ∧ st0.data.regs.rbp = { toBitVec := s.regs.rsp.toBitVec - 8 }
        ∧ st0.data.regs.r14 = s.regs.r14 ∧
        ∃ (p1 : BitVec 64) (x0 x1 : List UInt8), x0.length = 24 ∧ x1.length = S ∧ 
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq (x0.At (s.regs.rsp.toBitVec - 40))
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rsp.toBitVec - 16))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 32)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq (x1.At (s.regs.rsp.toBitVec - 48 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Heap (avail - 32)
          ⋆ Eq (bh.At s.regs.rbx.toBitVec)
          ⋆ Eq (ph.At (s.regs.rbx.toBitVec + 32))
          ⋆ Eq (td.At (s.regs.rbx.toBitVec + 64))
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At s.regs.rax.toBitVec)
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 16))
          ⋆ Eq (aP1.At (s.regs.rax.toBitVec + 24))
          ⋆ Eq (aL1.At (s.regs.rax.toBitVec + 32))
          ⋆ Eq (aC1.At (s.regs.rax.toBitVec + 40))
          ⋆ Eq (aP2.At (s.regs.rax.toBitVec + 48))
          ⋆ Eq (aL2.At (s.regs.rax.toBitVec + 56))
          ⋆ Eq (aC2.At (s.regs.rax.toBitVec + 64))
          ⋆ Eq (bh.At p1)
          ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec)
          ⋆ R) st0.data.dmem) →
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 83)
        ∧ st.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - 40 }
        ∧ st.data.regs.rbp = { toBitVec := s.regs.rsp.toBitVec - 8 }
        ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ (p1 p2 : BitVec 64) (x0 x1 : List UInt8), x0.length = 24 ∧ x1.length = S ∧ 
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq (x0.At (s.regs.rsp.toBitVec - 40))
          ⋆ Eq ((Int.toBytes 8 p2.toInt).At (s.regs.rsp.toBitVec - 16))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 68)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq (x1.At (s.regs.rsp.toBitVec - 48 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Heap (avail - 64)
          ⋆ Eq (bh.At s.regs.rbx.toBitVec)
          ⋆ Eq (ph.At (s.regs.rbx.toBitVec + 32))
          ⋆ Eq (td.At (s.regs.rbx.toBitVec + 64))
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At s.regs.rax.toBitVec)
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 p2.toInt).At (s.regs.rax.toBitVec + 24))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 32))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 40))
          ⋆ Eq (aP2.At (s.regs.rax.toBitVec + 48))
          ⋆ Eq (aL2.At (s.regs.rax.toBitVec + 56))
          ⋆ Eq (aC2.At (s.regs.rax.toBitVec + 64))
          ⋆ Eq (bh.At p1)
          ⋆ Eq (ph.At p2)
          ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec)
          ⋆ R) st.data.dmem)
      st0 := by
  intro k hk hf bh ph td hbh hph htd s ra guard fp s1 s2 spl l18 rslot lo aP0 aL0 aC0 aP1 aL1 aC1 aP2 aL2 aC2 hfp hs1 hs2 hspl hl18 hrslot haP0 haL0 haC0 haP1 haL1 haC1 haP2 haL2 haC2 R S hlo Heap avail hguard hav hms hmm
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at hguard ⊢
  rintro ⟨d, pc⟩ ⟨hpc, hrsp, hrbp, hr14, p1, x0, x1, hx0, hx1, Hm⟩
  dsimp only at hpc hrsp hrbp hr14  Hm
  subst hpc
  refine eventually_trans _ _ _ _ (Gen.pb_g4dec_ParentHash_seg k hk hf (rsp.toBitVec - 40) rax.toBitVec rbx.toBitVec
    (rsp.toBitVec + 8) (rsp.toBitVec + 16) (rsp.toBitVec - 16) (rsp.toBitVec - 48)
    (rsp.toBitVec - 48 - BitVec.ofNat 64 S) (rax.toBitVec + 24) (rax.toBitVec + 32) (rax.toBitVec + 40) (rbx.toBitVec + 32) S
    (by simp only [Int64.toBitVec_ofNat] <;> bv_omega) (by simp only [Int64.toBitVec_ofNat] <;> bv_omega) (by simp only [Int64.toBitVec_ofNat] <;> bv_omega) (by bv_omega) (frame_lo0 _ 40 48 S (by decide))
    (by simp only [Int64.toBitVec_ofNat] <;> bv_omega) (by simp only [Int64.toBitVec_ofNat] <;> bv_omega) (by simp only [Int64.toBitVec_ofNat] <;> bv_omega) (by simp only [Int64.toBitVec_ofNat] <;> bv_omega)
    { toBitVec := rsp.toBitVec - 8#64 } r14 ph hph
    x0 (Int.toBytes 8 (Host.addrOf (k + 32)).toBitVec.toInt) x1 (Int.toBytes 8 p1.toInt) aP1 aL1 aC1
    hx0 (Int.toBytes_length 8 _) hx1 (Int.toBytes_length 8 _) haP1 haL1 haC1
    _ Heap (avail - 32) (by omega) d hrsp hrbp hr14
      (by ecancel) hms hmm) ?_
  rintro ⟨d', pc'⟩ ⟨hpc', hrsp', hrbp', hr14', p2, spl', lo', hspl', hlo', hrY, Hm'⟩
  dsimp only at hpc' hrsp' hrbp' hr14' hrY Hm'
  subst hpc'
  obtain ⟨⟨rax2, rbx2, rcx2, rdx2, rsi2, rdi2, rsp2, rbp2, r82, r92, r102, r112, r122, r132, r142, r152⟩, zmms2, flags2, mem2⟩ := d'
  simp only at hrsp' hrbp' hr14' hrY Hm'
  subst rsp2 rbp2 r142
  apply Gen.pb_g4dec_s73 k hk hf (rsp.toBitVec - 40) (rsp.toBitVec - 16) p2 (by simp only [Int64.toBitVec_ofNat] <;> bv_omega) _ _ _ (by rfl) (by ecancel)
  kn
  apply Gen.pb_g4dec_s74 k hk hf
  apply Gen.pb_g4dec_s81 k hk hf
  apply Gen.pb_g4dec_s82 k hk hf rax.toBitVec (rax.toBitVec + 24) (by simp only [Int64.toBitVec_ofNat] <;> bv_omega) (Int.toBytes 8 p2.toInt) (Int.toBytes_length 8 _) _ _ _
    (by exact hrY) (by ecancel)
  intro m' H
  kn
  simp only [Reg64s.get64] at H
  apply Eventually.done
  refine ⟨rfl, rfl, rfl, rfl, p1, p2, spl', lo', hspl', hlo', ?_⟩
  dsimp only
  rw [show k + 67 + 1 = k + 68 from rfl] at H
  rw [show avail - 32 - 32 = avail - 64 by omega] at H
  ecancel
theorem pb_g5_f2_kind : ∀ (h : Host), type_of% (@pb_g5_f2 h)
    = @E2eScal.decFieldKindN h PbUnmarshal (E2eScal.layRt false 104 3) [.bytes 32, .bytes 32, .bytes 32]
    ⟨47, 1, [],
      [.at (.dn 8) (.reg .rbp), .at (.up 8) (.reg .rax), .at (.up 16) (.reg .rbx), .at (.dn 40) (.ex 0), .at (.dn 16) (.ptr 0), .at (.dn 48) (.ret 32), .lo (.ex 1)],
      [.n 24, .lo]⟩
    ⟨83, 2, [],
      [.at (.dn 8) (.reg .rbp), .at (.up 8) (.reg .rax), .at (.up 16) (.reg .rbx), .at (.dn 40) (.ex 0), .at (.dn 16) (.ptr 1), .at (.dn 48) (.ret 68), .lo (.ex 1)],
      [.n 24, .lo]⟩ := by
  intro h; rfl

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
/-- Field 3 `TotalDifficulty` (bytes): boundary state 2 (directive 83) → boundary state 3 (directive 119). -/
theorem pb_g5_f3 : ∀ (k : Nat) (hk : PbUnmarshal.IsInfixAt Host.prog k) (hf : LabelsFresh PbUnmarshal k)
    (bh ph td : List UInt8) (hbh : bh.length = 32) (hph : ph.length = 32) (htd : td.length = 32)
    (s : MachineData) (ra guard : UInt64)
    (fp s1 s2 spl l18 rslot lo aP0 aL0 aC0 aP1 aL1 aC1 aP2 aL2 aC2 : List UInt8)
    (hfp : fp.length = 8) (hs1 : s1.length = 8) (hs2 : s2.length = 8) (hspl : spl.length = 24) (hl18 : l18.length = 8) (hrslot : rslot.length = 8) (haP0 : aP0.length = 8) (haL0 : aL0.length = 8) (haC0 : aC0.length = 8) (haP1 : aP1.length = 8) (haL1 : aL1.length = 8) (haC1 : aC1.length = 8) (haP2 : aP2.length = 8) (haL2 : aL2.length = 8) (haC2 : aC2.length = 8)
    (R : DataMem → Prop) (S : Nat) (hlo : lo.length = S)
    (Heap : Nat → DataMem → Prop) (avail : Nat)
    (hguard : guard.toNat < s.regs.rsp.toNat) (hav : 96 ≤ avail)
    (hms : MakesliceC Heap ElfData.CheckpointAndEpoch.e2eU8Type_addr 1 S) (hmm : MemmoveC S) (st0 : MachineState),
    (st0.pc = Host.addrOf (k + 83)
        ∧ st0.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - 40 }
        ∧ st0.data.regs.rbp = { toBitVec := s.regs.rsp.toBitVec - 8 }
        ∧ st0.data.regs.r14 = s.regs.r14 ∧
        ∃ (p1 p2 : BitVec 64) (x0 x1 : List UInt8), x0.length = 24 ∧ x1.length = S ∧ 
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq (x0.At (s.regs.rsp.toBitVec - 40))
          ⋆ Eq ((Int.toBytes 8 p2.toInt).At (s.regs.rsp.toBitVec - 16))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 68)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq (x1.At (s.regs.rsp.toBitVec - 48 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Heap (avail - 64)
          ⋆ Eq (bh.At s.regs.rbx.toBitVec)
          ⋆ Eq (ph.At (s.regs.rbx.toBitVec + 32))
          ⋆ Eq (td.At (s.regs.rbx.toBitVec + 64))
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At s.regs.rax.toBitVec)
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 p2.toInt).At (s.regs.rax.toBitVec + 24))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 32))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 40))
          ⋆ Eq (aP2.At (s.regs.rax.toBitVec + 48))
          ⋆ Eq (aL2.At (s.regs.rax.toBitVec + 56))
          ⋆ Eq (aC2.At (s.regs.rax.toBitVec + 64))
          ⋆ Eq (bh.At p1)
          ⋆ Eq (ph.At p2)
          ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec)
          ⋆ R) st0.data.dmem) →
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 119)
        ∧ st.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - 40 }
        ∧ st.data.regs.rbp = { toBitVec := s.regs.rsp.toBitVec - 8 }
        ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ (p1 p2 p3 : BitVec 64) (x0 x1 : List UInt8), x0.length = 24 ∧ x1.length = S ∧ 
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq (x0.At (s.regs.rsp.toBitVec - 40))
          ⋆ Eq ((Int.toBytes 8 p3.toInt).At (s.regs.rsp.toBitVec - 16))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 104)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq (x1.At (s.regs.rsp.toBitVec - 48 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Heap (avail - 96)
          ⋆ Eq (bh.At s.regs.rbx.toBitVec)
          ⋆ Eq (ph.At (s.regs.rbx.toBitVec + 32))
          ⋆ Eq (td.At (s.regs.rbx.toBitVec + 64))
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At s.regs.rax.toBitVec)
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 p2.toInt).At (s.regs.rax.toBitVec + 24))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 32))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 40))
          ⋆ Eq ((Int.toBytes 8 p3.toInt).At (s.regs.rax.toBitVec + 48))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 56))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 64))
          ⋆ Eq (bh.At p1)
          ⋆ Eq (ph.At p2)
          ⋆ Eq (td.At p3)
          ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec)
          ⋆ R) st.data.dmem)
      st0 := by
  intro k hk hf bh ph td hbh hph htd s ra guard fp s1 s2 spl l18 rslot lo aP0 aL0 aC0 aP1 aL1 aC1 aP2 aL2 aC2 hfp hs1 hs2 hspl hl18 hrslot haP0 haL0 haC0 haP1 haL1 haC1 haP2 haL2 haC2 R S hlo Heap avail hguard hav hms hmm
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at hguard ⊢
  rintro ⟨d, pc⟩ ⟨hpc, hrsp, hrbp, hr14, p1, p2, x0, x1, hx0, hx1, Hm⟩
  dsimp only at hpc hrsp hrbp hr14  Hm
  subst hpc
  refine eventually_trans _ _ _ _ (Gen.pb_g4dec_TotalDifficulty_seg k hk hf (rsp.toBitVec - 40) rax.toBitVec rbx.toBitVec
    (rsp.toBitVec + 8) (rsp.toBitVec + 16) (rsp.toBitVec - 16) (rsp.toBitVec - 48)
    (rsp.toBitVec - 48 - BitVec.ofNat 64 S) (rax.toBitVec + 48) (rax.toBitVec + 56) (rax.toBitVec + 64) (rbx.toBitVec + 64) S
    (by simp only [Int64.toBitVec_ofNat] <;> bv_omega) (by simp only [Int64.toBitVec_ofNat] <;> bv_omega) (by simp only [Int64.toBitVec_ofNat] <;> bv_omega) (by bv_omega) (frame_lo0 _ 40 48 S (by decide))
    (by simp only [Int64.toBitVec_ofNat] <;> bv_omega) (by simp only [Int64.toBitVec_ofNat] <;> bv_omega) (by simp only [Int64.toBitVec_ofNat] <;> bv_omega) (by simp only [Int64.toBitVec_ofNat] <;> bv_omega)
    { toBitVec := rsp.toBitVec - 8#64 } r14 td htd
    x0 (Int.toBytes 8 (Host.addrOf (k + 68)).toBitVec.toInt) x1 (Int.toBytes 8 p2.toInt) aP2 aL2 aC2
    hx0 (Int.toBytes_length 8 _) hx1 (Int.toBytes_length 8 _) haP2 haL2 haC2
    _ Heap (avail - 64) (by omega) d hrsp hrbp hr14
      (by ecancel) hms hmm) ?_
  rintro ⟨d', pc'⟩ ⟨hpc', hrsp', hrbp', hr14', p3, spl', lo', hspl', hlo', hrY, Hm'⟩
  dsimp only at hpc' hrsp' hrbp' hr14' hrY Hm'
  subst hpc'
  obtain ⟨⟨rax2, rbx2, rcx2, rdx2, rsi2, rdi2, rsp2, rbp2, r82, r92, r102, r112, r122, r132, r142, r152⟩, zmms2, flags2, mem2⟩ := d'
  simp only at hrsp' hrbp' hr14' hrY Hm'
  subst rsp2 rbp2 r142
  apply Gen.pb_g4dec_s109 k hk hf (rsp.toBitVec - 40) (rsp.toBitVec - 16) p3 (by simp only [Int64.toBitVec_ofNat] <;> bv_omega) _ _ _ (by rfl) (by ecancel)
  kn
  apply Gen.pb_g4dec_s110 k hk hf
  apply Gen.pb_g4dec_s117 k hk hf
  apply Gen.pb_g4dec_s118 k hk hf rax.toBitVec (rax.toBitVec + 48) (by simp only [Int64.toBitVec_ofNat] <;> bv_omega) (Int.toBytes 8 p3.toInt) (Int.toBytes_length 8 _) _ _ _
    (by exact hrY) (by ecancel)
  intro m' H
  kn
  simp only [Reg64s.get64] at H
  apply Eventually.done
  refine ⟨rfl, rfl, rfl, rfl, p1, p2, p3, spl', lo', hspl', hlo', ?_⟩
  dsimp only
  rw [show k + 103 + 1 = k + 104 from rfl] at H
  rw [show avail - 64 - 32 = avail - 96 by omega] at H
  ecancel
theorem pb_g5_f3_kind : ∀ (h : Host), type_of% (@pb_g5_f3 h)
    = @E2eScal.decFieldKindN h PbUnmarshal (E2eScal.layRt false 104 3) [.bytes 32, .bytes 32, .bytes 32]
    ⟨83, 2, [],
      [.at (.dn 8) (.reg .rbp), .at (.up 8) (.reg .rax), .at (.up 16) (.reg .rbx), .at (.dn 40) (.ex 0), .at (.dn 16) (.ptr 1), .at (.dn 48) (.ret 68), .lo (.ex 1)],
      [.n 24, .lo]⟩
    ⟨119, 3, [],
      [.at (.dn 8) (.reg .rbp), .at (.up 8) (.reg .rax), .at (.up 16) (.reg .rbx), .at (.dn 40) (.ex 0), .at (.dn 16) (.ptr 2), .at (.dn 48) (.ret 104), .lo (.ex 1)],
      [.n 24, .lo]⟩ := by
  intro h; rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Epilogue: boundary state 3 (directive 119) → return. -/
theorem pb_g5_epi : ∀ (k : Nat) (hk : PbUnmarshal.IsInfixAt Host.prog k) (hf : LabelsFresh PbUnmarshal k)
    (bh ph td : List UInt8) (hbh : bh.length = 32) (hph : ph.length = 32) (htd : td.length = 32)
    (s : MachineData) (ra guard : UInt64)
    (fp s1 s2 spl l18 rslot lo aP0 aL0 aC0 aP1 aL1 aC1 aP2 aL2 aC2 : List UInt8)
    (hfp : fp.length = 8) (hs1 : s1.length = 8) (hs2 : s2.length = 8) (hspl : spl.length = 24) (hl18 : l18.length = 8) (hrslot : rslot.length = 8) (haP0 : aP0.length = 8) (haL0 : aL0.length = 8) (haC0 : aC0.length = 8) (haP1 : aP1.length = 8) (haL1 : aL1.length = 8) (haC1 : aC1.length = 8) (haP2 : aP2.length = 8) (haL2 : aL2.length = 8) (haC2 : aC2.length = 8)
    (R : DataMem → Prop) (S : Nat) (hlo : lo.length = S)
    (Heap : Nat → DataMem → Prop) (avail : Nat)
    (st0 : MachineState),
    (st0.pc = Host.addrOf (k + 119)
        ∧ st0.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - 40 }
        ∧ st0.data.regs.rbp = { toBitVec := s.regs.rsp.toBitVec - 8 }
        ∧ st0.data.regs.r14 = s.regs.r14 ∧
        ∃ (p1 p2 p3 : BitVec 64) (x0 x1 : List UInt8), x0.length = 24 ∧ x1.length = S ∧ 
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq (x0.At (s.regs.rsp.toBitVec - 40))
          ⋆ Eq ((Int.toBytes 8 p3.toInt).At (s.regs.rsp.toBitVec - 16))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 104)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq (x1.At (s.regs.rsp.toBitVec - 48 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Heap (avail - 96)
          ⋆ Eq (bh.At s.regs.rbx.toBitVec)
          ⋆ Eq (ph.At (s.regs.rbx.toBitVec + 32))
          ⋆ Eq (td.At (s.regs.rbx.toBitVec + 64))
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At s.regs.rax.toBitVec)
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 p2.toInt).At (s.regs.rax.toBitVec + 24))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 32))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 40))
          ⋆ Eq ((Int.toBytes 8 p3.toInt).At (s.regs.rax.toBitVec + 48))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 56))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 64))
          ⋆ Eq (bh.At p1)
          ⋆ Eq (ph.At p2)
          ⋆ Eq (td.At p3)
          ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec)
          ⋆ R) st0.data.dmem) →
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ (p1 p2 p3 : BitVec 64) (x0 x1 : List UInt8), x0.length = 24 ∧ x1.length = S ∧ 
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq (x0.At (s.regs.rsp.toBitVec - 40))
          ⋆ Eq ((Int.toBytes 8 p3.toInt).At (s.regs.rsp.toBitVec - 16))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 104)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq (x1.At (s.regs.rsp.toBitVec - 48 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Heap (avail - 96)
          ⋆ Eq (bh.At s.regs.rbx.toBitVec)
          ⋆ Eq (ph.At (s.regs.rbx.toBitVec + 32))
          ⋆ Eq (td.At (s.regs.rbx.toBitVec + 64))
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At s.regs.rax.toBitVec)
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 p2.toInt).At (s.regs.rax.toBitVec + 24))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 32))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 40))
          ⋆ Eq ((Int.toBytes 8 p3.toInt).At (s.regs.rax.toBitVec + 48))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 56))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 64))
          ⋆ Eq (bh.At p1)
          ⋆ Eq (ph.At p2)
          ⋆ Eq (td.At p3)
          ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec)
          ⋆ R) st.data.dmem)
      st0 := by
  intro k hk hf bh ph td hbh hph htd s ra guard fp s1 s2 spl l18 rslot lo aP0 aL0 aC0 aP1 aL1 aC1 aP2 aL2 aC2 hfp hs1 hs2 hspl hl18 hrslot haP0 haL0 haC0 haP1 haL1 haC1 haP2 haL2 haC2 R S hlo Heap avail
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at ⊢
  rintro ⟨d, pc⟩ ⟨hpc, hrsp, hrbp, hr14, p1, p2, p3, x0, x1, hx0, hx1, Hm⟩
  dsimp only at hpc hrsp hrbp hr14  Hm
  subst hpc
  have hE := Codec.infix_sub (q := Codec.decEpi) 119 hk
    (by simp only [PbUnmarshal, Codec.decEpi, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero])
  refine eventually_trans _ _ _ _ (Codec.decepi_seg (k + 119) hE (rsp.toBitVec - 40) (rsp.toBitVec - 8) rsp.toBitVec
    (by bv_omega) (by bv_omega) rbp ra r14 _ d hrsp hr14 (by ecancel)) ?_
  rintro ⟨d', pc'⟩ ⟨hpc', hrax', hrbx', hrsp', hrbp', hr14', hmem'⟩
  dsimp only at hpc' hrax' hrbx' hrsp' hrbp' hr14' hmem'
  apply Eventually.done
  refine ⟨hpc', hrax', hrbx', ?_, hrbp', hr14', p1, p2, p3, x0, x1, hx0, hx1, ?_⟩
  · rw [hrsp']; apply UInt64.toBitVec_inj.mp
    first
      | (simp only [UInt64.toBitVec_add, UInt64.toBitVec_ofNat]; done)
      | (simp only [UInt64.toBitVec_add, UInt64.toBitVec_ofNat]; bv_omega)
  · dsimp only; ecancel
theorem pb_g5_epi_kind : ∀ (h : Host), type_of% (@pb_g5_epi h)
    = @E2eScal.decEpiKindN h PbUnmarshal (E2eScal.layRt false 104 3) [.bytes 32, .bytes 32, .bytes 32]
    ⟨119, 3, [],
      [.at (.dn 8) (.reg .rbp), .at (.up 8) (.reg .rax), .at (.up 16) (.reg .rbx), .at (.dn 40) (.ex 0), .at (.dn 16) (.ptr 2), .at (.dn 48) (.ret 104), .lo (.ex 1)],
      [.n 24, .lo]⟩ := by
  intro h; rfl

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
/-- **Accept path of `(*v1alpha1.PowBlock).UnmarshalSSZ` (Go 1.26.10), generated-style proof**: head, one theorem per
field, epilogue, chained by `eventually_trans`. Statement = the kind instance (`_kind`). -/
theorem pb_e2e_accept_g5 : ∀ (k : Nat) (hk : PbUnmarshal.IsInfixAt Host.prog k) (hf : LabelsFresh PbUnmarshal k)
    (bh ph td : List UInt8) (hbh : bh.length = 32) (hph : ph.length = 32) (htd : td.length = 32)
    (s : MachineData) (ra guard : UInt64)
    (fp s1 s2 spl l18 rslot lo aP0 aL0 aC0 aP1 aL1 aC1 aP2 aL2 aC2 : List UInt8)
    (hfp : fp.length = 8) (hs1 : s1.length = 8) (hs2 : s2.length = 8) (hspl : spl.length = 24) (hl18 : l18.length = 8) (hrslot : rslot.length = 8) (haP0 : aP0.length = 8) (haL0 : aL0.length = 8) (haC0 : aC0.length = 8) (haP1 : aP1.length = 8) (haL1 : aL1.length = 8) (haC1 : aC1.length = 8) (haP2 : aP2.length = 8) (haL2 : aL2.length = 8) (haC2 : aC2.length = 8)
    (R : DataMem → Prop) (S : Nat) (hlo : lo.length = S)
    (Heap : Nat → DataMem → Prop) (avail : Nat)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8))
      ⋆ Eq (s1.At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq (spl.At (s.regs.rsp.toBitVec - 40))
      ⋆ Eq (l18.At (s.regs.rsp.toBitVec - 16))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 48))
      ⋆ Eq (lo.At (s.regs.rsp.toBitVec - 48 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Heap avail
      ⋆ Eq (bh.At s.regs.rbx.toBitVec)
      ⋆ Eq (ph.At (s.regs.rbx.toBitVec + 32))
      ⋆ Eq (td.At (s.regs.rbx.toBitVec + 64))
      ⋆ Eq (aP0.At s.regs.rax.toBitVec)
      ⋆ Eq (aL0.At (s.regs.rax.toBitVec + 8))
      ⋆ Eq (aC0.At (s.regs.rax.toBitVec + 16))
      ⋆ Eq (aP1.At (s.regs.rax.toBitVec + 24))
      ⋆ Eq (aL1.At (s.regs.rax.toBitVec + 32))
      ⋆ Eq (aC1.At (s.regs.rax.toBitVec + 40))
      ⋆ Eq (aP2.At (s.regs.rax.toBitVec + 48))
      ⋆ Eq (aL2.At (s.regs.rax.toBitVec + 56))
      ⋆ Eq (aC2.At (s.regs.rax.toBitVec + 64))
      ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec)
      ⋆ R)
    (hguard : guard.toNat < s.regs.rsp.toNat) (hlen : s.regs.rcx = 96) (hav : 96 ≤ avail)
    (hms : MakesliceC Heap ElfData.CheckpointAndEpoch.e2eU8Type_addr 1 S) (hmm : MemmoveC S),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ (p1 p2 p3 : BitVec 64) (x0 x1 : List UInt8), x0.length = 24 ∧ x1.length = S ∧ 
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq (x0.At (s.regs.rsp.toBitVec - 40))
          ⋆ Eq ((Int.toBytes 8 p3.toInt).At (s.regs.rsp.toBitVec - 16))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 104)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq (x1.At (s.regs.rsp.toBitVec - 48 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Heap (avail - 96)
          ⋆ Eq (bh.At s.regs.rbx.toBitVec)
          ⋆ Eq (ph.At (s.regs.rbx.toBitVec + 32))
          ⋆ Eq (td.At (s.regs.rbx.toBitVec + 64))
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At s.regs.rax.toBitVec)
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 p2.toInt).At (s.regs.rax.toBitVec + 24))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 32))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 40))
          ⋆ Eq ((Int.toBytes 8 p3.toInt).At (s.regs.rax.toBitVec + 48))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 56))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 64))
          ⋆ Eq (bh.At p1)
          ⋆ Eq (ph.At p2)
          ⋆ Eq (td.At p3)
          ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec)
          ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  intro k hk hf bh ph td hbh hph htd s ra guard fp s1 s2 spl l18 rslot lo aP0 aL0 aC0 aP1 aL1 aC1 aP2 aL2 aC2 hfp hs1 hs2 hspl hl18 hrslot haP0 haL0 haC0 haP1 haL1 haC1 haP2 haL2 haC2 R S hlo Heap avail h_mem hguard hlen hav hms hmm
  refine eventually_trans _ _ _ _ (pb_g5_head k hk hf bh ph td hbh hph htd s ra guard fp s1 s2 spl l18 rslot lo aP0 aL0 aC0 aP1 aL1 aC1 aP2 aL2 aC2 hfp hs1 hs2 hspl hl18 hrslot haP0 haL0 haC0 haP1 haL1 haC1 haP2 haL2 haC2 R S hlo Heap avail h_mem hguard hlen hav hms hmm) ?_
  intro st0 h0
  refine eventually_trans _ _ _ _ (pb_g5_f1 k hk hf bh ph td hbh hph htd s ra guard fp s1 s2 spl l18 rslot lo aP0 aL0 aC0 aP1 aL1 aC1 aP2 aL2 aC2 hfp hs1 hs2 hspl hl18 hrslot haP0 haL0 haC0 haP1 haL1 haC1 haP2 haL2 haC2 R S hlo Heap avail hguard hav hms hmm st0 h0) ?_
  intro st1 h1
  refine eventually_trans _ _ _ _ (pb_g5_f2 k hk hf bh ph td hbh hph htd s ra guard fp s1 s2 spl l18 rslot lo aP0 aL0 aC0 aP1 aL1 aC1 aP2 aL2 aC2 hfp hs1 hs2 hspl hl18 hrslot haP0 haL0 haC0 haP1 haL1 haC1 haP2 haL2 haC2 R S hlo Heap avail hguard hav hms hmm st1 h1) ?_
  intro st2 h2
  refine eventually_trans _ _ _ _ (pb_g5_f3 k hk hf bh ph td hbh hph htd s ra guard fp s1 s2 spl l18 rslot lo aP0 aL0 aC0 aP1 aL1 aC1 aP2 aL2 aC2 hfp hs1 hs2 hspl hl18 hrslot haP0 haL0 haC0 haP1 haL1 haC1 haP2 haL2 haC2 R S hlo Heap avail hguard hav hms hmm st2 h2) ?_
  intro st3 h3
  exact pb_g5_epi k hk hf bh ph td hbh hph htd s ra guard fp s1 s2 spl l18 rslot lo aP0 aL0 aC0 aP1 aL1 aC1 aP2 aL2 aC2 hfp hs1 hs2 hspl hl18 hrslot haP0 haL0 haC0 haP1 haL1 haC1 haP2 haL2 haC2 R S hlo Heap avail st3 h3
theorem pb_e2e_accept_g5_kind : ∀ (h : Host), type_of% (@pb_e2e_accept_g5 h)
    = @E2eScal.decAcceptKindN h PbUnmarshal (E2eScal.layRt false 104 3) [.bytes 32, .bytes 32, .bytes 32] := by
  intro h; rfl

/-- The generated-style theorem proves the committed hand statement `E2eScal.H6.pb_accept_stmt` (unchanged). -/
theorem pb_e2e_accept_g5_stmt : E2eScal.H6.pb_accept_stmt := pb_e2e_accept_g5

end E2eScal.Gen5
