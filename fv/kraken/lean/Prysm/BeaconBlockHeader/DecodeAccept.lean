import Prysm.BeaconBlockHeader.DecodeHead
import Prysm.BeaconBlockHeader.GeneratedDecodeRootFieldSegments
import Prysm.AttestationData.DecodeAccept

/-!
# Real Prysm `(*v1alpha1.BeaconBlockHeader).UnmarshalSSZ`, accept path, Go 1.26.10 machine code (hold-out)

Hand-written (composition; not generator output).

    func (b *BeaconBlockHeader) UnmarshalSSZ(buf []byte) error {
        if uint64(len(buf)) != 112 { return ssz.ErrSize }
        b.Slot.UnmarshalSSZ(buf[0:8]); b.ProposerIndex.UnmarshalSSZ(buf[8:16])   // errors wrapped
        b.ParentRoot = append(make([]byte, 0, 32), buf[16:48]...)
        b.StateRoot  = append(make([]byte, 0, 32), buf[48:80]...)
        b.BodyRoot   = append(make([]byte, 0, 32), buf[80:112]...)
        return err }

Receiver: the protoc struct, gc amd64 layout from `prysm/ir/ir-mainnet.json` (the generator read the root
offsets 24 / 48 / 72 from it): `state` 0, `Slot` 8, `ProposerIndex` 16, `ParentRoot` 24, `StateRoot` 48,
`BodyRoot` 72 (ptr, len, cap each). `unknownFields` and `sizeCache` are not touched on this path (in `R`).

**Proof.** `Decode.head` (entry → directive 88: length check, Slot and ValidatorIndex callees through
`Prysm.Slot.Decode.accept_function_spec` / `Prysm.ValidatorIndex.Decode.accept_function_spec`, spills of their nil errors), then the three GENERATED segment theorems
`Decode.generated_root_ParentRoot_seg` (88–112), `Decode.generated_root_StateRoot_seg` (124–148), `Decode.generated_root_BodyRoot_seg`
(159–183), with the instance directives between them by hand: 113–115 + `L_1f7` 122–123, 149–150 +
`L_292` 157–158, 184–185 + `L_331` 193–194 (reload of the slice pointer from rsp − 48 and its store), and
the epilogue 195–199 (rax, rbx reloaded from the spills, `add`, `pop`, `retq`).

Stack (rsp = s.regs.rsp at entry): return slot; saved rbp at rsp − 8; argument spills at rsp + 8, + 16,
+ 32; frame rsp − 104 … rsp − 9: argument area rsp − 104 … rsp − 81 (`sp0 sp1 sp2`), the error spills
rsp − 64 (`s28`), rsp − 56 (`s30`), the slice pointer save rsp − 48 (`l38`), the rest untouched on this
path (in `R`); callee return slot rsp − 112; `lo` = the `S + 8` bytes below it (the callee's saved rbp is
its top word). Runtime calls get `S + 8` stack bytes below their return slot.
-/

open Machine Runtime Prysm.AttestationData.Code Prysm.BeaconBlockHeader.Code Codec
variable [Host]

namespace Prysm.BeaconBlockHeader

theorem Decode.lo8 (x : BitVec 64) (S : Nat) (hS : S < 2 ^ 60) (a f : List UInt8) (ha : a.length = S) (hf : f.length = 8) :
    Eq ((a ++ f).At (x - 120 - BitVec.ofNat 64 S)) = Eq (a.At (x - 120 - BitVec.ofNat 64 S)) ⋆ Eq (f.At (x - 120)) := by
  refine at_app _ _ ?_ (by simp only [ha, hf]; omega)
  rw [ha]; bv_omega

theorem Decode.stack_low_eq (x : BitVec 64) (S : Nat) : x - 104 - 8 - BitVec.ofNat 64 (S + 8) = x - 120 - BitVec.ofNat 64 S := by
  have : BitVec.ofNat 64 (S + 8) = BitVec.ofNat 64 S + 8 := by
    apply BitVec.eq_of_toNat_eq; simp
  rw [this]; bv_omega

theorem Decode.j3 (x : BitVec 64) (a b c : List UInt8) (ha : a.length = 8) (hb : b.length = 8) (hc : c.length = 8) :
    Eq ((a ++ (b ++ c)).At (x - 104)) = Eq (a.At (x - 104)) ⋆ Eq (b.At (x - 96)) ⋆ Eq (c.At (x - 88)) := by
  rw [at_app _ _ (b := x - 96) (by rw [ha]; bv_omega) (by simp [ha, hb, hc]),
    at_app _ _ (b := x - 88) (by rw [hb]; bv_omega) (by simp [hb, hc])]
  simp only [Std.ExtHashMap.sep_assoc]

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- **Accept path of the real `(*v1alpha1.BeaconBlockHeader).UnmarshalSSZ` (Go 1.26.10)**: on a 112-byte
input it returns nil and the receiver holds Slot = buf[0:8], ProposerIndex = buf[8:16] and fresh 32-byte
ParentRoot / StateRoot / BodyRoot = buf[16:48] / buf[48:80] / buf[80:112] (len = cap = 32 each); the input,
`state`, the caller's frame `R` and the stack guard are unchanged; 96 heap bytes are used. -/
theorem Decode.accept (k : Nat) (hk : Code.unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh Code.unmarshalSSZ k)
    (kS : Nat) (hkS : slotUnmarshalSSZ.IsInfixAt Host.prog kS) (hfS : LabelsFresh slotUnmarshalSSZ kS)
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
    (hms : MakesliceC Heap ElfData.CheckpointAndEpoch.e2eU8Type_addr 1 (S + 8)) (hmm : MemmoveC (S + 8)) :
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
    exact Decode.lo8 _ S hS _ _ hlS hl8
  rw [hlos] at h_mem
  -- segment 1: entry → directive 88 (length check, Slot, ValidatorIndex, error spills)
  refine eventually_trans _ _ _ _ (Decode.head k hk hf hsl hvi in0 in1 hin0 hin1 _ ra guard fp s1 s2 s4 sp1 rslot
    (lo.drop S) ast a8 a16 s28 s30 hfp h1 h2 h4 hsp1 hrs hl8 hast ha8 ha16 hs28 hs30 _ (by dsimp only; ecancel)
    hguard hlen) ?_
  rintro ⟨d1, pc1⟩ ⟨hpc1, hrsp1, hrbp1, hr141, Hm1⟩
  dsimp only at hpc1 hrsp1 hrbp1 hr141 Hm1
  subst hpc1
  -- segment 2: ParentRoot (generated), 88 → 113
  refine eventually_trans _ _ _ _ (Decode.generated_root_ParentRoot_seg k hk hf (rsp.toBitVec - 104) rax.toBitVec rbx.toBitVec
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
    (by rw [Decode.j3 _ _ _ _ hsp0 (Int.toBytes_length 8 _) hsp2, Decode.lo8 _ S hS _ _ hlS (Int.toBytes_length 8 _)]
        ecancel) hms hmm) ?_
  rintro ⟨d2, pc2⟩ ⟨hpc2, hrsp2, hrbp2, hr142, p1, spl1, lo1, hspl1, hlo1, hrdx2, Hm2⟩
  dsimp only at hpc2 hrsp2 hrbp2 hr142 hrdx2 Hm2
  subst hpc2
  obtain ⟨⟨rax2, rbx2, rcx2, rdx2, rsi2, rdi2, rsp2, rbp2, r82, r92, r102, r112, r122, r132, r142, r152⟩,
    zmms2, flags2, mem2⟩ := d2
  simp only at hrsp2 hrbp2 hr142 hrdx2 Hm2
  subst hrsp2 hrbp2 hr142
  -- instance directives 113–115, L_1f7 (122), 123
  kat hk Code.unmarshalSSZ 113
  apply load_step_at _ _ (rsp.toBitVec - 48) _ _ (Int.toBytes 8 p1.toInt) _ _ (by bhaddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk Code.unmarshalSSZ 114
  kat hk Code.unmarshalSSZ 115
  klabel hk hf Code.unmarshalSSZ 122
  kat hk Code.unmarshalSSZ 122
  kat hk Code.unmarshalSSZ 123
  apply store_step_at _ _ (rax.toBitVec + 24) _ _ _ (Int.toBytes 8 p1.toInt) _ _ (by rw [hrdx2]; try bhaddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  intro m3' H3
  simp only [Width.bytes, Width.bits] at H3
  kunfold
  -- segment 3: StateRoot (generated), 124 → 149
  refine eventually_trans _ _ _ _ (Decode.generated_root_StateRoot_seg k hk hf (rsp.toBitVec - 104) rax.toBitVec rbx.toBitVec
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
  kat hk Code.unmarshalSSZ 149
  apply load_step_at _ _ (rsp.toBitVec - 48) _ _ (Int.toBytes 8 p2.toInt) _ _ (by bhaddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk Code.unmarshalSSZ 150
  klabel hk hf Code.unmarshalSSZ 157
  kat hk Code.unmarshalSSZ 157
  kat hk Code.unmarshalSSZ 158
  apply store_step_at _ _ (rax.toBitVec + 48) _ _ _ (Int.toBytes 8 p2.toInt) _ _ (by rw [hrdx3]; try bhaddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  intro m4' H4
  simp only [Width.bytes, Width.bits] at H4
  kunfold
  -- segment 4: BodyRoot (generated), 159 → 184
  refine eventually_trans _ _ _ _ (Decode.generated_root_BodyRoot_seg k hk hf (rsp.toBitVec - 104) rax.toBitVec rbx.toBitVec
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
  kat hk Code.unmarshalSSZ 184
  apply load_step_at _ _ (rsp.toBitVec - 48) _ _ (Int.toBytes 8 p3.toInt) _ _ (by bhaddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk Code.unmarshalSSZ 185
  klabel hk hf Code.unmarshalSSZ 193
  kat hk Code.unmarshalSSZ 193
  kat hk Code.unmarshalSSZ 194
  apply store_step_at _ _ (rax.toBitVec + 72) _ _ _ (Int.toBytes 8 p3.toInt) _ _ (by rw [hrdx4]; try bhaddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  intro m5' H5
  simp only [Width.bytes, Width.bits] at H5
  kunfold
  kat hk Code.unmarshalSSZ 195
  apply load_step_at _ _ (rsp.toBitVec - 64) _ _ (Int.toBytes 8 (UInt64.toBitVec 0).toInt) _ _ (by bhaddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk Code.unmarshalSSZ 196
  apply load_step_at _ _ (rsp.toBitVec - 56) _ _ (Int.toBytes 8 (UInt64.toBitVec 0).toInt) _ _ (by bhaddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk Code.unmarshalSSZ 197
  kat hk Code.unmarshalSSZ 198
  apply load_step_at _ _ (rsp.toBitVec - 8) _ _ (Int.toBytes 8 rbp.toBitVec.toInt) _ _ (by bhaddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk Code.unmarshalSSZ 199
  apply load_step_at _ _ rsp.toBitVec _ _ (Int.toBytes 8 ra.toBitVec.toInt) _ _ (by bhaddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
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
    | (apply UInt64.toBitVec_inj.mp; bhaddr)

end Prysm.BeaconBlockHeader
