import Prysm.AttestationData.DecodeAcceptTarget

/-!
# Real Prysm `(*v1alpha1.AttestationData).UnmarshalSSZ`, accept path, Go 1.26.10 machine code

    func (a *AttestationData) UnmarshalSSZ(buf []byte) error {        // phase0.ssz.go:273
        if uint64(len(buf)) != 128 { return ssz.ErrSize }
        a.Slot.UnmarshalSSZ(buf[0:8]); a.CommitteeIndex.UnmarshalSSZ(buf[8:16])   // errors wrapped
        a.BeaconBlockRoot = append(make([]byte, 0, 32), buf[16:48]...)
        a.Source = new(Checkpoint); a.Source.UnmarshalSSZ(buf[48:88])
        a.Target = new(Checkpoint); a.Target.UnmarshalSSZ(buf[88:128])
        return err }

Receiver: the protoc struct (`attestation.pb.go`, gc amd64 layout `Prysm.AttestationData.goFields`): `state` 0,
`Slot` 8, `CommitteeIndex` 16, `BeaconBlockRoot` 24 (ptr, len, cap), `Source` 48, `Target` 56,
`unknownFields` 64 (24), `sizeCache` 88 (4) + 4 bytes padding. Size 96. `unknownFields` and
`sizeCache` are not touched on this path (in `R`).

**Case covered.** One theorem covers every receiver: the code has no branch on `Source` /
`Target`: it always allocates both Checkpoint objects through `runtime.newobject`
and overwrites the old pointers (`aS`, `aT` are arbitrary bytes, nil or not). The conclusion
states the new pointers `ps`, `pt` and the full 72-byte content of each new object
(`state` = 0, `Epoch`, `Root` header, `unknownFields` / `sizeCache` = 0).

**Callees.** Slot, CommitteeIndex and both Checkpoint calls are discharged through the proved
function specifications `Prysm.Slot.Decode.accept_function_spec_holds`, `Prysm.CommitteeIndex.Decode.accept_function_spec_holds`, `Prysm.Checkpoint.Decode.accept_function_spec_holds` (the code places
`kS`, `kI`, `kC`, `kE` in the host); the statement has no hypothesis about their behaviour.
The runtime contract forms (`Runtime/Contracts.lean`, `Runtime/NewobjectContract.lean`) stay visible: the
Checkpoint callee's `MakesliceContract … S` / `MemmoveContract S` (what `Prysm.Checkpoint.Decode.accept_function_spec_holds` needs) and this
function's own `MakesliceContract … (S + 96)`, `MemmoveContract (S + 96)`, `NewobjectContract typeCheckpoint 72 (S + 96)`
(its runtime calls get the `S + 96` stack bytes below their return slot, which contain the
Checkpoint callee's frame and its own `S` scratch bytes).

**Proof.** Four segment lemmas (one proof of the whole function made a Lean process exceed the 6 GiB memory cap): `Decode.head` (entry → `L_167`), `Decode.block_root`
(→ `L_208`), `Decode.source` (→ `L_2d9`), `Decode.target` (→ return); every directive index was
re-derived from the Go 1.26.10 `.S`. An earlier hand proof on the Go 1.26.3 test target (Checkpoint inlined,
different frame) was not reused: only its proof style.

Stack (rsp = s.regs.rsp at entry): return slot; saved rbp at rsp − 8; argument spills at
rsp + 8, + 16, + 32 (rsp + 24 is not written); frame rsp − 120 … rsp − 8: argument area
rsp − 120 … rsp − 97 (`sp0 sp1 sp2`), the Root pointer save at rsp − 16 (`l68`), the rest
untouched on this path (in `R`); callee return slot rsp − 128; `lo` = the `S + 96` bytes
below it.
-/

open Machine Runtime Prysm.AttestationData.Code
variable [Host]

namespace Prysm.AttestationData

theorem Decode.accept_low_stack_split (x : BitVec 64) (S : Nat) (hS : S < 2 ^ 60) (a f : List UInt8) (ha : a.length = S + 88)
    (hf : f.length = 8) :
    Eq ((a ++ f).At (x - 224 - BitVec.ofNat 64 S)) = Eq (a.At (x - 224 - BitVec.ofNat 64 S)) ⋆ Eq (f.At (x - 136)) := by
  refine at_app _ _ ?_ (by simp only [ha, hf]; omega)
  rw [ha]
  have : BitVec.ofNat 64 (S + 88) = BitVec.ofNat 64 S + 88 := by apply BitVec.eq_of_toNat_eq; simp
  rw [this]; bv_omega

theorem Decode.accept_split_three_words (x : BitVec 64) (a b c : List UInt8) (ha : a.length = 8) (hb : b.length = 8) (hc : c.length = 8) :
    Eq ((a ++ (b ++ c)).At (x - 120)) = Eq (a.At (x - 120)) ⋆ Eq (b.At (x - 112)) ⋆ Eq (c.At (x - 104)) := by
  rw [at_app _ _ (b := x - 112) (by rw [ha]; bv_omega) (by simp [ha, hb, hc]),
    at_app _ _ (b := x - 104) (by rw [hb]; bv_omega) (by simp [hb, hc])]
  simp only [Std.ExtHashMap.sep_assoc]

theorem Decode.accept_split_spill_words (x : BitVec 64) (w : List UInt8) (h : w.length = 24) :
    Eq (w.At (x - 120)) = Eq ((w.take 8).At (x - 120)) ⋆ Eq (((w.drop 8).take 8).At (x - 112))
      ⋆ Eq ((w.drop 16).At (x - 104)) := by
  have e : w = w.take 8 ++ (((w.drop 8).take 8) ++ w.drop 16) := by
    conv => lhs; rw [← List.take_append_drop 8 w, ← List.take_append_drop 8 (w.drop 8)]
    simp only [List.drop_drop]
  conv => lhs; rw [e]
  exact Decode.accept_split_three_words x _ _ _ (by simp [h]) (by simp [h]) (by simp [h])

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
/-- **Accept path of the real `(*v1alpha1.AttestationData).UnmarshalSSZ` (Go 1.26.10)**:
on a 128-byte input it returns nil and the receiver holds Slot = buf[0:8], CommitteeIndex =
buf[8:16], a fresh 32-byte BeaconBlockRoot = buf[16:48], and fresh Source / Target objects
decoded from buf[48:88] / buf[88:128]; the input, `state`, `unknownFields`, `sizeCache`, the
caller's frame `R` and the stack guard are unchanged; 240 heap bytes are used. -/
theorem Decode.accept (k : Nat) (hk : unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh unmarshalSSZ k)
    (kS : Nat) (hkS : Prysm.Slot.Code.unmarshalSSZ.IsInfixAt Host.prog kS) (hfS : LabelsFresh Prysm.Slot.Code.unmarshalSSZ kS)
    (kI : Nat) (hkI : Prysm.CommitteeIndex.Code.unmarshalSSZ.IsInfixAt Host.prog kI) (hfI : LabelsFresh Prysm.CommitteeIndex.Code.unmarshalSSZ kI)
    (kC : Nat) (hkC : Prysm.Checkpoint.Code.unmarshalSSZ.IsInfixAt Host.prog kC) (hfC : LabelsFresh Prysm.Checkpoint.Code.unmarshalSSZ kC)
    (kE : Nat) (hkE : Prysm.Epoch.Code.unmarshalSSZ.IsInfixAt Host.prog kE) (hfE : LabelsFresh Prysm.Epoch.Code.unmarshalSSZ kE)
    (in0 in1 root se sroot te troot : List UInt8) (hin0 : in0.length = 8) (hin1 : in1.length = 8)
    (hroot : root.length = 32) (hse : se.length = 8) (hsroot : sroot.length = 32) (hte : te.length = 8)
    (htroot : troot.length = 32)
    (s : MachineData) (ra guard : UInt64)
    (fp s1 s2 s4 sp0 sp1 sp2 l68 rslot lo ast a8 a16 aP aL aC aS aT : List UInt8)
    (hfp : fp.length = 8) (h1 : s1.length = 8) (h2 : s2.length = 8) (h4 : s4.length = 8)
    (hsp0 : sp0.length = 8) (hsp1 : sp1.length = 8) (hsp2 : sp2.length = 8) (hl68 : l68.length = 8)
    (hrs : rslot.length = 8) (hast : ast.length = 8) (ha8 : a8.length = 8) (ha16 : a16.length = 8)
    (haP : aP.length = 8) (haL : aL.length = 8) (haC : aC.length = 8) (haS : aS.length = 8) (haT : aT.length = 8)
    (R : DataMem → Prop) (S : Nat) (hS8 : 8 ≤ S) (hS : S < 2 ^ 60) (hlo : lo.length = S + 96)
    (Heap : Nat → DataMem → Prop) (avail : Nat)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s1.At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16)) ⋆ Eq (s4.At (s.regs.rsp.toBitVec + 32))
      ⋆ Eq (sp0.At (s.regs.rsp.toBitVec - 120)) ⋆ Eq (sp1.At (s.regs.rsp.toBitVec - 112))
      ⋆ Eq (sp2.At (s.regs.rsp.toBitVec - 104)) ⋆ Eq (l68.At (s.regs.rsp.toBitVec - 16))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 128)) ⋆ Eq (lo.At (s.regs.rsp.toBitVec - 224 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Heap avail
      ⋆ Eq (in0.At s.regs.rbx.toBitVec) ⋆ Eq (in1.At (s.regs.rbx.toBitVec + 8))
      ⋆ Eq (root.At (s.regs.rbx.toBitVec + 16)) ⋆ Eq (se.At (s.regs.rbx.toBitVec + 48))
      ⋆ Eq (sroot.At (s.regs.rbx.toBitVec + 56)) ⋆ Eq (te.At (s.regs.rbx.toBitVec + 88))
      ⋆ Eq (troot.At (s.regs.rbx.toBitVec + 96))
      ⋆ Eq (ast.At s.regs.rax.toBitVec) ⋆ Eq (a8.At (s.regs.rax.toBitVec + 8))
      ⋆ Eq (a16.At (s.regs.rax.toBitVec + 16)) ⋆ Eq (aP.At (s.regs.rax.toBitVec + 24))
      ⋆ Eq (aL.At (s.regs.rax.toBitVec + 32)) ⋆ Eq (aC.At (s.regs.rax.toBitVec + 40))
      ⋆ Eq (aS.At (s.regs.rax.toBitVec + 48)) ⋆ Eq (aT.At (s.regs.rax.toBitVec + 56))
      ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R)
    (hguard : guard.toNat + 224 < s.regs.rsp.toNat) (hlen : s.regs.rcx = 128) (hav : 240 ≤ avail)
    (hms : MakesliceContract Heap ElfData.PrysmTarget.typeUint8_addr 1 S) (hmm : MemmoveContract S)
    (hms' : MakesliceContract Heap ElfData.PrysmTarget.typeUint8_addr 1 (S + 96)) (hmm' : MemmoveContract (S + 96))
    (hno : NewobjectContract Heap ElfData.PrysmTarget.typeCheckpoint_addr 72 (S + 96)) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ (p ps pt p1 p2 : BitVec 64) (w lo' : List UInt8), w.length = 8 ∧ lo'.length = S + 96 ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec + 32))
          ⋆ Eq ((Int.toBytes 8 pt.toInt).At (s.regs.rsp.toBitVec - 120))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rbx.toBitVec + 88).toInt).At (s.regs.rsp.toBitVec - 112))
          ⋆ Eq (w.At (s.regs.rsp.toBitVec - 104))
          ⋆ Eq ((Int.toBytes 8 p.toInt).At (s.regs.rsp.toBitVec - 16))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 193)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 128))
          ⋆ Eq (lo'.At (s.regs.rsp.toBitVec - 224 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Heap (avail - 240)
          ⋆ Eq (in0.At s.regs.rbx.toBitVec) ⋆ Eq (in1.At (s.regs.rbx.toBitVec + 8))
          ⋆ Eq (root.At (s.regs.rbx.toBitVec + 16)) ⋆ Eq (se.At (s.regs.rbx.toBitVec + 48))
          ⋆ Eq (sroot.At (s.regs.rbx.toBitVec + 56)) ⋆ Eq (te.At (s.regs.rbx.toBitVec + 88))
          ⋆ Eq (troot.At (s.regs.rbx.toBitVec + 96))
          ⋆ Eq (ast.At s.regs.rax.toBitVec) ⋆ Eq (in0.At (s.regs.rax.toBitVec + 8))
          ⋆ Eq (in1.At (s.regs.rax.toBitVec + 16)) ⋆ Eq ((Int.toBytes 8 p.toInt).At (s.regs.rax.toBitVec + 24))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 32)) ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 40))
          ⋆ Eq ((Int.toBytes 8 ps.toInt).At (s.regs.rax.toBitVec + 48))
          ⋆ Eq ((Int.toBytes 8 pt.toInt).At (s.regs.rax.toBitVec + 56))
          ⋆ Eq (root.At p)
          ⋆ Eq ((List.replicate 8 0).At ps) ⋆ Eq (se.At (ps + 8))
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At (ps + 16)) ⋆ Eq ((Int.toBytes 8 32).At (ps + 24))
          ⋆ Eq ((Int.toBytes 8 32).At (ps + 32)) ⋆ Eq ((List.replicate 32 0).At (ps + 40)) ⋆ Eq (sroot.At p1)
          ⋆ Eq ((List.replicate 8 0).At pt) ⋆ Eq (te.At (pt + 8))
          ⋆ Eq ((Int.toBytes 8 p2.toInt).At (pt + 16)) ⋆ Eq ((Int.toBytes 8 32).At (pt + 24))
          ⋆ Eq ((Int.toBytes 8 32).At (pt + 32)) ⋆ Eq ((List.replicate 32 0).At (pt + 40)) ⋆ Eq (troot.At p2)
          ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  have hsl : Prysm.Slot.Decode.accept_function_spec := Prysm.Slot.Decode.accept_function_spec_holds kS hkS hfS
  have hci : Prysm.CommitteeIndex.Decode.accept_function_spec := Prysm.CommitteeIndex.Decode.accept_function_spec_holds kI hkI hfI
  have hcp : Prysm.Checkpoint.Decode.accept_function_spec Heap S := Prysm.Checkpoint.Decode.accept_function_spec_holds kC hkC hfC kE hkE hfE Heap S hms hmm
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hguard hlen ⊢
  have hl88 : (lo.take (S + 88)).length = S + 88 := by simp [hlo]
  have hl8 : (lo.drop (S + 88)).length = 8 := by simp [hlo]
  have hlos : Eq (lo.At (rsp.toBitVec - 224 - BitVec.ofNat 64 S)) =
      Eq ((lo.take (S + 88)).At (rsp.toBitVec - 224 - BitVec.ofNat 64 S)) ⋆ Eq ((lo.drop (S + 88)).At (rsp.toBitVec - 136)) := by
    conv => lhs; rw [← List.take_append_drop (S + 88) lo]
    exact Decode.accept_low_stack_split _ S hS _ _ hl88 hl8
  rw [hlos] at h_mem
  -- segment 1: entry → L_167 (Slot, CommitteeIndex)
  refine eventually_trans _ _ _ _ (Decode.head k hk hf hsl hci in0 in1 hin0 hin1 _ ra guard fp s1 s2 s4 sp1 rslot
    (lo.drop (S + 88)) ast a8 a16 hfp h1 h2 h4 hsp1 hrs hl8 hast ha8 ha16 _ (by dsimp only; ecancel) hguard hlen) ?_
  rintro ⟨d1, pc1⟩ ⟨hpc1, hrsp1, hrbp1, hr141, Hm1⟩
  dsimp only at hpc1 hrsp1 hrbp1 hr141 Hm1
  subst hpc1
  -- segment 2: L_167 → L_208 (BeaconBlockRoot)
  refine eventually_trans _ _ _ _ (Decode.block_root k hk hf rsp r14 rax.toBitVec rbx.toBitVec root hroot
    (sp0 ++ (Int.toBytes 8 (rbx.toBitVec + 8).toInt ++ sp2)) (Int.toBytes 8 (Host.addrOf (k + 56)).toBitVec.toInt)
    (lo.take (S + 88) ++ Int.toBytes 8 (rsp.toBitVec - 8#64).toInt) l68 aP aL aC
    (by simp only [List.length_append, hsp0, hsp2, Int.toBytes_length]) (Int.toBytes_length 8 _) hl68 haP haL haC _ S hS
    (by simp only [List.length_append, hl88, Int.toBytes_length]) Heap avail (by omega)
    d1 (by rw [hrsp1]; first | rfl | (apply UInt64.toBitVec_inj.mp; simp))
    (by rw [hrbp1]; first | rfl | (apply UInt64.toBitVec_inj.mp; simp)) hr141
    (by rw [Decode.accept_split_three_words _ _ _ _ hsp0 (Int.toBytes_length 8 _) hsp2, Decode.accept_low_stack_split _ S hS _ _ hl88 (Int.toBytes_length 8 _)]
        ecancel) hms' hmm') ?_
  rintro ⟨d2, pc2⟩ ⟨hpc2, hrsp2, hrbp2, hr142, p, spl, lo2, hspl, hlo2, hrbx2, hrdx2, Hm2⟩
  dsimp only at hpc2 hrsp2 hrbp2 hr142 hrbx2 hrdx2 Hm2
  subst hpc2
  rw [Decode.accept_split_spill_words _ _ hspl] at Hm2
  -- segment 3: L_208 → L_2d9 (Source)
  refine eventually_trans _ _ _ _ (Decode.source k hk hf rsp r14 guard rax.toBitVec rbx.toBitVec p se sroot hse hsroot
    (Int.toBytes 8 rdi.toBitVec.toInt) (spl.take 8) ((spl.drop 8).take 8)
    (Int.toBytes 8 (Host.addrOf (k + 107)).toBitVec.toInt) lo2 (Int.toBytes 8 p.toInt) aS
    (Int.toBytes_length 8 _) (by simp [hspl]) (by simp [hspl]) (Int.toBytes_length 8 _) (Int.toBytes_length 8 _) haS
    _ S hS8 hS hlo2 Heap (avail - 32) (by omega) d2 hrsp2 hrbp2 hr142 hrdx2 hrbx2 (by ecancel) hguard hno hcp) ?_
  rintro ⟨d3, pc3⟩ ⟨hpc3, hrsp3, hrbp3, hr143, ps, p1, lo3, hlo3, Hm3⟩
  dsimp only at hpc3 hrsp3 hrbp3 hr143 Hm3
  subst hpc3
  -- segment 4: L_2d9 → return (Target)
  refine eventually_mono (Decode.target k hk hf rsp r14 guard ra rbp rax.toBitVec rbx.toBitVec te troot hte htroot
    (Int.toBytes 8 rdi.toBitVec.toInt) (Int.toBytes 8 ps.toInt) (Int.toBytes 8 (rbx.toBitVec + 48).toInt)
    (Int.toBytes 8 (Host.addrOf (k + 143)).toBitVec.toInt) lo3 aT
    (Int.toBytes_length 8 _) (Int.toBytes_length 8 _) (Int.toBytes_length 8 _) (Int.toBytes_length 8 _) haT
    _ S hS8 hS hlo3 Heap (avail - 32 - 72 - 32) (by omega) d3 hrsp3 hrbp3 hr143 (by ecancel) hguard hno hcp) ?_
  rintro st ⟨e1, e2, e3, e4, e5, e6, pt, p2, lo4, hlo4, Hm4⟩
  rw [show avail - 32 - 72 - 32 - 72 - 32 = avail - 240 by omega] at Hm4
  exact ⟨e1, e2, e3, e4, e5, e6, p, ps, pt, p1, p2, (spl.drop 16), lo4, by simp [hspl], hlo4, by ecancel⟩

end Prysm.AttestationData
