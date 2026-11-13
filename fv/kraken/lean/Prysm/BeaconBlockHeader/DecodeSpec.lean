import Prysm.BeaconBlockHeader.DecodeAccept
import Prysm.BeaconBlockHeader.DecodeRejectSize
import Prysm.BeaconBlockHeader.Spec

/-!
# Spec alignment of the real BeaconBlockHeader decoder (hold-out)

Hand-written (the text of `Prysm/AttestationData/DecodeSpec.lean` with the BeaconBlockHeader
statement).
- `Decode.accept_spec`: if EthLib accepts `bsA` (`desc`, the independent consensus-specs Desc)
  as `v`, there is `g : SszValue` with `g.toValue = v` and `bsA = SszValue.encode g`; with the input chunks of that `g`
  the machine code returns nil and the receiver holds `g` (Slot / ProposerIndex = `uintBytes 8`, the three
  roots at fresh `p1 p2 p3` with len = cap = 32).
- `Decode.reject_size_spec`: `bs.size ≠ 112` → EthLib rejects, and the machine code (with `rcx = bs.size`)
  returns the two words of `ssz.ErrSize`.
- `Decode.reject_complete`: every input that EthLib rejects has `size ≠ 112`, the path condition of the one
  reachable reject site. The two `fmt.Errorf` wraps are not reached on 112-byte inputs (`Prysm/BeaconBlockHeader/DecodeRejectSize.lean`).
-/

open Machine Runtime Prysm.AttestationData.Code Prysm.BeaconBlockHeader.Code Codec EthLib.Serialization.Ssz
variable [Host]

namespace Prysm.BeaconBlockHeader

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem Decode.accept_spec (k : Nat) (hk : Code.unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh Code.unmarshalSSZ k)
    (kS : Nat) (hkS : Prysm.Slot.Code.unmarshalSSZ.IsInfixAt Host.prog kS) (hfS : LabelsFresh Prysm.Slot.Code.unmarshalSSZ kS)
    (kV : Nat) (hkV : Prysm.ValidatorIndex.Code.unmarshalSSZ.IsInfixAt Host.prog kV) (hfV : LabelsFresh Prysm.ValidatorIndex.Code.unmarshalSSZ kV)
    (bsA : Array UInt8) (v : Value) (hd : deserialize desc bsA = .ok v)
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
    (Pm : ∀ g : SszValue, bsA = SszValue.encode g →
      s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s1.At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16)) ⋆ Eq (s4.At (s.regs.rsp.toBitVec + 32))
      ⋆ Eq (sp0.At (s.regs.rsp.toBitVec - 104)) ⋆ Eq (sp1.At (s.regs.rsp.toBitVec - 96))
      ⋆ Eq (sp2.At (s.regs.rsp.toBitVec - 88))
      ⋆ Eq (s28.At (s.regs.rsp.toBitVec - 64)) ⋆ Eq (s30.At (s.regs.rsp.toBitVec - 56))
      ⋆ Eq (l38.At (s.regs.rsp.toBitVec - 48))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 112)) ⋆ Eq (lo.At (s.regs.rsp.toBitVec - 120 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Heap avail
      ⋆ Eq ((uintBytes 8 g.slot.toNat).toList.At s.regs.rbx.toBitVec)
      ⋆ Eq ((uintBytes 8 g.proposer.toNat).toList.At (s.regs.rbx.toBitVec + 8))
      ⋆ Eq (g.parent.toList.At (s.regs.rbx.toBitVec + 16)) ⋆ Eq (g.state.toList.At (s.regs.rbx.toBitVec + 48))
      ⋆ Eq (g.body.toList.At (s.regs.rbx.toBitVec + 80))
      ⋆ Eq (ast.At s.regs.rax.toBitVec) ⋆ Eq (a8.At (s.regs.rax.toBitVec + 8))
      ⋆ Eq (a16.At (s.regs.rax.toBitVec + 16))
      ⋆ Eq (aP1.At (s.regs.rax.toBitVec + 24)) ⋆ Eq (aL1.At (s.regs.rax.toBitVec + 32))
      ⋆ Eq (aC1.At (s.regs.rax.toBitVec + 40))
      ⋆ Eq (aP2.At (s.regs.rax.toBitVec + 48)) ⋆ Eq (aL2.At (s.regs.rax.toBitVec + 56))
      ⋆ Eq (aC2.At (s.regs.rax.toBitVec + 64))
      ⋆ Eq (aP3.At (s.regs.rax.toBitVec + 72)) ⋆ Eq (aL3.At (s.regs.rax.toBitVec + 80))
      ⋆ Eq (aC3.At (s.regs.rax.toBitVec + 88))
      ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R)
    (hguard : guard.toNat + 112 < s.regs.rsp.toNat) (hlen : s.regs.rcx.toNat = bsA.size) (hav : 96 ≤ avail)
    (hms : MakesliceC Heap ElfData.CheckpointAndEpoch.e2eU8Type_addr 1 (S + 8)) (hmm : MemmoveC (S + 8)) :
    ∃ g : SszValue, g.toValue = v ∧ bsA = SszValue.encode g ∧
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
          ⋆ Eq ((uintBytes 8 g.slot.toNat).toList.At s.regs.rbx.toBitVec)
          ⋆ Eq ((uintBytes 8 g.proposer.toNat).toList.At (s.regs.rbx.toBitVec + 8))
          ⋆ Eq (g.parent.toList.At (s.regs.rbx.toBitVec + 16)) ⋆ Eq (g.state.toList.At (s.regs.rbx.toBitVec + 48))
          ⋆ Eq (g.body.toList.At (s.regs.rbx.toBitVec + 80))
          ⋆ Eq (ast.At s.regs.rax.toBitVec) ⋆ Eq ((uintBytes 8 g.slot.toNat).toList.At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((uintBytes 8 g.proposer.toNat).toList.At (s.regs.rax.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 24))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 32)) ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 40))
          ⋆ Eq ((Int.toBytes 8 p2.toInt).At (s.regs.rax.toBitVec + 48))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 56)) ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 64))
          ⋆ Eq ((Int.toBytes 8 p3.toInt).At (s.regs.rax.toBitVec + 72))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 80)) ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 88))
          ⋆ Eq (g.parent.toList.At p1) ⋆ Eq (g.state.toList.At p2) ⋆ Eq (g.body.toList.At p3)
          ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  obtain ⟨g, rfl, rfl⟩ := SszValue.accepted_is_encoding hd
  refine ⟨g, rfl, rfl, ?_⟩
  have h112 : s.regs.rcx = 112 := by
    apply UInt64.toNat_inj.mp; rw [hlen, SszValue.enc_size]; rfl
  exact Decode.accept k hk hf kS hkS hfS kV hkV hfV _ _ _ _ _
    (by simp [Spec.uintBytes_size]) (by simp [Spec.uintBytes_size]) (by simp) (by simp) (by simp) s ra guard
    fp s1 s2 s4 sp0 sp1 sp2 s28 s30 l38 rslot lo ast a8 a16 aP1 aL1 aC1 aP2 aL2 aC2 aP3 aL3 aC3
    hfp h1 h2 h4 hsp0 hsp1 hsp2 hs28 hs30 hl38 hrs hast ha8 ha16 haP1 haL1 haC1 haP2 haL2 haC2 haP3 haL3 haC3
    R S hS hlo Heap avail (Pm g rfl) hguard h112 hav hms hmm

/-- `len(buf) ≠ 112`: EthLib rejects, and the machine code returns the two words of `ssz.ErrSize`. -/
theorem Decode.reject_size_spec (k : Nat) (hk : Code.unmarshalSSZ.IsInfixAt Host.prog k)
    (hf : LabelsFresh Code.unmarshalSSZ k) (bs : Array UInt8) (hbs : bs.size ≠ 112)
    (s : MachineData) (ra guard e0 e1 : UInt64) (fp s2 : List UInt8) (hfp : fp.length = 8) (h2 : s2.length = 8)
    (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At ElfData.CheckpointAndEpoch.e2eErrSize_addr)
      ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrSize" + 8).toBitVec) ⋆ R)
    (hguard : guard.toNat < s.regs.rsp.toNat) (hlen : s.regs.rcx.toNat = bs.size) :
    (∃ e, deserialize desc bs = .error e) ∧
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = e0 ∧ st.data.regs.rbx = e1
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14
        ∧ (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At ElfData.CheckpointAndEpoch.e2eErrSize_addr)
          ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrSize" + 8).toBitVec) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩ :=
  ⟨SszValue.spec_rejects bs hbs, Decode.reject_size k hk hf s ra guard e0 e1 fp s2 hfp h2 R h_mem hguard
    (fun h => hbs (by rw [← hlen, h]; rfl))⟩

/-- **`reject_complete`**: an input that EthLib rejects reaches the `ssz.ErrSize` site (path condition
`size ≠ 112`). -/
theorem Decode.reject_complete (bs : Array UInt8) (h : ¬ ∃ v, deserialize desc bs = .ok v) :
    bs.size ≠ 112 := fun h112 => h ((SszValue.spec_accepts_iff bs).mpr h112)

end Prysm.BeaconBlockHeader
