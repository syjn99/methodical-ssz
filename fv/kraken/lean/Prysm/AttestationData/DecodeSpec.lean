import Prysm.AttestationData.DecodeAccept
import Prysm.AttestationData.DecodeRejectSize
import Prysm.AttestationData.Spec

/-!
# Spec alignment of the real AttestationData decoder

- `Decode.accept_spec`: if EthLib accepts `bsA` (`desc`, the independent
  consensus-specs Desc) as `v`, there is `g : SszValue` with `g.toValue = v` and
  `bsA = SszValue.encode g`; with the input chunks of that `g` the machine code returns nil and
  the receiver holds `g` (Slot / CommitteeIndex = `uintBytes 8`, BeaconBlockRoot = `g.root`
  at the fresh `p`, Source / Target = fresh objects holding `g.source` / `g.target`).
- `Decode.reject_size_spec`: `bs.size ≠ 128` → EthLib rejects, and the machine code
  (with `rcx = bs.size`) returns the two words of `ssz.ErrSize`.
- `Decode.reject_complete` (obligation `reject_complete`): every input that EthLib rejects
  has `size ≠ 128`, the path condition of the one reachable reject site (`return
  ssz.ErrSize`). The four `fmt.Errorf` wrap sites are `unreachable_mc` rows
  (`AdReject.lean`); they are not needed for the join and are not reject coverage.
-/

open Machine Runtime TestTarget Prysm.AttestationData.Code EthLib.Serialization.Ssz
variable [Host]

namespace Prysm.AttestationData

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
theorem Decode.accept_spec (k : Nat) (hk : unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh unmarshalSSZ k)
    (kS : Nat) (hkS : slotUnmarshalSSZ.IsInfixAt Host.prog kS) (hfS : LabelsFresh slotUnmarshalSSZ kS)
    (kI : Nat) (hkI : committeeIndexUnmarshalSSZ.IsInfixAt Host.prog kI) (hfI : LabelsFresh committeeIndexUnmarshalSSZ kI)
    (kC : Nat) (hkC : Prysm.Checkpoint.Code.unmarshalSSZ.IsInfixAt Host.prog kC) (hfC : LabelsFresh Prysm.Checkpoint.Code.unmarshalSSZ kC)
    (kE : Nat) (hkE : Prysm.Epoch.Code.unmarshalSSZ.IsInfixAt Host.prog kE) (hfE : LabelsFresh Prysm.Epoch.Code.unmarshalSSZ kE)
    (bsA : Array UInt8) (v : Value) (hd : deserialize desc bsA = .ok v)
    (s : MachineData) (ra guard : UInt64)
    (fp s1 s2 s4 sp0 sp1 sp2 l68 rslot lo ast a8 a16 aP aL aC aS aT : List UInt8)
    (hfp : fp.length = 8) (h1 : s1.length = 8) (h2 : s2.length = 8) (h4 : s4.length = 8)
    (hsp0 : sp0.length = 8) (hsp1 : sp1.length = 8) (hsp2 : sp2.length = 8) (hl68 : l68.length = 8)
    (hrs : rslot.length = 8) (hast : ast.length = 8) (ha8 : a8.length = 8) (ha16 : a16.length = 8)
    (haP : aP.length = 8) (haL : aL.length = 8) (haC : aC.length = 8) (haS : aS.length = 8) (haT : aT.length = 8)
    (R : DataMem → Prop) (S : Nat) (hS8 : 8 ≤ S) (hS : S < 2 ^ 60) (hlo : lo.length = S + 96)
    (Heap : Nat → DataMem → Prop) (avail : Nat)
    (Pm : ∀ g : SszValue, bsA = SszValue.encode g →
      s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s1.At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16)) ⋆ Eq (s4.At (s.regs.rsp.toBitVec + 32))
      ⋆ Eq (sp0.At (s.regs.rsp.toBitVec - 120)) ⋆ Eq (sp1.At (s.regs.rsp.toBitVec - 112))
      ⋆ Eq (sp2.At (s.regs.rsp.toBitVec - 104)) ⋆ Eq (l68.At (s.regs.rsp.toBitVec - 16))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 128)) ⋆ Eq (lo.At (s.regs.rsp.toBitVec - 224 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Heap avail
      ⋆ Eq ((uintBytes 8 g.slot.toNat).toList.At s.regs.rbx.toBitVec) ⋆ Eq ((uintBytes 8 g.index.toNat).toList.At (s.regs.rbx.toBitVec + 8))
      ⋆ Eq (g.root.toList.At (s.regs.rbx.toBitVec + 16)) ⋆ Eq ((uintBytes 8 g.source.epoch.toNat).toList.At (s.regs.rbx.toBitVec + 48))
      ⋆ Eq (g.source.root.toList.At (s.regs.rbx.toBitVec + 56)) ⋆ Eq ((uintBytes 8 g.target.epoch.toNat).toList.At (s.regs.rbx.toBitVec + 88))
      ⋆ Eq (g.target.root.toList.At (s.regs.rbx.toBitVec + 96))
      ⋆ Eq (ast.At s.regs.rax.toBitVec) ⋆ Eq (a8.At (s.regs.rax.toBitVec + 8))
      ⋆ Eq (a16.At (s.regs.rax.toBitVec + 16)) ⋆ Eq (aP.At (s.regs.rax.toBitVec + 24))
      ⋆ Eq (aL.At (s.regs.rax.toBitVec + 32)) ⋆ Eq (aC.At (s.regs.rax.toBitVec + 40))
      ⋆ Eq (aS.At (s.regs.rax.toBitVec + 48)) ⋆ Eq (aT.At (s.regs.rax.toBitVec + 56))
      ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R)
    (hguard : guard.toNat + 224 < s.regs.rsp.toNat) (hlen : s.regs.rcx.toNat = bsA.size) (hav : 240 ≤ avail)
    (hms : MakesliceC Heap ElfData.CheckpointAndEpoch.e2eU8Type_addr 1 S) (hmm : MemmoveC S)
    (hms' : MakesliceC Heap ElfData.CheckpointAndEpoch.e2eU8Type_addr 1 (S + 96)) (hmm' : MemmoveC (S + 96))
    (hno : NewobjectC Heap ElfData.AttestationData.adCpType_addr 72 (S + 96)) :
    ∃ g : SszValue, g.toValue = v ∧ bsA = SszValue.encode g ∧
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
          ⋆ Eq ((uintBytes 8 g.slot.toNat).toList.At s.regs.rbx.toBitVec) ⋆ Eq ((uintBytes 8 g.index.toNat).toList.At (s.regs.rbx.toBitVec + 8))
          ⋆ Eq (g.root.toList.At (s.regs.rbx.toBitVec + 16)) ⋆ Eq ((uintBytes 8 g.source.epoch.toNat).toList.At (s.regs.rbx.toBitVec + 48))
          ⋆ Eq (g.source.root.toList.At (s.regs.rbx.toBitVec + 56)) ⋆ Eq ((uintBytes 8 g.target.epoch.toNat).toList.At (s.regs.rbx.toBitVec + 88))
          ⋆ Eq (g.target.root.toList.At (s.regs.rbx.toBitVec + 96))
          ⋆ Eq (ast.At s.regs.rax.toBitVec) ⋆ Eq ((uintBytes 8 g.slot.toNat).toList.At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((uintBytes 8 g.index.toNat).toList.At (s.regs.rax.toBitVec + 16)) ⋆ Eq ((Int.toBytes 8 p.toInt).At (s.regs.rax.toBitVec + 24))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 32)) ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 40))
          ⋆ Eq ((Int.toBytes 8 ps.toInt).At (s.regs.rax.toBitVec + 48))
          ⋆ Eq ((Int.toBytes 8 pt.toInt).At (s.regs.rax.toBitVec + 56))
          ⋆ Eq (g.root.toList.At p)
          ⋆ Eq ((List.replicate 8 0).At ps) ⋆ Eq ((uintBytes 8 g.source.epoch.toNat).toList.At (ps + 8))
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At (ps + 16)) ⋆ Eq ((Int.toBytes 8 32).At (ps + 24))
          ⋆ Eq ((Int.toBytes 8 32).At (ps + 32)) ⋆ Eq ((List.replicate 32 0).At (ps + 40)) ⋆ Eq (g.source.root.toList.At p1)
          ⋆ Eq ((List.replicate 8 0).At pt) ⋆ Eq ((uintBytes 8 g.target.epoch.toNat).toList.At (pt + 8))
          ⋆ Eq ((Int.toBytes 8 p2.toInt).At (pt + 16)) ⋆ Eq ((Int.toBytes 8 32).At (pt + 24))
          ⋆ Eq ((Int.toBytes 8 32).At (pt + 32)) ⋆ Eq ((List.replicate 32 0).At (pt + 40)) ⋆ Eq (g.target.root.toList.At p2)
          ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  obtain ⟨g, rfl, rfl⟩ := SszValue.accepted_is_encoding hd
  refine ⟨g, rfl, rfl, ?_⟩
  have h128 : s.regs.rcx = 128 := by
    apply UInt64.toNat_inj.mp; rw [hlen, SszValue.enc_size]; rfl
  exact Decode.accept k hk hf kS hkS hfS kI hkI hfI kC hkC hfC kE hkE hfE _ _ _ _ _ _ _
    (by simp [Spec.uintBytes_size]) (by simp [Spec.uintBytes_size]) (by simp) (by simp [Spec.uintBytes_size]) (by simp)
    (by simp [Spec.uintBytes_size]) (by simp) s ra guard
    fp s1 s2 s4 sp0 sp1 sp2 l68 rslot lo ast a8 a16 aP aL aC aS aT hfp h1 h2 h4 hsp0 hsp1 hsp2 hl68 hrs hast ha8
    ha16 haP haL haC haS haT R S hS8 hS hlo Heap avail (Pm g rfl) hguard h128 hav hms hmm hms' hmm' hno

/-- `len(buf) ≠ 128`: EthLib rejects, and the machine code returns the two words of `ssz.ErrSize`. -/
theorem Decode.reject_size_spec (k : Nat) (hk : unmarshalSSZ.IsInfixAt Host.prog k)
    (hf : LabelsFresh unmarshalSSZ k) (bs : Array UInt8) (hbs : bs.size ≠ 128)
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

/-- **`reject_complete`**: an input that EthLib rejects reaches the `ssz.ErrSize` site
(path condition `size ≠ 128`). -/
theorem Decode.reject_complete (bs : Array UInt8) (h : ¬ ∃ v, deserialize desc bs = .ok v) :
    bs.size ≠ 128 := fun h128 => h ((SszValue.spec_accepts_iff bs).mpr h128)

end Prysm.AttestationData
