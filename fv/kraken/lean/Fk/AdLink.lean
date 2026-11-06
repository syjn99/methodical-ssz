import Fk.AdAccept
import Fk.AdSpec

/-!
# Prysm AttestationData accept path against EthLib

`ad_unmarshal_accept_spec_k`: if EthLib accepts `bsA` as `v`, there is `g`
with `g.toValue = v` and `bsA = adEncode g`; with the input chunks of that `g`
the machine returns nil and the receiver holds `g` (Slot, CommitteeIndex,
-/

open Fk Fk.Code Fv1 EthLib.Serialization.Ssz
variable [Host]

set_option maxHeartbeats 4000000 in
theorem ad_unmarshal_accept_spec_k (k : Nat) (hk : PrysmAttestationDataUnmarshalSSZ.IsInfixAt Host.prog k)
    (hf : LabelsFresh PrysmAttestationDataUnmarshalSSZ k)
    (bsA : Array UInt8) (v : Value) (hd : deserialize adDesc bsA = .ok v)
    (s : MachineData) (ra guard : UInt64)
    (fp s8 s16 l16 l24 rslot c0 c8 cP cL cC cS cT : List UInt8)
    (hfp : fp.length = 8) (hs8 : s8.length = 8) (hs16 : s16.length = 8) (hl16 : l16.length = 8) (hl24 : l24.length = 8)
    (hrs : rslot.length = 8) (hc0 : c0.length = 8) (hc8 : c8.length = 8) (hcP : cP.length = 8) (hcL : cL.length = 8)
    (hcC : cC.length = 8) (hcS : cS.length = 8) (hcT : cT.length = 8)
    (R : DataMem → Prop) (S : Nat) (scratch spa spb : List UInt8) (hsc : scratch.length = S)
    (hspa : spa.length = 8) (hspb : spb.length = 16)
    (Heap : Nat → DataMem → Prop) (avail : Nat)
    (P : ∀ g : AttestationDataG, bsA = adEncode g →
      s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s8.At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq (s16.At (s.regs.rsp.toBitVec + 16)) ⋆ Eq (l16.At (s.regs.rsp.toBitVec - 16))
      ⋆ Eq (l24.At (s.regs.rsp.toBitVec - 24))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 56)) ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - 56 - BitVec.ofNat 64 S))
      ⋆ Eq (spa.At (s.regs.rsp.toBitVec - 48)) ⋆ Eq (spb.At (s.regs.rsp.toBitVec - 40))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16)) ⋆ Heap avail
      ⋆ Eq ((uintBytes 8 g.slot.toNat).toList.At s.regs.rbx.toBitVec)
      ⋆ Eq ((uintBytes 8 g.index.toNat).toList.At (s.regs.rbx.toBitVec + 8))
      ⋆ Eq (g.root.toList.At (s.regs.rbx.toBitVec + 16))
      ⋆ Eq ((uintBytes 8 g.source.epoch.toNat).toList.At (s.regs.rbx.toBitVec + 48))
      ⋆ Eq (g.source.root.toList.At (s.regs.rbx.toBitVec + 56))
      ⋆ Eq ((uintBytes 8 g.target.epoch.toNat).toList.At (s.regs.rbx.toBitVec + 88))
      ⋆ Eq (g.target.root.toList.At (s.regs.rbx.toBitVec + 96))
      ⋆ Eq (c0.At s.regs.rax.toBitVec) ⋆ Eq (c8.At (s.regs.rax.toBitVec + 8))
      ⋆ Eq (cP.At (s.regs.rax.toBitVec + 16)) ⋆ Eq (cL.At (s.regs.rax.toBitVec + 24))
      ⋆ Eq (cC.At (s.regs.rax.toBitVec + 32)) ⋆ Eq (cS.At (s.regs.rax.toBitVec + 40))
      ⋆ Eq (cT.At (s.regs.rax.toBitVec + 48))
      ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R)
    (hguard : guard.toNat < s.regs.rsp.toNat) (hsp : 56 ≤ s.regs.rsp.toNat)
    (hlen : s.regs.rcx.toNat = bsA.size) (hav : 160 ≤ avail)
    (hms : MakesliceC Heap (label "type__" + 48736).toBitVec 1 S) (hmm : MemmoveC S)
    (hno : NewobjectC Heap (label "type__" + 100288).toBitVec 32 S) :
    ∃ g : AttestationDataG, g.toValue = v ∧ bsA = adEncode g ∧
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ p ps pt p1 p2 : BitVec 64, (Eq ((uintBytes 8 g.slot.toNat).toList.At s.regs.rax.toBitVec)
          ⋆ Eq ((uintBytes 8 g.index.toNat).toList.At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 p.toInt).At (s.regs.rax.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 24)) ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 32))
          ⋆ Eq ((Int.toBytes 8 ps.toInt).At (s.regs.rax.toBitVec + 40))
          ⋆ Eq ((Int.toBytes 8 pt.toInt).At (s.regs.rax.toBitVec + 48)) ⋆ Eq (g.root.toList.At p)
          ⋆ Eq ((uintBytes 8 g.source.epoch.toNat).toList.At ps) ⋆ Eq ((Int.toBytes 8 p1.toInt).At (ps + 8))
          ⋆ Eq ((Int.toBytes 8 32).At (ps + 16)) ⋆ Eq ((Int.toBytes 8 32).At (ps + 24))
          ⋆ Eq (g.source.root.toList.At p1)
          ⋆ Eq ((uintBytes 8 g.target.epoch.toNat).toList.At pt) ⋆ Eq ((Int.toBytes 8 p2.toInt).At (pt + 8))
          ⋆ Eq ((Int.toBytes 8 32).At (pt + 16)) ⋆ Eq ((Int.toBytes 8 32).At (pt + 24))
          ⋆ Eq (g.target.root.toList.At p2)
          ⋆ Heap (avail - 160) ⋆ R ⋆ fun _ => True) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  obtain ⟨g, rfl, rfl⟩ := accepted_is_enc (G := AttestationDataG) (toV := AttestationDataG.toValue)
    (enc := adEncode) adDesc_wellFormed ad_serialize ad_toValue_surjective' hd
  refine ⟨g, rfl, rfl, ?_⟩
  have h128 : s.regs.rcx = 128 := by
    apply UInt64.toNat_inj.mp; rw [hlen, ad_encode_size]; rfl
  refine eventually_trans _ _ _ _ (ad_accept_main k hk hf _ _ _ _ _ _ _ (by simp [Fv.uintBytes_size])
    (by simp [Fv.uintBytes_size]) (by simp)
    (by simp [Fv.uintBytes_size]) (by simp) (by simp [Fv.uintBytes_size]) (by simp) s ra guard
    fp s8 s16 l16 l24 rslot c0 c8 cP cL cC cS cT hfp hs8 hs16 hl16 hl24 hrs hc0 hc8 hcP hcL hcC hcS hcT
    R S scratch spa spb hsc hspa hspb Heap avail (P g rfl) hguard hsp h128 hav hms hmm hno) ?_
  rintro st ⟨e1, e2, e3, e4, e5, e6, p, ps, pt, p1, p2, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hm⟩
  exact Eventually.done _ ⟨e1, e2, e3, e4, e5, e6, p, ps, pt, p1, p2, sep_true (by ecancel)⟩
