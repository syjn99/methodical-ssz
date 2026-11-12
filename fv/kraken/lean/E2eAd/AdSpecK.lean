import E2eAd.AdAccept
import E2eAd.AdReject
import E2eAd.Spec

/-!
# Spec alignment of the real AttestationData decoder

- `ad_e2e_accept_spec_k`: if EthLib accepts `bsA` (`prysmAdDesc`, the independent
  consensus-specs Desc) as `v`, there is `g : PAd` with `g.toValue = v` and
  `bsA = padEnc g`; with the input chunks of that `g` the machine code returns nil and
  the receiver holds `g` (Slot / CommitteeIndex = `uintBytes 8`, BeaconBlockRoot = `g.root`
  at the fresh `p`, Source / Target = fresh objects holding `g.source` / `g.target`).
- `ad_e2e_reject_size_spec`: `bs.size ≠ 128` → EthLib rejects, and the machine code
  (with `rcx = bs.size`) returns the two words of `ssz.ErrSize`.
- `ad_e2e_reject_complete` (obligation `reject_complete`): every input that EthLib rejects
  has `size ≠ 128`, the path condition of the one reachable reject site (`return
  ssz.ErrSize`). The four `fmt.Errorf` wrap sites are `unreachable_mc` rows
  (`AdReject.lean`); they are not needed for the join and are not reject coverage.
-/

open Fk E2e E2eAd.Code EthLib.Serialization.Ssz
variable [Host]

namespace E2eAd

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
theorem ad_e2e_accept_spec_k (k : Nat) (hk : AdUnmarshal.IsInfixAt Host.prog k) (hf : LabelsFresh AdUnmarshal k)
    (kS : Nat) (hkS : SlUnmarshal.IsInfixAt Host.prog kS) (hfS : LabelsFresh SlUnmarshal kS)
    (kI : Nat) (hkI : CiUnmarshal.IsInfixAt Host.prog kI) (hfI : LabelsFresh CiUnmarshal kI)
    (kC : Nat) (hkC : E2e.Code.CpUnmarshal.IsInfixAt Host.prog kC) (hfC : LabelsFresh E2e.Code.CpUnmarshal kC)
    (kE : Nat) (hkE : E2e.Code.EpUnmarshal.IsInfixAt Host.prog kE) (hfE : LabelsFresh E2e.Code.EpUnmarshal kE)
    (bsA : Array UInt8) (v : Value) (hd : deserialize prysmAdDesc bsA = .ok v)
    (s : MachineData) (ra guard : UInt64)
    (fp s1 s2 s4 sp0 sp1 sp2 l68 rslot lo ast a8 a16 aP aL aC aS aT : List UInt8)
    (hfp : fp.length = 8) (h1 : s1.length = 8) (h2 : s2.length = 8) (h4 : s4.length = 8)
    (hsp0 : sp0.length = 8) (hsp1 : sp1.length = 8) (hsp2 : sp2.length = 8) (hl68 : l68.length = 8)
    (hrs : rslot.length = 8) (hast : ast.length = 8) (ha8 : a8.length = 8) (ha16 : a16.length = 8)
    (haP : aP.length = 8) (haL : aL.length = 8) (haC : aC.length = 8) (haS : aS.length = 8) (haT : aT.length = 8)
    (R : DataMem → Prop) (S : Nat) (hS8 : 8 ≤ S) (hS : S < 2 ^ 60) (hlo : lo.length = S + 96)
    (Heap : Nat → DataMem → Prop) (avail : Nat)
    (Pm : ∀ g : PAd, bsA = padEnc g →
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
    (hms : MakesliceC Heap E2e.Data.e2eU8Type_addr 1 S) (hmm : MemmoveC S)
    (hms' : MakesliceC Heap E2e.Data.e2eU8Type_addr 1 (S + 96)) (hmm' : MemmoveC (S + 96))
    (hno : NewobjectC Heap E2eAd.Data.adCpType_addr 72 (S + 96)) :
    ∃ g : PAd, g.toValue = v ∧ bsA = padEnc g ∧
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
  obtain ⟨g, rfl, rfl⟩ := pad_accepted_is_enc hd
  refine ⟨g, rfl, rfl, ?_⟩
  have h128 : s.regs.rcx = 128 := by
    apply UInt64.toNat_inj.mp; rw [hlen, pad_enc_size]; rfl
  exact ad_e2e_accept_main k hk hf kS hkS hfS kI hkI hfI kC hkC hfC kE hkE hfE _ _ _ _ _ _ _
    (by simp [Fv.uintBytes_size]) (by simp [Fv.uintBytes_size]) (by simp) (by simp [Fv.uintBytes_size]) (by simp)
    (by simp [Fv.uintBytes_size]) (by simp) s ra guard
    fp s1 s2 s4 sp0 sp1 sp2 l68 rslot lo ast a8 a16 aP aL aC aS aT hfp h1 h2 h4 hsp0 hsp1 hsp2 hl68 hrs hast ha8
    ha16 haP haL haC haS haT R S hS8 hS hlo Heap avail (Pm g rfl) hguard h128 hav hms hmm hms' hmm' hno

/-- `len(buf) ≠ 128`: EthLib rejects, and the machine code returns the two words of `ssz.ErrSize`. -/
theorem ad_e2e_reject_size_spec (k : Nat) (hk : AdUnmarshal.IsInfixAt Host.prog k)
    (hf : LabelsFresh AdUnmarshal k) (bs : Array UInt8) (hbs : bs.size ≠ 128)
    (s : MachineData) (ra guard e0 e1 : UInt64) (fp s2 : List UInt8) (hfp : fp.length = 8) (h2 : s2.length = 8)
    (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At E2e.Data.e2eErrSize_addr)
      ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrSize" + 8).toBitVec) ⋆ R)
    (hguard : guard.toNat < s.regs.rsp.toNat) (hlen : s.regs.rcx.toNat = bs.size) :
    (∃ e, deserialize prysmAdDesc bs = .error e) ∧
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = e0 ∧ st.data.regs.rbx = e1
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14
        ∧ (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At E2e.Data.e2eErrSize_addr)
          ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrSize" + 8).toBitVec) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩ :=
  ⟨pad_spec_rejects bs hbs, ad_e2e_reject_size_main k hk hf s ra guard e0 e1 fp s2 hfp h2 R h_mem hguard
    (fun h => hbs (by rw [← hlen, h]; rfl))⟩

/-- **`reject_complete`**: an input that EthLib rejects reaches the `ssz.ErrSize` site
(path condition `size ≠ 128`). -/
theorem ad_e2e_reject_complete (bs : Array UInt8) (h : ¬ ∃ v, deserialize prysmAdDesc bs = .ok v) :
    bs.size ≠ 128 := fun h128 => h ((pad_spec_accepts_iff bs).mpr h128)

end E2eAd
