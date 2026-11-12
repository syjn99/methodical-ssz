import E2eScal.Gen5F24PdcDec
import E2eScal.F24PdcSpec

/-!
# Spec alignment of the real `v1alpha1.PartialDataColumnGroupID` decoder (FLAT24 / H7)

Built on the GENERATED theorems of `Gen5F24PdcDec.lean` (`p2dec --gen5`, one-shot run of FLAT24 Part 1; raw output, not
edited):
- `pdc_e2e_accept_spec_k`: if EthLib accepts `bsA` (`prysmPdcDesc`) as `v`, there is `g : PPdc` with `g.toValue = v`
  and `bsA = ppdcEnc g`; with the input chunks of that `g` the machine code returns nil and the receiver holds `g`.
  The statement is the generated accept statement (kind instance) with the input chunks replaced by the
  encoding of `g` (text written by the FLAT24 evidence script `f24speck.py` from the generated statement; then checked
  by Lean against `E2eScal.Gen.pdc_g5dec_accept`).
- `pdc_e2e_reject_size_spec`: `bs.size ≠ 40` → EthLib rejects, and the machine code returns `ssz.ErrSize`
  (generated `pdc_g5dec_reject`).
- `pdc_e2e_reject_complete`: every input that EthLib rejects has `size ≠ 40` (the path condition of the size reject).
Not stated here: that the callee error paths (`fmt.errorf` wraps) are unreachable when `size = 40`.
-/

open Machine Runtime TestTarget E2e E2eScal Codec E2eScal.F24Code EthLib.Serialization.Ssz
variable [Host]

namespace E2eScal.F24

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Accept side: the generated accept statement for the input chunks of the `g` that EthLib decodes. -/
theorem pdc_e2e_accept_spec_k : ∀ (k : Nat) (hk : PdcUnmarshal.IsInfixAt Host.prog k) (hf : LabelsFresh PdcUnmarshal k)
    (kS : Nat) (hkS : E2eAd.Code.SlUnmarshal.IsInfixAt Host.prog kS) (hfS : LabelsFresh E2eAd.Code.SlUnmarshal kS)
    (bsA : Array UInt8) (v : Value) (hd : deserialize prysmPdcDesc bsA = .ok v)
    (s : MachineData) (ra guard : UInt64)
    (fp s1 s2 s4 sp0 sp1 sp2 l28 rslot lo ast aP0 aL0 aC0 aN1 : List UInt8)
    (hfp : fp.length = 8) (hs1 : s1.length = 8) (hs2 : s2.length = 8) (hs4 : s4.length = 8) (hsp0 : sp0.length = 8) (hsp1 : sp1.length = 8) (hsp2 : sp2.length = 8) (hl28 : l28.length = 8) (hrslot : rslot.length = 8) (hast : ast.length = 8) (haP0 : aP0.length = 8) (haL0 : aL0.length = 8) (haC0 : aC0.length = 8) (haN1 : aN1.length = 8)
    (R : DataMem → Prop) (S : Nat) (hS : S < 2 ^ 60) (hlo : lo.length = S + 8)
    (Heap : Nat → DataMem → Prop) (avail : Nat)
    (Pm : ∀ g : PPdc, bsA = ppdcEnc g →
      s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8))
      ⋆ Eq (s1.At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq (s4.At (s.regs.rsp.toBitVec + 32))
      ⋆ Eq (sp0.At (s.regs.rsp.toBitVec - 72))
      ⋆ Eq (sp1.At (s.regs.rsp.toBitVec - 64))
      ⋆ Eq (sp2.At (s.regs.rsp.toBitVec - 56))
      ⋆ Eq (l28.At (s.regs.rsp.toBitVec - 32))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 80))
      ⋆ Eq (lo.At (s.regs.rsp.toBitVec - 88 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Heap avail
      ⋆ Eq (g.beaconBlockRoot.toArray.toList.At s.regs.rbx.toBitVec)
      ⋆ Eq ((uintBytes 8 g.slot.toNat).toList.At (s.regs.rbx.toBitVec + 32))
      ⋆ Eq (ast.At s.regs.rax.toBitVec)
      ⋆ Eq (aP0.At (s.regs.rax.toBitVec + 8))
      ⋆ Eq (aL0.At (s.regs.rax.toBitVec + 16))
      ⋆ Eq (aC0.At (s.regs.rax.toBitVec + 24))
      ⋆ Eq (aN1.At (s.regs.rax.toBitVec + 32))
      ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec)
      ⋆ R)
    (hguard : guard.toNat + 80 < s.regs.rsp.toNat) (hlen : s.regs.rcx.toNat = bsA.size) (hav : 32 ≤ avail)
    (hms : MakesliceC Heap ElfData.CheckpointAndEpoch.e2eU8Type_addr 1 (S + 8)) (hmm : MemmoveC (S + 8)),
    ∃ g : PPdc, g.toValue = v ∧ bsA = ppdcEnc g ∧
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ (p1 : BitVec 64) (x0 x1 : List UInt8), x0.length = 24 ∧ x1.length = S + 8 ∧ 
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec + 32))
          ⋆ Eq (x0.At (s.regs.rsp.toBitVec - 72))
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rsp.toBitVec - 32))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 56)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 80))
          ⋆ Eq (x1.At (s.regs.rsp.toBitVec - 88 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Heap (avail - 32)
          ⋆ Eq (g.beaconBlockRoot.toArray.toList.At s.regs.rbx.toBitVec)
          ⋆ Eq ((uintBytes 8 g.slot.toNat).toList.At (s.regs.rbx.toBitVec + 32))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 24))
          ⋆ Eq ((uintBytes 8 g.slot.toNat).toList.At (s.regs.rax.toBitVec + 32))
          ⋆ Eq (g.beaconBlockRoot.toArray.toList.At p1)
          ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec)
          ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  intro k hk hf kS hkS hfS bsA v hd s ra guard fp s1 s2 s4 sp0 sp1 sp2 l28 rslot lo ast aP0 aL0 aC0 aN1 hfp hs1 hs2 hs4 hsp0 hsp1 hsp2 hl28 hrslot hast haP0 haL0 haC0 haN1 R S hS hlo Heap avail Pm hguard hlen hav hms hmm
  obtain ⟨g, rfl, hb⟩ := ppdc_accepted_is_enc hd
  refine ⟨g, rfl, hb, ?_⟩
  have hn : s.regs.rcx = 40 := by
    apply UInt64.toNat_inj.mp; rw [hlen, hb, ppdc_enc_size]; rfl
  exact E2eScal.Gen.pdc_g5dec_accept k hk hf kS hkS hfS _ _ (by simp) (by simp [Spec.uintBytes_size]) s ra guard fp s1 s2 s4 sp0 sp1 sp2 l28 rslot lo ast aP0 aL0 aC0 aN1 hfp hs1 hs2 hs4 hsp0 hsp1 hsp2 hl28 hrslot hast haP0 haL0 haC0 haN1 R S hS hlo Heap avail (Pm g hb) hguard hn hav hms hmm

/-- `len(buf) ≠ 40`: EthLib rejects, and the machine code returns the two words of `ssz.ErrSize`. -/
theorem pdc_e2e_reject_size_spec (k : Nat) (hk : PdcUnmarshal.IsInfixAt Host.prog k)
    (hf : LabelsFresh PdcUnmarshal k) (bs : Array UInt8) (hbs : bs.size ≠ 40)
    (s : MachineData) (ra guard e0 e1 : UInt64) (fp s2 : List UInt8) (hfp : fp.length = 8) (h2 : s2.length = 8)
    (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At ElfData.CheckpointAndEpoch.e2eErrSize_addr)
      ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrSize" + 8).toBitVec) ⋆ R)
    (hguard : guard.toNat < s.regs.rsp.toNat) (hlen : s.regs.rcx.toNat = bs.size) :
    (∃ e, deserialize prysmPdcDesc bs = .error e) ∧
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
  ⟨ppdc_spec_rejects bs hbs, E2eScal.Gen.pdc_g5dec_reject k hk hf s ra guard e0 e1 fp s2 hfp h2 R h_mem hguard
    (fun h => hbs (by rw [← hlen, h]; rfl))⟩

/-- **`reject_complete`**: an input that EthLib rejects has `size ≠ 40`: the path condition of the size reject.
(The callee error returns are not covered.) -/
theorem pdc_e2e_reject_complete (bs : Array UInt8) (h : ¬ ∃ v, deserialize prysmPdcDesc bs = .ok v) :
    bs.size ≠ 40 := fun h40 => h ((ppdc_spec_accepts_iff bs).mpr h40)

end E2eScal.F24
