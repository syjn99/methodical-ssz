import E2eScal.Gen5F24BsrDec
import E2eScal.F24BsrSpec

/-!
# Spec alignment of the real `v1alpha1.BlobSidecarsByRangeRequest` decoder (FLAT24 / H7)

Built on the GENERATED theorems of `Gen5F24BsrDec.lean` (`p2dec --gen5`, one-shot run of FLAT24 Part 1; raw output, not
edited):
- `bsr_e2e_accept_spec_k`: if EthLib accepts `bsA` (`prysmBsrDesc`) as `v`, there is `g : PBsr` with `g.toValue = v`
  and `bsA = pbsrEnc g`; with the input chunks of that `g` the machine code returns nil and the receiver holds `g`.
  The statement is the generated accept statement (kind instance) with the input chunks replaced by the
  encoding of `g` (text written by the FLAT24 evidence script `f24speck.py` from the generated statement; then checked
  by Lean against `E2eScal.Gen.bsr_g5dec_accept`).
- `bsr_e2e_reject_size_spec`: `bs.size ≠ 16` → EthLib rejects, and the machine code returns `ssz.ErrSize`
  (generated `bsr_g5dec_reject`).
- `bsr_e2e_reject_complete`: every input that EthLib rejects has `size ≠ 16` (the path condition of the size reject).
Not stated here: that the callee error paths (`fmt.errorf` wraps) are unreachable when `size = 16`.
-/

open Machine Runtime TestTarget E2e E2eScal Codec E2eScal.F24Code EthLib.Serialization.Ssz
variable [Host]

namespace E2eScal.F24

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Accept side: the generated accept statement for the input chunks of the `g` that EthLib decodes. -/
theorem bsr_e2e_accept_spec_k : ∀ (k : Nat) (hk : BsrUnmarshal.IsInfixAt Host.prog k) (hf : LabelsFresh BsrUnmarshal k)
    (kS : Nat) (hkS : Prysm.AttestationData.Code.slotUnmarshalSSZ.IsInfixAt Host.prog kS) (hfS : LabelsFresh Prysm.AttestationData.Code.slotUnmarshalSSZ kS)
    (bsA : Array UInt8) (v : Value) (hd : deserialize prysmBsrDesc bsA = .ok v)
    (s : MachineData) (ra guard : UInt64)
    (fp s1 s2 sp1 rslot lo ast aN0 aN1 : List UInt8)
    (hfp : fp.length = 8) (hs1 : s1.length = 8) (hs2 : s2.length = 8) (hsp1 : sp1.length = 8) (hrslot : rslot.length = 8) (hlo : lo.length = 8) (hast : ast.length = 8) (haN0 : aN0.length = 8) (haN1 : aN1.length = 8)
    (R : DataMem → Prop)
    (Pm : ∀ g : PBsr, bsA = pbsrEnc g →
      s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8))
      ⋆ Eq (s1.At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq (sp1.At (s.regs.rsp.toBitVec - 56))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 72))
      ⋆ Eq (lo.At (s.regs.rsp.toBitVec - 80))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq ((uintBytes 8 g.startSlot.toNat).toList.At s.regs.rbx.toBitVec)
      ⋆ Eq ((uintBytes 8 g.count.toNat).toList.At (s.regs.rbx.toBitVec + 8))
      ⋆ Eq (ast.At s.regs.rax.toBitVec)
      ⋆ Eq (aN0.At (s.regs.rax.toBitVec + 8))
      ⋆ Eq (aN1.At (s.regs.rax.toBitVec + 16))
      ⋆ R)
    (hguard : guard.toNat + 72 < s.regs.rsp.toNat) (hlen : s.regs.rcx.toNat = bsA.size),
    ∃ g : PBsr, g.toValue = v ∧ bsA = pbsrEnc g ∧
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ (x0 x1 : List UInt8), x0.length = 8 ∧ x1.length = 8 ∧ 
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq (x0.At (s.regs.rsp.toBitVec - 56))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 18)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 72))
          ⋆ Eq (x1.At (s.regs.rsp.toBitVec - 80))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq ((uintBytes 8 g.startSlot.toNat).toList.At s.regs.rbx.toBitVec)
          ⋆ Eq ((uintBytes 8 g.count.toNat).toList.At (s.regs.rbx.toBitVec + 8))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq ((uintBytes 8 g.startSlot.toNat).toList.At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((uintBytes 8 g.count.toNat).toList.At (s.regs.rax.toBitVec + 16))
          ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  intro k hk hf kS hkS hfS bsA v hd s ra guard fp s1 s2 sp1 rslot lo ast aN0 aN1 hfp hs1 hs2 hsp1 hrslot hlo hast haN0 haN1 R Pm hguard hlen
  obtain ⟨g, rfl, hb⟩ := pbsr_accepted_is_enc hd
  refine ⟨g, rfl, hb, ?_⟩
  have hn : s.regs.rcx = 16 := by
    apply UInt64.toNat_inj.mp; rw [hlen, hb, pbsr_enc_size]; rfl
  exact E2eScal.Gen.bsr_g5dec_accept k hk hf kS hkS hfS _ _ (by simp [Spec.uintBytes_size]) (by simp [Spec.uintBytes_size]) s ra guard fp s1 s2 sp1 rslot lo ast aN0 aN1 hfp hs1 hs2 hsp1 hrslot hlo hast haN0 haN1 R (Pm g hb) hguard hn

/-- `len(buf) ≠ 16`: EthLib rejects, and the machine code returns the two words of `ssz.ErrSize`. -/
theorem bsr_e2e_reject_size_spec (k : Nat) (hk : BsrUnmarshal.IsInfixAt Host.prog k)
    (hf : LabelsFresh BsrUnmarshal k) (bs : Array UInt8) (hbs : bs.size ≠ 16)
    (s : MachineData) (ra guard e0 e1 : UInt64) (fp s2 : List UInt8) (hfp : fp.length = 8) (h2 : s2.length = 8)
    (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At ElfData.CheckpointAndEpoch.e2eErrSize_addr)
      ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrSize" + 8).toBitVec) ⋆ R)
    (hguard : guard.toNat < s.regs.rsp.toNat) (hlen : s.regs.rcx.toNat = bs.size) :
    (∃ e, deserialize prysmBsrDesc bs = .error e) ∧
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
  ⟨pbsr_spec_rejects bs hbs, E2eScal.Gen.bsr_g5dec_reject k hk hf s ra guard e0 e1 fp s2 hfp h2 R h_mem hguard
    (fun h => hbs (by rw [← hlen, h]; rfl))⟩

/-- **`reject_complete`**: an input that EthLib rejects has `size ≠ 16`: the path condition of the size reject.
(The callee error returns are not covered.) -/
theorem bsr_e2e_reject_complete (bs : Array UInt8) (h : ¬ ∃ v, deserialize prysmBsrDesc bs = .ok v) :
    bs.size ≠ 16 := fun h16 => h ((pbsr_spec_accepts_iff bs).mpr h16)

end E2eScal.F24
