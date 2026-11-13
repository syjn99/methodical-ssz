import Prysm.HistoricalBatch.DecodeSpec

/-!
# Negative-suite targets for the spec companions of the HistoricalBatch decoder

`spec_prop` and `complete_prop` are copies of the frozen `Decode.reject_size_spec_statement` and `Decode.reject_complete_statement`
(equal by `rfl`, the `example`s at the end). `spec_check` and `complete_chk` prove them again from the spec lemmas with
the proof text of the companions. A mutant changes the size constant inside a copy: the EthLib rejection property and
the completeness property then no longer hold for that size, so the proof must fail inside the theorem
(`lv/negcases-spec.json`). The `example`s lie after the theorems; the negative runner cuts the module at the target.
-/

open Machine Runtime EthLib.Serialization.Ssz Prysm.HistoricalBatch.Code
variable [Host]

namespace Prysm.HistoricalBatch.NegativeSuiteTargets

def spec_prop : Prop :=
  ∀ (k : Nat) (hk : unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh unmarshalSSZ k)
    (bs : Array UInt8) (hbs : bs.size ≠ 524288)
    (s : MachineData) (ra guard e0 e1 : UInt64) (fp s2 : List UInt8) (hfp : fp.length = 8) (h2 : s2.length = 8)
    (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At ElfData.PrysmTarget.sszErrSize_addr)
      ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrSize" + 8).toBitVec) ⋆ R)
    (hguard : guard.toNat < s.regs.rsp.toNat) (hlen : s.regs.rcx.toNat = bs.size),
    (∃ e, deserialize desc bs = .error e) ∧
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = e0 ∧ st.data.regs.rbx = e1
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14
        ∧ (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At ElfData.PrysmTarget.sszErrSize_addr)
          ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrSize" + 8).toBitVec) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩

theorem spec_check : spec_prop := by
  intro k hk hf bs hbs s ra guard e0 e1 fp s2 hfp h2 R h_mem hguard hlen
  exact ⟨spec_rejects bs hbs, Decode.reject_size k hk hf s ra guard e0 e1 fp s2 hfp h2 R h_mem hguard
    (fun h => hbs (by rw [← hlen, h]; rfl))⟩

def complete_prop : Prop :=
  ∀ bs : Array UInt8, (¬ ∃ v, deserialize desc bs = .ok v) → bs.size ≠ 524288

theorem complete_chk : complete_prop :=
  fun bs h h' => h ((spec_accepts_iff bs).mpr h')

example : spec_prop = Decode.reject_size_spec_statement := rfl
example : complete_prop = Decode.reject_complete_statement := rfl

end Prysm.HistoricalBatch.NegativeSuiteTargets
