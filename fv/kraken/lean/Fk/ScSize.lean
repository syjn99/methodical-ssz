import Fk.Step

/-! Scalars.SizeSSZ on Kraken main: `mov $0x10,%eax; ret` returns 16. -/

open Fk Fk.Code
variable [Host]

theorem sc_size_main (k : Nat) (hk : ScalarsSizeSSZ.IsInfixAt Host.prog k) (s : MachineData) (ra : UInt64)
    (R : DataMem → Prop) (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec) ⋆ R) :
    Eventually (step1 Host.exe) (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = 16)
      ⟨s, Host.addrOf k⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem ⊢
  apply estep (isInfixAt_drop hk 0)
  kunfold
  apply estep (isInfixAt_drop hk 1)
  kunfold
  apply estep (isInfixAt_drop hk 2)
  kunfold
  apply load_step _ _ _ _ (Int.toBytes 8 ra.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  apply Eventually.done
  simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  exact ⟨trivial, rfl⟩
