import Fk.Step

/-! Scalars.SizeSSZ on Kraken main: `mov $0x10,%eax; ret` returns 16. The
memory is unchanged (fix 3 X4, as the other size theorems) and r14 (Go's g) is
kept. -/

open Fk Fk.Code
variable [Host]

theorem sc_size_main (k : Nat) (hk : ScalarsSizeSSZ.IsInfixAt Host.prog k) (s : MachineData) (ra : UInt64)
    (R : DataMem → Prop) (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = 16 ∧ st.data.regs.rsp = s.regs.rsp + 8
        ∧ st.data.regs.r14 = s.regs.r14 ∧ st.data.dmem = s.dmem)
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
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> first | trivial | rfl | (apply UInt64.toBitVec_inj.mp; simp)
