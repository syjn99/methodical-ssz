import Machine.Step
import Prysm.AttestationData.Code
import Prysm.AttestationData.Spec

/-!
# SizeSSZ of `v1alpha1.AttestationData`

- `Size.result`: `(*AttestationData).SizeSSZ` (directives 0 label, 1 `mov $0x80,%eax`,
  2 `retq`) returns 128 with memory unchanged.
- `Size.result_spec`: 128 is the length of `serialize desc g.toValue` (`desc_fixedSize` gives the same size).
-/

open Machine Runtime Prysm.AttestationData.Code EthLib.Serialization.Ssz

namespace Prysm.AttestationData

theorem Size.result_spec (g : SszValue) : ∃ bs, serialize desc g.toValue = .ok bs ∧ bs.size = 128 :=
  ⟨SszValue.encode g, SszValue.serialize_eq g, SszValue.encode_size g⟩

variable [Host]

theorem Size.result (k : Nat) (hk : sizeSSZ.IsInfixAt Host.prog k) (s : MachineData) (ra : UInt64)
    (R : DataMem → Prop) (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = 128 ∧ st.data.regs.rsp = s.regs.rsp + 8
        ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14 ∧ st.data.dmem = s.dmem)
      ⟨s, Host.addrOf k⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem ⊢
  step_directive hk sizeSSZ 0
  step_directive hk sizeSSZ 1
  step_directive hk sizeSSZ 2
  apply load_step _ _ _ _ (Int.toBytes 8 ra.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  unfold_step
  apply Eventually.done
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | exact trivial
    | with_reducible rfl
    | rfl
    | (apply UInt64.toBitVec_inj.mp; simp; done)

end Prysm.AttestationData
