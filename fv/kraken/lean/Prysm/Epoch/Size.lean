module

public import Machine.Step
public import Prysm.Epoch.Code
public import Prysm.Epoch.SpecDescription
public import Spec.TestFixed

@[expose] public section

/-!
# SizeSSZ of the hand-written Prysm `primitives.Epoch`

- `Size.result`: `(*primitives.Epoch).SizeSSZ` (directives 0 label, 1 `mov $0x8,%eax`,
  2 `retq`) returns 8 with memory unchanged.
- `Size.result_spec`: 8 is the length of `serialize desc (.uint x)` for every 64-bit value `x`.
-/

open Machine Runtime Prysm.Epoch.Code EthLib.Serialization.Ssz

namespace Prysm.Epoch

/-- EthLib encodes a 64-bit value of `.uint 8` as its 8 little-endian bytes. -/
theorem uint64_serialize_eq (x : UInt64) : serialize (.uint 8) (.uint x.toNat) = .ok (uintBytes 8 x.toNat) := by
  simp [serialize, x.toNat_lt]

theorem Size.result_spec (x : UInt64) : ∃ bs, serialize desc (.uint x.toNat) = .ok bs ∧ bs.size = 8 :=
  ⟨uintBytes 8 x.toNat, uint64_serialize_eq x, Spec.uintBytes_size 8 x.toNat⟩

variable [Host]

theorem Size.result (k : Nat) (hk : sizeSSZ.IsInfixAt Host.prog k) (s : MachineData) (ra : UInt64)
    (R : DataMem → Prop) (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = 8 ∧ st.data.regs.rsp = s.regs.rsp + 8
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

end Prysm.Epoch
