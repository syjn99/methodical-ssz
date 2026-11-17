import Machine.Step
import Machine.Labels
import Machine.Bytes
import Prysm.BeaconBlockHeader.Code

/-!
# Prysm `(*v1alpha1.BeaconBlockHeader).UnmarshalSSZ`: the error wraps after the callees

Hand-written. The `fmt.errorf` wraps after the Slot call (directives 20–45) and the ValidatorIndex call (58–84) are not
reached on a 112-byte input: `Decode.generated_accept` passes from directive 19 to 46 and from 57 to 85 under
`Prysm.Slot.Decode.accept_function_spec` / `Prysm.ValidatorIndex.Decode.accept_function_spec` (rax = 0).

**Unreachable error paths**:
`Decode.slot_err_unreachable` (directive 18 → 46, skips 20–45, "Slot: %w") and
`Decode.validator_index_err_unreachable` (56 → 85, skips 58–84, "ValidatorIndex: %w"): with `rax = 0` after the callee
the code jumps over the wrap with registers and memory unchanged.
-/

open Machine Prysm.BeaconBlockHeader.Code
variable [Host]

namespace Prysm.BeaconBlockHeader

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- **Unreachable: the `fmt.errorf("Slot: %w")` path** (directives 20–45). -/
theorem Decode.slot_err_unreachable (k : Nat) (hk : unmarshalSSZ.IsInfixAt Host.prog k)
    (hf : LabelsFresh unmarshalSSZ k) (s : MachineData) (h0 : s.regs.rax = 0) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 46) ∧ st.data.regs = s.regs ∧ st.data.dmem = s.dmem)
      ⟨s, Host.addrOf (k + 18)⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h0 ⊢
  subst h0
  step_directive hk unmarshalSSZ 18
  intro _
  step_directive hk unmarshalSSZ 19
  split
  case isFalse h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
  simp only [Effects.All]
  label_address hk hf unmarshalSSZ 46
  exact Eventually.done _ ⟨rfl, rfl, rfl⟩

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- **Unreachable: the `fmt.errorf("ValidatorIndex: %w")` path** (directives 58–84). -/
theorem Decode.validator_index_err_unreachable (k : Nat) (hk : unmarshalSSZ.IsInfixAt Host.prog k)
    (hf : LabelsFresh unmarshalSSZ k) (s : MachineData) (h0 : s.regs.rax = 0) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 85) ∧ st.data.regs = s.regs ∧ st.data.dmem = s.dmem)
      ⟨s, Host.addrOf (k + 56)⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h0 ⊢
  subst h0
  step_directive hk unmarshalSSZ 56
  intro _
  step_directive hk unmarshalSSZ 57
  split
  case isFalse h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
  simp only [Effects.All]
  label_address hk hf unmarshalSSZ 85
  exact Eventually.done _ ⟨rfl, rfl, rfl⟩

end Prysm.BeaconBlockHeader
