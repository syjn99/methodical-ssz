module

public import Machine.Step
public import Machine.Labels
public import Machine.Bytes
public import Prysm.SingleAttestation.Code

@[expose] public section

/-!
# Prysm `(*v1alpha1.SingleAttestation).UnmarshalSSZ`: the error wraps after the callees

Hand-written, in the form of `Prysm/BeaconBlockHeader/DecodeErrorUnreachable.lean`.
The three `fmt.errorf` wraps after the callees are not reached on a 240-byte input: `Decode.accept` passes from
directive 19 to 47, from 57 to 85 and from 108 to 136 under `Prysm.CommitteeIndex.Decode.accept_function_spec`,
`Prysm.ValidatorIndex.Decode.accept_function_spec` and `Prysm.AttestationData.Decode.accept` (rax = 0).

**Unreachable error paths** (conditional skips, `FINDINGS.md`, entry "Unreachable error wraps hold only with the callee
specifications"):
`Decode.committee_id_err_unreachable` (directive 18 → 47, skips 20–46, "CommitteeId: %w"),
`Decode.attester_index_err_unreachable` (56 → 85, skips 58–84, "AttesterIndex: %w") and
`Decode.data_err_unreachable` (107 → 136, skips 109–135, "Data: %w"): with `rax = 0` after the callee the code jumps over
the wrap with registers and memory unchanged.
-/

open Machine Prysm.SingleAttestation.Code
variable [Host]

namespace Prysm.SingleAttestation

/-- **Unreachable: the `fmt.errorf("CommitteeId: %w")` path** (directives 20–46). -/
theorem Decode.committee_id_err_unreachable (k : Nat) (hk : unmarshalSSZ.IsInfixAt Host.prog k)
    (hf : LabelsFresh unmarshalSSZ k) (s : MachineData) (h0 : s.regs.rax = 0) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 47) ∧ st.data.regs = s.regs ∧ st.data.dmem = s.dmem)
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
  label_address hk hf unmarshalSSZ 47
  exact Eventually.done _ ⟨rfl, rfl, rfl⟩

/-- **Unreachable: the `fmt.errorf("AttesterIndex: %w")` path** (directives 58–84). -/
theorem Decode.attester_index_err_unreachable (k : Nat) (hk : unmarshalSSZ.IsInfixAt Host.prog k)
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

/-- **Unreachable: the `fmt.errorf("Data: %w")` path** (directives 109–135). -/
theorem Decode.data_err_unreachable (k : Nat) (hk : unmarshalSSZ.IsInfixAt Host.prog k)
    (hf : LabelsFresh unmarshalSSZ k) (s : MachineData) (h0 : s.regs.rax = 0) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 136) ∧ st.data.regs = s.regs ∧ st.data.dmem = s.dmem)
      ⟨s, Host.addrOf (k + 107)⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h0 ⊢
  subst h0
  step_directive hk unmarshalSSZ 107
  intro _
  step_directive hk unmarshalSSZ 108
  split
  case isFalse h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
  simp only [Effects.All]
  label_address hk hf unmarshalSSZ 136
  exact Eventually.done _ ⟨rfl, rfl, rfl⟩

end Prysm.SingleAttestation
