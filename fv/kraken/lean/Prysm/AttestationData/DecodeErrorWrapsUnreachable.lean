import Machine.Step
import Machine.Labels
import Machine.Bytes
import Prysm.AttestationData.Code
import Prysm.ElfData.PrysmTarget
import Prysm.Checkpoint.DecodeRejectSize
import Prysm.AttestationData.DecodeRejectSize

/-!
# Real Prysm `(*v1alpha1.AttestationData).UnmarshalSSZ`: the four error wraps that no 128-byte input reaches

**`unreachable_mc` rows** (own column, never reject coverage): after each callee returns with `rax = 0` the code jumps
over its `fmt.errorf` wrap with registers and memory unchanged. The callee function specifications give `rax = 0` for the
calls that `Decode.accept` makes with `len(buf) = 128`. The size reject is in `Prysm/AttestationData/DecodeRejectSize.lean`.
-/

open Machine Prysm.AttestationData.Code
variable [Host]

namespace Prysm.AttestationData

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- **`unreachable_mc`: the `fmt.errorf("Slot: %w")` path** (directives 20–46). -/
theorem Decode.slot_err_unreachable (k : Nat) (hk : unmarshalSSZ.IsInfixAt Host.prog k)
    (hf : LabelsFresh unmarshalSSZ k) (s : MachineData) (h0 : s.regs.rax = 0) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 47) ∧ st.data.regs = s.regs ∧ st.data.dmem = s.dmem)
      ⟨s, Host.addrOf (k + 18)⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h0 ⊢
  subst h0
  kat hk unmarshalSSZ 18
  intro _
  kat hk unmarshalSSZ 19
  split
  case isFalse h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
  simp only [Effects.All]
  klabel hk hf unmarshalSSZ 47
  exact Eventually.done _ ⟨rfl, rfl, rfl⟩

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- **`unreachable_mc`: the `fmt.errorf("CommitteeIndex: %w")` path** (directives 58–84). -/
theorem Decode.committee_index_err_unreachable (k : Nat) (hk : unmarshalSSZ.IsInfixAt Host.prog k)
    (hf : LabelsFresh unmarshalSSZ k) (s : MachineData) (h0 : s.regs.rax = 0) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 85) ∧ st.data.regs = s.regs ∧ st.data.dmem = s.dmem)
      ⟨s, Host.addrOf (k + 56)⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h0 ⊢
  subst h0
  kat hk unmarshalSSZ 56
  intro _
  kat hk unmarshalSSZ 57
  split
  case isFalse h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
  simp only [Effects.All]
  klabel hk hf unmarshalSSZ 85
  exact Eventually.done _ ⟨rfl, rfl, rfl⟩

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- **`unreachable_mc`: the `fmt.errorf("Source: %w")` path** (directives 145–171). -/
theorem Decode.source_err_unreachable (k : Nat) (hk : unmarshalSSZ.IsInfixAt Host.prog k)
    (hf : LabelsFresh unmarshalSSZ k) (s : MachineData) (h0 : s.regs.rax = 0) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 172) ∧ st.data.regs = s.regs ∧ st.data.dmem = s.dmem)
      ⟨s, Host.addrOf (k + 143)⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h0 ⊢
  subst h0
  kat hk unmarshalSSZ 143
  intro _
  kat hk unmarshalSSZ 144
  split
  case isFalse h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
  simp only [Effects.All]
  klabel hk hf unmarshalSSZ 172
  exact Eventually.done _ ⟨rfl, rfl, rfl⟩

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- **`unreachable_mc`: the `fmt.errorf("Target: %w")` path** (directives 195–221). -/
theorem Decode.target_err_unreachable (k : Nat) (hk : unmarshalSSZ.IsInfixAt Host.prog k)
    (hf : LabelsFresh unmarshalSSZ k) (s : MachineData) (h0 : s.regs.rax = 0) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 222) ∧ st.data.regs = s.regs ∧ st.data.dmem = s.dmem)
      ⟨s, Host.addrOf (k + 193)⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h0 ⊢
  subst h0
  kat hk unmarshalSSZ 193
  intro _
  kat hk unmarshalSSZ 194
  split
  case isFalse h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
  simp only [Effects.All]
  klabel hk hf unmarshalSSZ 222
  exact Eventually.done _ ⟨rfl, rfl, rfl⟩

end Prysm.AttestationData
