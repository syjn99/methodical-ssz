module

public import Prysm.SingleAttestation.WitnessDecodeRejectSize
public import Prysm.SingleAttestation.DecodeErrorUnreachable

@[expose] public section

/-!
# Witness of the three unreachable-path theorems of the SingleAttestation decoder

Host and state of `Prysm.SingleAttestation.Witness.DecodeRejectSize` (label `ssz.ErrSize` at index 0, the Go 1.26.10
`(*v1alpha1.SingleAttestation).UnmarshalSSZ` at index 1). The premises are code placement, label
freshness and `rax = 0`. `initial_state 240 …` with `rax` replaced by 0 satisfies all of them.
The run starts at directive 18, 56 or 107 (after the callee's return), not at the function entry.
-/

open Machine Runtime

namespace Prysm.SingleAttestation.Witness.DecodeErrorUnreachable

/-- The `Prysm/SingleAttestation/WitnessDecodeRejectSize.lean` state with a nil callee error (`rax = 0`). -/
def start_state (zmms : RegZmms) (flags : StatusFlags) : MachineData :=
  ⟨⟨0, 0x10200, 240, 0, 0, 0, 0x10020, 0, 0, 0, 0, 0, 0, 0, 0x10000, 0⟩, zmms, flags, DecodeRejectSize.mem⟩

/-- **Non-vacuity of `Decode.committee_id_err_unreachable`, `Decode.attester_index_err_unreachable` and
`Decode.data_err_unreachable`.** -/
theorem runs (zmms : RegZmms) (flags : StatusFlags) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (1 + 47) ∧ st.data.regs = (start_state zmms flags).regs
        ∧ st.data.dmem = (start_state zmms flags).dmem) ⟨start_state zmms flags, Host.addrOf (1 + 18)⟩ ∧
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (1 + 85) ∧ st.data.regs = (start_state zmms flags).regs
        ∧ st.data.dmem = (start_state zmms flags).dmem) ⟨start_state zmms flags, Host.addrOf (1 + 56)⟩ ∧
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (1 + 136) ∧ st.data.regs = (start_state zmms flags).regs
        ∧ st.data.dmem = (start_state zmms flags).dmem) ⟨start_state zmms flags, Host.addrOf (1 + 107)⟩ :=
  ⟨Decode.committee_id_err_unreachable 1 DecodeRejectSize.placed_at_1 DecodeRejectSize.labels_fresh_at_1 (start_state zmms flags) rfl,
   Decode.attester_index_err_unreachable 1 DecodeRejectSize.placed_at_1 DecodeRejectSize.labels_fresh_at_1 (start_state zmms flags) rfl,
   Decode.data_err_unreachable 1 DecodeRejectSize.placed_at_1 DecodeRejectSize.labels_fresh_at_1 (start_state zmms flags) rfl⟩

end Prysm.SingleAttestation.Witness.DecodeErrorUnreachable
