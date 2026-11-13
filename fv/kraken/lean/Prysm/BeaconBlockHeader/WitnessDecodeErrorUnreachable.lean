import Prysm.BeaconBlockHeader.WitnessDecodeRejectSize

/-!
# Witness of the two `unreachable_mc` theorems of the BeaconBlockHeader decoder

Host and state of `Prysm.BeaconBlockHeader.WitnessDecodeRejectSize` (label `ssz.ErrSize` at index 0, the real Go 1.26.10
`(*v1alpha1.BeaconBlockHeader).UnmarshalSSZ` at index 1). The premises are code placement, label
freshness and `rax = 0`. `initial_state 112 …` with `rax` replaced by 0 satisfies all of them.
The run starts at directive 18 or 56 (after the callee's return), not at the function entry.
-/

open Machine Runtime

namespace Prysm.BeaconBlockHeader.Witness.DecodeErrorUnreachable

/-- The `Prysm/BeaconBlockHeader/WitnessDecodeRejectSize.lean` state with a nil callee error (`rax = 0`). -/
def start_state (zmms : RegZmms) (flags : StatusFlags) : MachineData :=
  ⟨⟨0, 0x10200, 112, 0, 0, 0, 0x10020, 0, 0, 0, 0, 0, 0, 0, 0x10000, 0⟩, zmms, flags, DecodeRejectSize.mem⟩

/-- **Non-vacuity of `Decode.slot_err_unreachable` and `Decode.validator_index_err_unreachable`.** -/
theorem runs (zmms : RegZmms) (flags : StatusFlags) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (1 + 46) ∧ st.data.regs = (start_state zmms flags).regs
        ∧ st.data.dmem = (start_state zmms flags).dmem) ⟨start_state zmms flags, Host.addrOf (1 + 18)⟩ ∧
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (1 + 85) ∧ st.data.regs = (start_state zmms flags).regs
        ∧ st.data.dmem = (start_state zmms flags).dmem) ⟨start_state zmms flags, Host.addrOf (1 + 56)⟩ :=
  ⟨Decode.slot_err_unreachable 1 DecodeRejectSize.placed_at_1 DecodeRejectSize.labels_fresh_at_1 (start_state zmms flags) rfl,
   Decode.validator_index_err_unreachable 1 DecodeRejectSize.placed_at_1 DecodeRejectSize.labels_fresh_at_1 (start_state zmms flags) rfl⟩

end Prysm.BeaconBlockHeader.Witness.DecodeErrorUnreachable
