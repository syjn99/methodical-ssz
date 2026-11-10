import E2eScal.WitBhR

/-!
# Witness of the two `unreachable_mc` theorems of the BeaconBlockHeader decoder (session 10)

Host and state of `E2eScal.WitBhR` (label `ssz.ErrSize` at index 0, the real Go 1.26.10
`(*v1alpha1.BeaconBlockHeader).UnmarshalSSZ` at index 1). The premises are code placement, label
freshness and `rax = 0`. `cs0 112 …` with `rax` replaced by 0 satisfies all of them.
The run starts at directive 18 or 56 (after the callee's return), not at the function entry.
-/

open Fk E2eScal.Bh E2eScal.WitBhR

namespace E2eScal.WitBhU

/-- The `WitBhR` state with a nil callee error (`rax = 0`). -/
def s0 (zmms : RegZmms) (flags : StatusFlags) : MachineData :=
  ⟨⟨0, 0x10200, 112, 0, 0, 0, 0x10020, 0, 0, 0, 0, 0, 0, 0, 0x10000, 0⟩, zmms, flags, mem⟩

/-- **Non-vacuity of `bh_e2e_slot_err_unreachable` and `bh_e2e_vi_err_unreachable`.** -/
theorem bh_unreach_runs (zmms : RegZmms) (flags : StatusFlags) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (1 + 46) ∧ st.data.regs = (s0 zmms flags).regs
        ∧ st.data.dmem = (s0 zmms flags).dmem) ⟨s0 zmms flags, Host.addrOf (1 + 18)⟩ ∧
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (1 + 85) ∧ st.data.regs = (s0 zmms flags).regs
        ∧ st.data.dmem = (s0 zmms flags).dmem) ⟨s0 zmms flags, Host.addrOf (1 + 56)⟩ :=
  ⟨bh_e2e_slot_err_unreachable 1 hk1 hf1 (s0 zmms flags) rfl,
   bh_e2e_vi_err_unreachable 1 hk1 hf1 (s0 zmms flags) rfl⟩

end E2eScal.WitBhU
