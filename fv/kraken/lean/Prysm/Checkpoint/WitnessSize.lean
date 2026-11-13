import Prysm.Checkpoint.EncodeSpec
import Machine.WitnessHost

/-! # Witness of `Size.result`: the real SizeSSZ code alone; memory = the return slot. -/

open Machine Runtime Machine.Witness Prysm.Checkpoint.Code

namespace Prysm.Checkpoint.Witness.Size

instance host : Host := mkHost sizeSSZ (by decide)

theorem placed_at_0 : sizeSSZ.IsInfixAt Host.prog 0 := ⟨[], by simp [Host.prog, mkHost]⟩

def initial_state (zmms : RegZmms) (flags : StatusFlags) : MachineData :=
  ⟨⟨0, 0, 0, 0, 0, 0, 0x10000, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, zmms, flags,
    (Int.toBytes 8 (0 : UInt64).toBitVec.toInt).At (0x10000 : BitVec 64)⟩

/-- **Non-vacuity of `Size.result`** (frame `R` = emp). -/
theorem runs (zmms : RegZmms) (flags : StatusFlags) :
    Eventually (step1 Host.exe) (fun st => st.pc = Int64.ofBitVec (0 : UInt64).toBitVec ∧ st.data.regs.rax = 40)
      ⟨initial_state zmms flags, Host.addrOf 0⟩ :=
  eventually_mono (Size.result 0 placed_at_0 (initial_state zmms flags) 0 Std.ExtHashMap.emp
    (by simp only [initial_state, Std.ExtHashMap.sep_emp]; rfl)) (fun _ h => ⟨h.1, h.2.1⟩)

end Prysm.Checkpoint.Witness.Size
