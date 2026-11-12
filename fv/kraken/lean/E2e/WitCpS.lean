import E2e.CpSpecM
import Fk.WHost

/-! # Witness of `cp_e2e_size_main`: the real SizeSSZ code alone; memory = the return slot. -/

open Fk Fk.W E2e E2e.Code

namespace E2e.WitCpS

instance host : Host := mkHost CpSize (by decide)

theorem hk0 : CpSize.IsInfixAt Host.prog 0 := ⟨[], by simp [Host.prog, mkHost]⟩

def cs0 (zmms : RegZmms) (flags : StatusFlags) : MachineData :=
  ⟨⟨0, 0, 0, 0, 0, 0, 0x10000, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, zmms, flags,
    (Int.toBytes 8 (0 : UInt64).toBitVec.toInt).At (0x10000 : BitVec 64)⟩

/-- **Non-vacuity of `cp_e2e_size_main`** (frame `R` = emp). -/
theorem cps_runs (zmms : RegZmms) (flags : StatusFlags) :
    Eventually (step1 Host.exe) (fun st => st.pc = Int64.ofBitVec (0 : UInt64).toBitVec ∧ st.data.regs.rax = 40)
      ⟨cs0 zmms flags, Host.addrOf 0⟩ :=
  eventually_mono (cp_e2e_size_main 0 hk0 (cs0 zmms flags) 0 Std.ExtHashMap.emp
    (by simp only [cs0, Std.ExtHashMap.sep_emp]; rfl)) (fun _ h => ⟨h.1, h.2.1⟩)

end E2e.WitCpS
