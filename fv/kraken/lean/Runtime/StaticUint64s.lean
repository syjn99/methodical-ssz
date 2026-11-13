import Kraken.X64.WP
import Machine.Include

/-!
# The table `runtime.staticuint64s` of the Go runtime

`data_include staticuint64s` (`Machine/Include.lean`) reads `link/out/data/staticuint64s.data`.
`link/data.py` writes that file from the ELF, and `link/check.py` compares it with the ELF.
The address is the label `runtime.staticuint64s` of the `Host` program, so the definition holds for every Go ELF.
The contract form `StaticBox` (`Runtime/Contracts.lean`) reads the table.
-/

namespace Runtime.Data

data_include staticuint64s

/-- `runtime.staticuint64s` is the table of the uint64 values 0..255. Checked by
the kernel (`decide +kernel`: no `Lean.ofReduceBool`, unlike `native_decide`). -/
theorem _root_.Runtime.Data.staticuint64s_table : Runtime.Data.staticuint64s = (List.range 256).flatMap (fun i : Nat => Int.toBytes 8 (i : Int)) := by
  decide +kernel

end Runtime.Data
