import Fk
import Fk.RtErr
import Fk.WHost

open Fk Fk.Code Fk.W
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace Review1bFix
-- A shared Host for seven contract definitions, including both errorf cases.
def P : Program := [.label "runtime.fvBump"] ++ BumpAlloc1 ++ RtCopy ++ BumpNew32 ++ RtErr
local instance : Host := mkHost P (by decide)

theorem hkM : BumpAlloc1.IsInfixAt Host.prog 1 := by
  exact ⟨RtCopy ++ BumpNew32 ++ RtErr, by rfl⟩
theorem hkC : RtCopy.IsInfixAt Host.prog 7 := by
  exact ⟨BumpNew32 ++ RtErr, by rfl⟩
theorem hkN : BumpNew32.IsInfixAt Host.prog 33 := by
  exact ⟨RtErr, by rfl⟩
theorem hkE : RtErr.IsInfixAt Host.prog 39 := by
  exact ⟨[], by rfl⟩
theorem hfM : ∀ i < 1, Host.prog[i]? ≠ some (.label "runtime.makeslice") := by
  intro i hi
  have hz : i = 0 := by omega
  subst i
  decide
theorem hfC : LabelsFresh RtCopy 7 := labelsFresh_of (by decide)
theorem hfE : LabelsFresh RtErr 39 := labelsFresh_of (by decide)
theorem hfN : ∀ i < 33, Host.prog[i]? ≠ some (.label "runtime.newobject") := by
  have hf : LabelsFresh BumpNew32 33 := labelsFresh_of (by decide)
  have hnot : "runtime.newobject" ∉ labs (P.take 33) := by decide
  intro i hi hp
  apply hnot; apply mem_labs; rw [List.mem_iff_getElem?]
  exact ⟨i, by rw [List.getElem?_take, if_pos hi]; exact hp⟩

-- Budget and scalar premises for ListU64's prefix-3 append of four bytes.
example : nextSliceCap 7 3 = 7 := by decide
example : 3 ≤ 3 ∧ 3 < 3 + 4 ∧ 2 * nextSliceCap 7 3 + 8192 ≤ 12576 ∧ 12576 ≤ maxAlloc := by decide
-- This does not construct the full lum_grow_site state or its Host.

-- Old 2^63 input is excluded. This alone is not a satisfiability proof.
example (esz oc avail : Nat) (he : 0 < esz) :
    ¬ (2 * (esz * nextSliceCap (2^63) oc) + 8192 ≤ avail ∧ avail ≤ maxAlloc) :=
  Fk.Witness.review1b_input_excluded esz oc avail he

-- funspec's pre-call stack pointer is decreased by eight before body execution.
example (sp : BitVec 64) : sp - 8 + 16 = sp + 8 := by bv_omega
example : (0x1000#64 - 8 + 16) ≠ (0x1000#64 + 16) := by decide

end Review1bFix
