/-
Claude re-check of the re-proof fix session (2026-11-06).
Goal: (1) the strengthened contracts are jointly satisfiable (regression theorem still closes, and the
new error-path premises are consistent with the semtest cases); (2) the composition theorem's arithmetic
premises are satisfiable; (3) the axioms of the new declarations are standard.
Run: cd fv/kraken/lean && lake env lean <this file>
-/
import Fk.Regress
import Fk.Compose
import Fk.WitLcA1
import Fk.WitBlR
import Fk.WitVbvR
import Fk.WitLuG
open Fk Fv1 EthLib.Serialization.Ssz

#print Fk.Regress.Joint

-- 2. The invalid-input contract's premise `¬ blValid buf` is met by the semtest reject cases
--    and refuted by the accept cases (same rule as `f12_test.go`).
example : ¬ blValid [] := by rw [blValid, blValid_iff]; unfold blArith; decide
example : ¬ blValid [0] := by rw [blValid, blValid_iff]; unfold blArith; decide
example : blValid [1] := by rw [blValid, blValid_iff]; unfold blArith; decide
theorem rep_last (n : Nat) (x : UInt8) : (List.replicate n (0 : UInt8) ++ [x]).getLastD 0 = x := by simp
theorem rep_len (n : Nat) (x : UInt8) : (List.replicate n (0 : UInt8) ++ [x]).length = n + 1 := by simp
example : ¬ blValid (List.replicate 256 0 ++ [2]) := by   -- 2049 bits (semtest case)
  rw [blValid, blValid_iff]; unfold blArith; simp only [rep_last, rep_len]; decide
example : ¬ blValid (List.replicate 257 0 ++ [1]) := by   -- 258 bytes (F2 input)
  rw [blValid, blValid_iff]; unfold blArith; simp only [rep_last, rep_len]; decide

-- 3. `ValidateBitlistErrC`: the budget inequalities admit the model's consumption (16 bytes, empty message).
example : ∃ avail avail' msg : Nat, 8192 ≤ avail ∧ msg ≤ 128 ∧ avail' + 16 + msg ≤ avail ∧ avail ≤ avail' + 8192 :=
  ⟨8192, 8176, 0, by omega, by omega, by omega, by omega⟩

-- 4. `lu_unmarshal_then_marshal`: the arithmetic premises are satisfiable (n = 1, dlen = 0, cap = 12).
example : ∃ n dlen cap rcx rdi avail : Nat, n ≤ 16 ∧ dlen + 4 + 8 * n ≤ cap ∧ cap < 2 ^ 63
    ∧ rcx = 4 + 8 * n ∧ rcx ≤ rdi ∧ rdi < 2 ^ 63 ∧ 8 * n ≤ avail :=
  ⟨1, 0, 12, 12, 12, 8, by omega, by omega, by decide, rfl, by omega, by decide, by omega⟩

-- 5. The new witnesses apply the main theorems; axioms are standard.
#check @Fk.WitLcA1.lc_accept_runs
#check @Fk.WitBlR.bl_marshal_reject_runs
#check @Fk.WitVbvR.vbv_reject_pad_runs
#check @Fk.WitLuG.lum_grow_runs
#print axioms lu_unmarshal_then_marshal
#print axioms Fk.Regress.joint_models
#print axioms Fk.WitLcA1.lc_accept_runs
#print axioms Fk.WitBlR.bl_marshal_reject_runs
#print axioms Fk.WitVbvR.vbv_reject_pad_runs
#print axioms Fk.WitLuG.lum_grow_runs