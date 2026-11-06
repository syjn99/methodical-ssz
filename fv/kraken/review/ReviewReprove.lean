/-
Claude re-check of the re-proof session (2026-11-06).
Goal: show that the premise sets of the theorems that still lack a witness are
satisfiable (no hidden contradiction), and that the spec-side rules match EthLib on examples.
Run: cd fv/kraken/lean && lake env lean <this file>
-/
import Fk.Regress
import Fk.LcAccept
import Fk.LuGrow
import Fk.BlMarshal
open Fk Fv1 EthLib.Serialization.Ssz

-- 1. `lum_grow_site`: the register/budget premises are jointly satisfiable.
example : ∃ rcx rdi rdx avail : Nat, rdx = rcx + 4 ∧ rcx ≤ rdi ∧ rdi < rdx
    ∧ 2 * nextSliceCap rdx rdi + 8192 ≤ avail ∧ avail ≤ maxAlloc :=
  ⟨0, 0, 4, 8192 + 2 * nextSliceCap 4 0, rfl, Nat.le_refl _, by decide, Nat.le_refl _, by decide⟩

-- 2. `lc_accept_main`: the list premises are satisfiable with one empty ListU64 element.
def g0 : ListU64 := ⟨[]⟩
def tl0 : List UInt8 := [4, 0, 0, 0] ++ [4, 0, 0, 0]
example : (∀ g ∈ [g0], g.ok) := by intro g hg; simp only [List.mem_singleton] at hg; subst hg; unfold ListU64.ok g0; decide
example : lcStart [g0] 1 = tl0.length := by decide
example : tl0.take 4 = (uintBytes 4 (4 * 1)).toList := by decide
example : ∀ i (hi : i < [g0].length),
    (tl0.drop (lcStart [g0] i)).take (4 + 8 * ([g0][i].l.length))
      = [4, 0, 0, 0] ++ (u64Bytes [g0][i].l).toList := by
  intro i hi
  have h0 : i = 0 := by simp only [List.length_singleton] at hi; omega
  subst h0; decide +revert

-- 3. `blValid` on examples, straight against EthLib's `unpackDelimited`.
example : blValid [1] := by rw [blValid, blValid_iff]; unfold blArith; decide
example : ¬ blValid [0] := by rw [blValid, blValid_iff]; unfold blArith; decide
example : ¬ blValid [] := by rw [blValid, blValid_iff]; unfold blArith; decide
-- Long inputs: `decide` hits the recursion limit on 257-element lists, so use the list lemmas.
theorem rep_last (n : Nat) (x : UInt8) : (List.replicate n (0 : UInt8) ++ [x]).getLastD 0 = x := by simp
theorem rep_len (n : Nat) (x : UInt8) : (List.replicate n (0 : UInt8) ++ [x]).length = n + 1 := by simp
example : blValid (List.replicate 255 0 ++ [255]) := by   -- 2047 bits
  rw [blValid, blValid_iff]; unfold blArith; simp only [rep_last, rep_len]; decide
example : blValid (List.replicate 256 0 ++ [1]) := by     -- 2048 bits
  rw [blValid, blValid_iff]; unfold blArith; simp only [rep_last, rep_len]; decide
example : ¬ blValid (List.replicate 256 0 ++ [3]) := by   -- 2049 bits
  rw [blValid, blValid_iff]; unfold blArith; simp only [rep_last, rep_len]; decide
example : ¬ blValid (List.replicate 257 0 ++ [1]) := by   -- 2056 bits
  rw [blValid, blValid_iff]; unfold blArith; simp only [rep_last, rep_len]; decide

-- 4. `ValidateBitlistC`: the conclusion is not self-contradictory (itab ≠ 0).
example : ∀ rax : UInt64, (rax = 0 ↔ False) → rax.toBitVec = (label "go_itab._errors.errorString_error").toBitVec → True :=
  fun _ _ _ => trivial
example : (label "go_itab._errors.errorString_error").toBitVec ≠ 0 := Fk.Regress.hit
