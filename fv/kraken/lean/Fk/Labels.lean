import Fk.Step

/-!
# Label resolution in a `Host`

Kraken resolves `label l` to the address of the *first* `.label l` directive of
the laid-out host program (`Executable.labels`, `findSome?`), or `-1`.
`label_eq_addrOf` turns that into `Host.addrOf j` for the first occurrence `j`.
`label_in_fragment` states it for a label inside our function at index `k`,
given that the label does not occur in the host program before the function.
-/

namespace Fk

theorem findSome?_eq_of_first {α β : Type} (f : α → Option β) :
    ∀ (L : List α) (j : Nat) (x : α) (v : β), L[j]? = some x → f x = some v →
      (∀ i < j, ∀ y, L[i]? = some y → f y = none) → L.findSome? f = some v
  | [], j, x, v, hj, _, _ => by simp at hj
  | a :: L, 0, x, v, hj, hf, _ => by
    simp at hj; subst hj; simp [List.findSome?, hf]
  | a :: L, j + 1, x, v, hj, hf, hpre => by
    have ha : f a = none := hpre 0 (by omega) a rfl
    simp only [List.findSome?, ha]
    exact findSome?_eq_of_first f L j x v (by simpa using hj) hf
      (fun i hi y hy => hpre (i + 1) (by omega) y (by simpa using hy))

variable [Host]

theorem label_eq_addrOf {l : Label} {j : Nat} (hj : Host.prog[j]? = some (.label l))
    (hfirst : ∀ i < j, Host.prog[i]? ≠ some (.label l)) : label l = Host.addrOf j := by
  show (Executable.labels Host.exe).label l = Host.addrOf j
  unfold Executable.labels
  dsimp only
  rw [findSome?_eq_of_first _ _ j _ (Host.addrOf j)
    (by rw [Kraken.Executable.getElem?_withAddresses_eq, Host.exe_getElem?, hj]; rfl) (by simp; rfl)]
  · rfl
  · intro i hi y hy
    rw [Kraken.Executable.getElem?_withAddresses_eq, Host.exe_getElem?] at hy
    cases hp : Host.prog[i]? with
    | none => simp [hp] at hy
    | some d =>
      simp only [hp, Option.map_some, Option.some.injEq] at hy
      subst hy
      have := hfirst i hi
      rw [hp] at this
      simp only [ne_eq, Option.some.injEq] at this
      simp [this]

/-- A label inside a fragment at index `k`, at offset `j`, with no earlier occurrence
in the fragment or in the host program before `k`. -/
theorem label_in_fragment {p : Program} {k j : Nat} {l : Label} (hk : p.IsInfixAt Host.prog k)
    (hj : p[j]? = some (.label l)) (hin : ∀ i < j, p[i]? ≠ some (.label l))
    (hpre : ∀ i < k, Host.prog[i]? ≠ some (.label l)) : label l = Host.addrOf (k + j) := by
  have hjlt : j < p.length := by
    rcases Nat.lt_or_ge j p.length with h | h
    · exact h
    · simp [List.getElem?_eq_none h] at hj
  have hk' := List.isInfixAt_iff_getElem?.mp hk
  apply label_eq_addrOf
  · rw [hk' j hjlt]; simpa [List.getElem?_eq_getElem hjlt] using hj
  · intro i hi
    rcases Nat.lt_or_ge i k with h | h
    · exact hpre i h
    · have := hk' (i - k) (by omega)
      rw [show k + (i - k) = i by omega] at this
      rw [this]
      have := hin (i - k) (by omega)
      rwa [List.getElem?_eq_getElem (by omega)] at this

end Fk
