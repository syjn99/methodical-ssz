import Machine.Step

/-!
# Label resolution in a `Host`

Kraken resolves `label l` to the address of the *first* `.label l` directive of
the laid-out host program (`Executable.labels`, `findSome?`), or `-1`.
`label_eq_addrOf` turns that into `Host.addrOf j` for the first occurrence `j`.
-/

namespace Machine

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

/-- No label of fragment `p` occurs in the host program before index `k`
(a link-level fact: assembly labels are unique). -/
def LabelsFresh (p : Program) (k : Nat) : Prop :=
  ∀ i < k, ∀ l, Host.prog[i]? = some (Kraken.Directive.label l) → Kraken.Directive.label l ∉ p

theorem label_at {p : Program} {k : Nat} (hk : p.IsInfixAt Host.prog k) (hf : LabelsFresh p k)
    {j : Nat} {l : Label} (hj : p[j]? = some (.label l)) (hin : ∀ i < j, p[i]? ≠ some (.label l)) :
    label l = Host.addrOf (k + j) :=
  label_in_fragment hk hj hin (fun i hi h => hf i hi l h (List.mem_of_getElem? hj))

/-- `label_at` with the "first in the fragment" side condition as a list check. -/
theorem label_at' {p : Program} {k : Nat} (hk : p.IsInfixAt Host.prog k) (hf : LabelsFresh p k)
    {j : Nat} {l : Label} (hj : p[j]? = some (.label l))
    (hin : @List.contains _ instBEqOfDecidableEq (p.take j) (Kraken.Directive.label l) = false) :
    label l = Host.addrOf (k + j) := by
  refine label_at hk hf hj (fun i hi h => ?_)
  have hmem : Kraken.Directive.label l ∈ p.take j := by
    have hlt : i < p.length := by
      rcases Nat.lt_or_ge i p.length with h' | h'
      · exact h'
      · simp [List.getElem?_eq_none h'] at h
    rw [List.mem_iff_getElem?]
    exact ⟨i, by rw [List.getElem?_take_of_lt hi, h]⟩
  have := @List.contains_iff_mem _ instBEqOfDecidableEq _ _ _ |>.mpr hmem
  rw [hin] at this; exact absurd this (by decide)

end Machine

/-- Rewrite `label l` (the label at directive `j` of fragment `prog`) to `Host.addrOf (k + j)`.
Side conditions are computed by `simp` (not `decide`/`rfl`, whose proof terms
exceed the recursion limit for long fragments). -/
macro "klabel " hk:term:max hf:term:max prog:ident j:num : tactic => `(tactic| (
  have hkl := Machine.label_at' $hk $hf (j := $j)
    (by simp only [$prog:ident, List.getElem?_cons_succ, List.getElem?_cons_zero]; rfl)
    (by simp only [$prog:ident, List.take_succ_cons, List.take_zero, List.contains_cons, List.contains_nil]; decide)
  rw [hkl]; clear hkl))
