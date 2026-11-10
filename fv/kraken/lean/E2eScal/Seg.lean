import Fk.Step
import Fk.Labels
import Fk.Bytes

/-!
# Scalability stage S1: shared glue of the parameterized segment lemmas

A segment lemma of `E2eScal` is stated for a *code template*: a Lean function from the
parameters (labels, frame size, stack-slot and field displacements) to a list of
directives. The lemma takes the template's place in the host program as a hypothesis
`(tmpl params).IsInfixAt Host.prog j` (and, for a jump target, `label l = Host.addrOf j'`).
An instance discharges these hypotheses from the included `.S` (`infix_sub` below and
`Fk.label_at'`): the check is a computation on the directive lists, so a wrong template
or a wrong parameter only makes the instance fail.

Nothing here is trusted beyond `Fk.Step` / `Fk.Labels`.
-/

namespace E2eScal

/-- A part `q` of fragment `p` (from directive `a`, `q.length` directives) is at
index `k + a` of the list in which `p` is at index `k`. -/
theorem infix_sub {α : Type} {p l q : List α} {k : Nat} (a : Nat) (h : p.IsInfixAt l k)
    (hq : (p.drop a).take q.length = q) : q.IsInfixAt l (k + a) := by
  rw [List.isInfixAt_iff_getElem?] at *
  intro i hi
  have hlen : q.length ≤ p.length - a := by
    have := congrArg List.length hq
    simp only [List.length_take, List.length_drop] at this
    omega
  have := h (a + i) (by omega)
  rw [Nat.add_assoc, this]
  congr 1
  have h2 : q[i] = ((p.drop a).take q.length)[i]'(by simp; omega) := by
    simp only [hq]
  rw [h2, List.getElem_take, List.getElem_drop]

end E2eScal

-- A template is stepped with `kat hA tmpl n` (`Fk/Step.lean`): its `simp only [tmpl, ...]`
-- unfolds the template application by its equation lemma.
