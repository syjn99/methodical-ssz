import Fk.Labels
import Fk.Bytes

/-!
# Witness hosts (1b-fix X4)

`mkHost P`: a `Host` whose program is `P` and whose directive `i` sits at
address `0x10000 + i` (every directive has size 1). Witness files build one
host per main theorem: data labels first, then the target function, then the
runtime models. `labelsFresh_of` turns a Boolean label check into
`LabelsFresh`; `mk_label` resolves a label to its address.
-/

open Fk

namespace Fk.W

theorem sizeBefore_one (P : Program) (j : Nat) :
    ((Kraken.Layout.apply ⟨0x10000, fun _ => 1⟩ P).program.take j |>.map (·.size)).sum = min j P.length := by
  simp only [Kraken.Layout.apply]
  rw [List.map_take, show (List.mapIdx (fun _ d => ({ directive := d, size := 1 } : Kraken.Sized Directive)) P).map (·.size)
      = List.replicate P.length 1 by apply List.ext_getElem <;> simp]
  simp [List.take_replicate]

/-- The witness host of program `P` (at most 2^32 directives). -/
@[instance_reducible] def mkHost (P : Program) (hP : P.length < 2 ^ 32) : Host where
  prog := P
  layout := ⟨0x10000, fun _ => 1⟩
  zero_inert := by intro i d _ h; simp at h
  addr_determines_offset := by
    intro j k h
    simp only [Kraken.Executable.addrOf, Kraken.Executable.sizeBefore] at h ⊢
    rw [sizeBefore_one] at h ⊢; rw [sizeBefore_one] at h ⊢
    have h' := congrArg Int64.toNatClampNeg ((Int64.add_right_inj _).mp h)
    rw [Int64.toNatClampNeg_ofNat_of_lt (by omega), Int64.toNatClampNeg_ofNat_of_lt (by omega)] at h'
    exact h'

theorem mk_addrOf (P : Program) (hP : P.length < 2 ^ 32) (j : Nat) (hj : j ≤ P.length) :
    @Host.addrOf (mkHost P hP) j = 0x10000 + Int64.ofNat j := by
  show (0x10000 : Int64) + Int64.ofNat (((Kraken.Layout.apply ⟨0x10000, fun _ => 1⟩ P).program.take j).map (·.size)).sum = _
  rw [sizeBefore_one, Nat.min_eq_left hj]

/-- Labels of a program, in order. -/
def labs (P : Program) : List Label :=
  P.filterMap fun d => match d with | .label l => some l | _ => none

theorem mem_labs {P : Program} {l : Label} (h : Kraken.Directive.label l ∈ P) : l ∈ labs P := by
  simp only [labs, List.mem_filterMap]
  exact ⟨_, h, rfl⟩

theorem labelsFresh_of [Host] {p : Program} {k : Nat}
    (h : ∀ l ∈ labs (Host.prog.take k), l ∉ labs p) : LabelsFresh p k := by
  intro i hi l hp hmem
  apply h l _ (mem_labs hmem)
  apply mem_labs
  rw [List.mem_iff_getElem?]
  exact ⟨i, by rw [List.getElem?_take, ite_eq_left_iff.mpr (fun h => absurd hi h), hp]⟩

/-- A label that occurs first at index `j` resolves to `0x10000 + j`. -/
theorem mk_label (P : Program) (hP : P.length < 2 ^ 32) (j : Nat) (l : Label)
    (hj : P[j]? = some (.label l)) (hfirst : l ∉ labs (P.take j)) :
    (letI := mkHost P hP; label l) = 0x10000 + Int64.ofNat j := by
  have hjl : j ≤ P.length := by
    rcases Nat.lt_or_ge j P.length with h | h
    · omega
    · simp [List.getElem?_eq_none h] at hj
  letI := mkHost P hP
  rw [label_eq_addrOf (l := l) (j := j) hj ?_, mk_addrOf P hP j hjl]
  intro i hi hpi
  apply hfirst
  apply mem_labs
  rw [List.mem_iff_getElem?]
  exact ⟨i, by rw [List.getElem?_take, ite_eq_left_iff.mpr (fun h => absurd hi h)]; exact hpi⟩

theorem nil_At_emp (a : BitVec 64) : Eq (([] : List UInt8).At a) = Std.ExtHashMap.emp := by
  funext m; apply propext; simp only [List.At, List.mapIdx_nil, Std.ExtHashMap.ofList_nil, Std.ExtHashMap.emp]
  exact ⟨Eq.symm, Eq.symm⟩

end Fk.W
