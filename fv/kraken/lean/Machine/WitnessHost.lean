import Machine.Labels
import Machine.Bytes

/-!
# Witness hosts

`mkHost P`: a `Host` whose program is `P` and whose directive `i` sits at
address `0x10000 + i` (every directive has size 1). Witness files build one
host per main theorem: data labels first, then the target function, then the
runtime models. `labelsFresh_of` turns a Boolean label check into
`LabelsFresh`; `mk_label` resolves a label to its address.
-/

open Machine TestTarget

namespace Machine.Witness

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

/-- `X` sits at index `A.length` of `A ++ (X ++ B)`. -/
theorem infixAt_of {P : Program} (A : Program) {X : Program} (B : Program) {n : Nat}
    (hP : P = A ++ (X ++ B)) (hn : A.length = n) : X.IsInfixAt P n := by
  subst hP hn
  exact ⟨B, by rw [List.drop_left]⟩

/-- A label that does not occur in the first `k` directives sits at no index below `k`. -/
theorem notLabel_of [Host] {k : Nat} {l : Label} (h : l ∉ labs (Host.prog.take k)) :
    ∀ i < k, Host.prog[i]? ≠ some (.label l) := by
  intro i hi hp
  apply h; apply mem_labs; rw [List.mem_iff_getElem?]
  exact ⟨i, by rw [List.getElem?_take, ite_eq_left_iff.mpr (fun h => absurd hi h)]; exact hp⟩

theorem u64_toBitVec_zero : (UInt64.toBitVec 0) = 0#64 := rfl
theorem u64_toBitVec_ofNat (n : Nat) : (UInt64.ofNat n).toBitVec = BitVec.ofNat 64 n := rfl

/-- Split `H : Eq ((block ..).At a) m` into one `Eq (chunk.At addr)` per chunk and
normalize the addresses; the terms are the length hypotheses of the chunks.
Hygiene is off: `H` and `block` are the witness file's names. -/
syntax "wit_split" (" [" term,* "]")? : tactic
set_option hygiene false in
macro_rules
  | `(tactic| wit_split $[[$hs,*]]?) => do
    let hs := (hs.map (·.getElems)).getD #[]
    let ls ← hs.mapM fun h => `(Lean.Parser.Tactic.simpLemma| $h:term)
    let l1 := #[← `(Lean.Parser.Tactic.simpLemma| List.length_append), ← `(Lean.Parser.Tactic.simpLemma| List.length_replicate),
      ← `(Lean.Parser.Tactic.simpLemma| Int.toBytes_length), ← `(Lean.Parser.Tactic.simpLemma| List.length_cons),
      ← `(Lean.Parser.Tactic.simpLemma| List.length_nil)] ++ ls
    let l2 := #[← `(Lean.Parser.Tactic.simpLemma| List.length_replicate), ← `(Lean.Parser.Tactic.simpLemma| Int.toBytes_length),
      ← `(Lean.Parser.Tactic.simpLemma| List.length_cons), ← `(Lean.Parser.Tactic.simpLemma| List.length_nil),
      ← `(Lean.Parser.Tactic.simpLemma| Nat.reduceAdd)] ++ ls ++
      #[← `(Lean.Parser.Tactic.simpLemma| BitVec.ofNat_eq_ofNat), ← `(Lean.Parser.Tactic.simpLemma| BitVec.reduceAdd)]
    `(tactic| (
      conv at H => lhs; unfold block
      repeat rw [Mem.At_append_sep _ _ _ (by simp only [$l1,*]; omega)] at H
      simp only [$l2,*] at H))

end Machine.Witness
