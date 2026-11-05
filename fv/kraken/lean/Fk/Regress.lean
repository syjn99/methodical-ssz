import Fk.RtErr
import Fk.WHost
import Fk.BumpMore
import Fk.Vbl
import Fk.Witness

/-!
# Regression checks that keep their meaning (re-proof R10, astra 1b-fix 7)

The 1b review file `review/Review1b.lean` no longer elaborates against the new
contract signatures; a type error is not a regression test. This module states
what the old counterexamples exercised, as theorems in the build:

- `joint_models`: one host and one heap (`bumpHeap`) satisfy nine contracts
  together: makeslice (1-byte elements), memmove, growslice, the 16-byte
  newobject (the errorString of the nil error paths), the two `fmt.errorf`
  contracts (one code), convT64 and both ValidateBitlist contracts (the
  `bsr`-free model; re-proof fix X5).
  `not_joint_false` states that these premises do not prove `False`.
- `old_input_excluded`: the 1b growslice counterexample input (`newLen = 2^63`)
  violates the new budget premise.
Call witnesses (`*_runs` in `Fk/Wit*.lean`) are the third kind of check.
-/

open Fk Fk.Code Fk.W

namespace Fk.Regress

def P : Program :=
  [.label "runtime.fvBump", .label "go_itab._errors.errorString_error"]
    ++ BumpAlloc1 ++ RtCopy ++ BumpNew16 ++ RtErr ++ RtVbl

set_option maxRecDepth 100000 in
theorem P_len : P.length = 72 := by rfl

instance host : Host := mkHost P (by rw [P_len]; decide)
theorem prog_eq : Host.prog = P := rfl

set_option maxRecDepth 100000 in
theorem hkM : BumpAlloc1.IsInfixAt Host.prog 2 := by
  rw [prog_eq]; exact ⟨RtCopy ++ BumpNew16 ++ RtErr ++ RtVbl, by rfl⟩
set_option maxRecDepth 100000 in
theorem hkC : RtCopy.IsInfixAt Host.prog 8 := by
  rw [prog_eq]; exact ⟨BumpNew16 ++ RtErr ++ RtVbl, by rfl⟩
set_option maxRecDepth 100000 in
theorem hkN : BumpNew16.IsInfixAt Host.prog 34 := by
  rw [prog_eq]; exact ⟨RtErr ++ RtVbl, by rfl⟩
set_option maxRecDepth 100000 in
theorem hkE : RtErr.IsInfixAt Host.prog 40 := by
  rw [prog_eq]; exact ⟨RtVbl, by rfl⟩
set_option maxRecDepth 100000 in
theorem hkV : RtVbl.IsInfixAt Host.prog 51 := by
  rw [prog_eq]; exact ⟨[], by rfl⟩

set_option maxRecDepth 100000 in
theorem hfC : LabelsFresh RtCopy 8 := labelsFresh_of (by rw [prog_eq]; decide)
set_option maxRecDepth 100000 in
theorem hfE : LabelsFresh RtErr 40 := labelsFresh_of (by rw [prog_eq]; decide)
set_option maxRecDepth 100000 in
theorem hfV : LabelsFresh RtVbl 51 := labelsFresh_of (by rw [prog_eq]; decide)

set_option maxRecDepth 100000 in
theorem hfM : ∀ i < 2, Host.prog[i]? ≠ some (.label "runtime.makeslice") := by
  have hl : "runtime.makeslice" ∉ labs (P.take 2) := by decide
  intro i hi hp
  apply hl; apply mem_labs; rw [List.mem_iff_getElem?]
  exact ⟨i, by rw [List.getElem?_take, ite_eq_left_iff.mpr (fun h => absurd hi h)]; exact hp⟩
set_option maxRecDepth 100000 in
theorem hfN : ∀ i < 34, Host.prog[i]? ≠ some (.label "runtime.newobject") := by
  have hl : "runtime.newobject" ∉ labs (P.take 34) := by decide
  intro i hi hp
  apply hl; apply mem_labs; rw [List.mem_iff_getElem?]
  exact ⟨i, by rw [List.getElem?_take, ite_eq_left_iff.mpr (fun h => absurd hi h)]; exact hp⟩

set_option maxRecDepth 100000 in
theorem label_itab : label "go_itab._errors.errorString_error" = 0x10000 + 1 :=
  mk_label P _ 1 _ (by simp [P]) (by decide)
theorem hit : (label "go_itab._errors.errorString_error").toBitVec ≠ 0 := by rw [label_itab]; decide

/-- The nine contracts used by the theorems, in one host and one heap
(re-proof fix X5: `FmtErrorfWC` replaced `FmtErrorfC`; `ValidateBitlistErrC` added). -/
def Joint (S : Nat) (ty : BitVec 64) : Prop :=
  MakesliceC bumpHeap ty 1 S ∧ MemmoveC S ∧ GrowsliceC bumpHeap ty 1 S ∧ NewobjectC bumpHeap ty 16 S
    ∧ FmtErrorfNilC S ∧ FmtErrorfWC bumpHeap S ∧ ConvT64C bumpHeap S
    ∧ ValidateBitlistC S ∧ ValidateBitlistErrC bumpHeap S

theorem joint_models (S : Nat) (ty : BitVec 64) : Joint S ty :=
  ⟨bump_makeslice1 2 hkM hfM ty, rt_memmove 8 hkC hfC S, rt_growslice 8 hkC hfC ty S,
    bump_newobject16 34 hkN hfN ty, rt_errorf_nil 40 hkE hfE S,
    rt_errorf_w 40 hkE hfE bumpHeap S, rt_convT64 40 hkE hfE bumpHeap S, rt_validate_bitlist 51 hkV hfV S,
    rt_validate_bitlist_err 51 hkV hfV S⟩

theorem not_joint_false (S : Nat) (ty : BitVec 64) : ¬ (Joint S ty → False) :=
  fun h => h (joint_models S ty)

end Fk.Regress

/-- The 1b growslice counterexample input (`newLen = 2^63`) violates the budget premise. -/
theorem Fk.Regress.old_input_excluded (esz oc avail : Nat) (he : 0 < esz) :
    ¬ (2 * (esz * nextSliceCap (2 ^ 63) oc) + 8192 ≤ avail ∧ avail ≤ maxAlloc) :=
  Fk.Witness.review1b_input_excluded esz oc avail he
