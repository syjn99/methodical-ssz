import E2eScal.EncSteps
import E2eScal.FieldComp

/-!
# ENC2 L2: helpers of the generated-style field proofs of encoders

A field theorem of a generated-style encoder proof is a list of step applications on a state with literal
registers (`StepK.lean`, `EncSteps.lean`). Two helpers keep the text independent of the syntactic form a
step leaves behind:

* `kreg_eq r v`: replace the value of register `r` by an equal term `v` (the normal form the emitter writes:
  `rcx + n`, `rbx + rcx + n`, `rsp - n`). The equality is closed by `eb`. After it every later store, address
  and boundary fact names the normal form.
* `eb`: closes an address equation `base + disp = a` (`bv_omega`, with the `Int64` displacement literal
  unfolded first). The value equation of `kreg_eq` is closed by `show (actual : BitVec 64) = v; bv_omega`.
-/

open Fk

namespace E2eScal
variable [Host]

/-- The bits of a negated `Int64` literal. -/
theorem i64_neg_bv (x : Int64) : (-x).toBitVec = -x.toBitVec := rfl

/-- **Register value rewrite**: if register `r` holds `v`, the state with `r := v` may be used instead. -/
theorem kreg_eq (r : Reg64) (v : BitVec 64) (j : Nat) (final : MachineState → Prop) (s : MachineData)
    (hv : s.regs.get64 r = v)
    (hk : Eventually (step1 Host.exe) final ⟨setR s r v, Host.addrOf j⟩) :
    Eventually (step1 Host.exe) final ⟨s, Host.addrOf j⟩ := by
  subst hv
  cases r <;> exact hk

end E2eScal

/-- Close an address equation of a generated-style encoder proof: both sides are `BitVec 64` terms written by
the emitter, with `Int64` displacement literals. -/
macro "eb" : tactic => `(tactic| first
  | bv_omega
  | (simp only [Int64.toBitVec_ofNat, E2eScal.i64_neg_bv] <;> first | bv_omega | exact BitVec.add_zero _ | rfl)
  | exact BitVec.add_zero _)
