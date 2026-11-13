import Codec.EncodeSteps
import Codec.FieldFrame

/-!
# Helpers of the generated-style field proofs of encoders

A field theorem of a generated-style encoder proof is a list of step applications on a state with literal
registers (`Codec/WindowSteps.lean`, `Codec/EncodeSteps.lean`). Two helpers keep the text independent of the syntactic form a
step leaves behind:

* `register_value_rewrite r v`: replace the value of register `r` by an equal term `v` (the normal form the emitter writes:
  `rcx + n`, `rbx + rcx + n`, `rsp - n`). The equality is closed by `encoder_address_equation`. After it every later store, address
  and boundary fact names the normal form.
* `encoder_address_equation`: closes an address equation `base + disp = a` (`bv_omega`, with the `Int64` displacement literal
  unfolded first). The value equation of `register_value_rewrite` is closed by `show (actual : BitVec 64) = v; bv_omega`.
-/

open Machine Runtime

namespace Codec
variable [Host]

/-- The bits of a negated `Int64` literal. -/
theorem int64_neg_toBitVec (x : Int64) : (-x).toBitVec = -x.toBitVec := rfl

/-- **Register value rewrite**: if register `r` holds `v`, the state with `r := v` may be used instead. -/
theorem register_value_rewrite (r : Reg64) (v : BitVec 64) (j : Nat) (final : MachineState → Prop) (s : MachineData)
    (hv : s.regs.get64 r = v)
    (hk : Eventually (step1 Host.exe) final ⟨setRegister s r v, Host.addrOf j⟩) :
    Eventually (step1 Host.exe) final ⟨s, Host.addrOf j⟩ := by
  subst hv
  cases r <;> exact hk

end Codec

/-- Close an address equation of a generated-style encoder proof: both sides are `BitVec 64` terms written by
the emitter, with `Int64` displacement literals. -/
macro "encoder_address_equation" : tactic => `(tactic| first
  | bv_omega
  | (simp only [Int64.toBitVec_ofNat, Codec.int64_neg_toBitVec] <;> first | bv_omega | exact BitVec.add_zero _ | rfl)
  | exact BitVec.add_zero _)
