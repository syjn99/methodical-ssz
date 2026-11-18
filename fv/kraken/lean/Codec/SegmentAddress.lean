import Machine.Step

/-!
# Address equations of the segment and loop lemmas

The tactic `segment_addr` proves an address equation of a segment lemma, for example `sp + dR.toBitVec = aR`.
It goes to `toNat` and closes the goal with `omega`.
The tactic `address_with_products` does the same for an address with products and shifts, for example the address of
element `i` of a loop.
The scoped notation `shift_left5 x` is the value of `shl $5` on `x` in the form of the step lemmas.
-/

namespace Codec

/-- Address equation by `toNat` and `omega`. -/
macro "segment_addr" : tactic => `(tactic| (
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_neg, BitVec.toNat_ofNat, BitVec.ofNat_eq_ofNat,
    UInt64.toNat_toBitVec, UInt64.toBitVec_add, UInt64.toBitVec_ofNat, Width.bits, Nat.reducePow]
  all_goals omega))

/-- Address equation by `toNat` and `omega` with products and shifts (the `address_equation` set plus `toNat_mul` and
`toNat_shiftLeft`). -/
macro "address_with_products" : tactic => `(tactic| (
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_neg, BitVec.toNat_ofNat, BitVec.ofNat_eq_ofNat,
    BitVec.toNat_mul, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, UInt64.toNat_toBitVec, UInt64.toBitVec_add,
    UInt64.toBitVec_ofNat, Width.bits, Nat.reducePow]
  all_goals omega))

/-- The value that `shl $5` leaves in a 64-bit register, with Kraken's width term `Width.W64.bits` in the
shift instance (the form `shift_left64` produces; `x <<< 5` at width `64` is not syntactically equal, and `ecancel` does
not unify the two). -/
scoped notation "shift_left5 " x:max => @HShiftLeft.hShiftLeft Width.W64.type Nat (BitVec 64)
  (@BitVec.instHShiftLeftNat Width.W64.bits) x 5

end Codec
