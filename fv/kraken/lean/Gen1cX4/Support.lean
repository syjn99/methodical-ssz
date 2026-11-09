import Fk.Bytes

/-! Lemmas used by the proofs that fv/kraken/gen/x4 generates. Written by hand, not generated.
`ofBytes1` is the statement of `Fk.sc_ofBytes1` (Fk/ScRejectBool.lean), proved here again so the
generated modules do not import a hand proof module. -/

namespace Gen1cX4

theorem ofBytes1 (e : UInt8) : BitVec.ofInt 8 (Int.ofBytes [e]) = e.toBitVec := by
  have := e.toNat_lt
  apply BitVec.eq_of_toNat_eq
  simp [Int.ofBytes, BitVec.toNat_ofInt]

end Gen1cX4
