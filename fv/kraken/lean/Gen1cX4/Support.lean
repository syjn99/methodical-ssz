import Fk.Bytes
import Fk.Flags

/-! Lemmas used by the proofs that fv/kraken/gen/x4 generates. Written by hand, not generated.
`ofBytes1` is the statement of `Fk.sc_ofBytes1` (Fk/ScRejectBool.lean), proved here again so the
generated modules do not import a hand proof module. -/

namespace Gen1cX4

theorem ofBytes1 (e : UInt8) : BitVec.ofInt 8 (Int.ofBytes [e]) = e.toBitVec := by
  have := e.toNat_lt
  apply BitVec.eq_of_toNat_eq
  simp [Int.ofBytes, BitVec.toNat_ofInt]

end Gen1cX4

namespace Gen1cX4

/-- The statement of `Fk.lu_off4` (Fk/LuReject.lean), proved here again: the 32-bit load of a
first offset, zero-extended and compared with 4. -/
theorem off4 (o4 : List UInt8) (ho4 : o4.length = 4)
    (h : BitVec.zeroExtend 64 (BitVec.ofInt 32 (Int.ofBytes o4)) - 4 = 0#64) : Int.ofBytes o4 = 4 := by
  have h0 := Int.ofBytes_ge_zero o4
  have h1 := Int.ofBytes_lt o4
  rw [ho4] at h1
  have hx : BitVec.zeroExtend 64 (BitVec.ofInt 32 (Int.ofBytes o4)) = 4 := by
    rw [← BitVec.sub_add_cancel (BitVec.zeroExtend 64 (BitVec.ofInt 32 (Int.ofBytes o4))) 4, h]; rfl
  have := congrArg BitVec.toNat hx
  simp [BitVec.toNat_ofInt] at this
  omega

end Gen1cX4
