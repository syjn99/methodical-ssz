import Runtime.Contracts
import Machine.Frame
import Prysm.Checkpoint.Code
import Prysm.Checkpoint.DecodeAccept
import Machine.StoreLemmas
import Runtime.StaticBoxLemmas

/-!
# BitVec equalities that the encoder proofs of several types use

`add_mul_one`: an address with scale 1 (`x + y * 1 = x + y`). `eq_32_of_sub_eq_zero`: the 32-byte length check of an
encoder reject (`x - 32 = 0` gives `x = 32`).
-/

open Machine Runtime Prysm.Checkpoint.Code
variable [Host]

namespace Codec

theorem add_mul_one (x y : BitVec 64) : x + y * 1#64 = x + y := by rw [BitVec.mul_one]

theorem eq_32_of_sub_eq_zero (x : BitVec 64) (h : x - 32#64 = 0#64) : x = 32 := by bv_omega

theorem add_add_8_mul_one (x y : BitVec 64) : x + (y + 8) * 1#64 = x + y + 8 := by
  rw [BitVec.mul_one, BitVec.add_assoc]

end Codec
