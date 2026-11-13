import Prysm.AttestationData.DecodeAccept
import Codec.StackGuard
import Prysm.IndexedAttestation.AddressTactic
import Prysm.IndexedAttestation.Statements
import Prysm.IndexedAttestation.DecodeLoop

/-!
# `sar $0x3f` of a negated positive value

`sshiftRight_neg_63_eq_allOnes`: for `0 < d < 2^63`, the arithmetic shift right by 63 of `-d` is all ones.
-/

open Machine Runtime Prysm.IndexedAttestation.Code
variable [Host]

namespace Codec

omit [Host] in
/-- `sar $0x3f` of a negated positive value below 2⁶³ (directive 21). -/
theorem sshiftRight_neg_63_eq_allOnes (d : BitVec 64) (h0 : d.toNat ≠ 0) (h1 : d.toNat < 2 ^ 63) :
    BitVec.sshiftRight (-d) 63 = BitVec.allOnes 64 := by
  apply BitVec.eq_of_toInt_eq
  rw [BitVec.toInt_sshiftRight, BitVec.toInt_allOnes]
  have hn : (-d).toInt = -(d.toNat : Int) := by
    rw [BitVec.toInt_neg_of_ne_intMin]
    · rw [BitVec.toInt_eq_toNat_of_lt (by omega)]
    · intro h; have := congrArg BitVec.toNat h; simp [BitVec.toNat_intMin] at this; omega
  rw [hn, Int.shiftRight_eq_div_pow]
  simp only [Nat.reducePow]
  omega

end Codec
