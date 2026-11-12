import Fk.Step

/-! The address tactic of the T3 proofs (moved from `IaReject.lean`, so that `IaAccept.lean` does not import the
reject module; `gen/e2e/lvnegative.py` inlines `StmtIa.lean` into a mutant and needs it imported only once). -/

namespace E2eList

/-- Address equation by `toNat` and `omega` (`kaddr` plus `Width.bits`). -/
macro "iaaddr" : tactic => `(tactic| (
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_neg, BitVec.toNat_ofNat, BitVec.ofNat_eq_ofNat,
    UInt64.toNat_toBitVec, UInt64.toBitVec_add, UInt64.toBitVec_ofNat, Width.bits, Nat.reducePow]
  all_goals omega))

end E2eList
