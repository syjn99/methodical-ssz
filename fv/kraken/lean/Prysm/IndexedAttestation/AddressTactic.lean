import Machine.Step

/-! The address tactic of the IndexedAttestation proofs (moved from `Prysm/IndexedAttestation/DecodeRejectSize.lean`, so that `Prysm/IndexedAttestation/DecodeAccept.lean` does not import the
reject module; `gen/e2e/lvnegative.py` inlines `Prysm/IndexedAttestation/Statements.lean` into a mutant and needs it imported only once). -/

namespace Prysm.IndexedAttestation

/-- Address equation by `toNat` and `omega` (`address_equation` plus `Width.bits`). -/
macro "indexed_attestation_addr" : tactic => `(tactic| (
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_neg, BitVec.toNat_ofNat, BitVec.ofNat_eq_ofNat,
    UInt64.toNat_toBitVec, UInt64.toBitVec_add, UInt64.toBitVec_ofNat, Width.bits, Nat.reducePow]
  all_goals omega))

end Prysm.IndexedAttestation
