import Codec.SegmentTemplate
import Runtime.Contracts
import Prysm.ElfData.PrysmTarget

/-!
# Address equations of the segment lemmas

The tactic `segment_addr` proves an address equation of a segment lemma, for example `sp + dR.toBitVec = aR`.
It goes to `toNat` and closes the goal with `omega`.
The imports give the segment lemmas that import this module the code templates, the runtime contracts and the ELF data.
-/

open Machine Runtime

namespace Codec

variable [Host]

/-- Address equation by `toNat` and `omega`. -/
macro "segment_addr" : tactic => `(tactic| (
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_neg, BitVec.toNat_ofNat, BitVec.ofNat_eq_ofNat,
    UInt64.toNat_toBitVec, UInt64.toBitVec_add, UInt64.toBitVec_ofNat, Width.bits, Nat.reducePow]
  all_goals omega))

end Codec
