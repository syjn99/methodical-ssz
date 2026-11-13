import Prysm.Checkpoint.Spec
import Prysm.Checkpoint.SpecEquivalence
import EthLib.Serialization.Proofs.Ssz.Codec.Table
import EthLib.Serialization.Proofs.Ssz.Codec.CanonicalTable
import Prysm.SyncCommittee.SpecDefinitions

/-!
# EthLib `assemble` of a list of fixed-size parts

`headWidth_inline`, `bodyWidth_inline`, `assemble_inline_ok`: for parts that are all inline, the head is the
concatenation of the parts and the body is empty. Stated for any list of parts.
-/

namespace Codec
open EthLib.Serialization.Ssz Spec

theorem headWidth_inline : ∀ (parts : List Bytes),
    headWidth ((parts.map fun _ => true).zip parts) = (concatParts parts).size
  | [] => rfl
  | p :: ps => by simp [headWidth, concatParts, Codec.headWidth_inline ps]

theorem bodyWidth_inline : ∀ (parts : List Bytes), bodyWidth ((parts.map fun _ => true).zip parts) = 0
  | [] => rfl
  | p :: ps => by simp [bodyWidth, Codec.bodyWidth_inline ps]

theorem assemble_inline_ok (parts : List Bytes) (h : (concatParts parts).size < 2 ^ 32) :
    assemble (parts.map fun _ => true) parts = .ok (concatParts parts) := by
  have h1 := Codec.headWidth_inline parts
  have h2 := Codec.bodyWidth_inline parts
  have h3 := headOf_inline parts
  have h4 := bodiesOf_inline parts
  simp only [assemble, h1, h2, bytesPerOffset]
  simp only [Nat.add_zero, show ¬ (concatParts parts).size ≥ 2 ^ (8 * 4) by omega, ↓reduceIte, pure, Except.pure]
  rw [h3, h4, Array.append_empty]

end Codec
