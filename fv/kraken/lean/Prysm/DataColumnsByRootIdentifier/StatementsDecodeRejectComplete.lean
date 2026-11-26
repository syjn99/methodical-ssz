import Prysm.DataColumnsByRootIdentifier.SpecDefinitions
import Prysm.DataColumnsByRootIdentifier.SpecDescription

/-!
# Hand STATEMENT of the reject completeness of the decoder

Statement only.
Statement shape: `Decode.reject_cases_statement` of `Prysm/IndexedAttestation/Statements.lean`.
The statement is about EthLib only.
Each disjunct is the path condition of one machine reject theorem of the decoder.
- `bs.size < 36`: `Decode.reject_size` and `Decode.reject_size_spec`.
- the offset is not 36: `Decode.reject_offset` and `Decode.reject_offset_spec`.
- misaligned: `Decode.reject_alignment_error_word_nonzero` and its spec form.
- more than 128 elements: `Decode.reject_overflow_error_word_nonzero` and its spec form.
The alignment and overflow theorems have the premise `e0 ≠ 0` (`Prysm/DataColumnsByRootIdentifier/StatementsDecodeErrorWordNonzero.lean`).
So for these two disjuncts the statement gives reject completeness of the machine code only under that premise.
-/

open EthLib.Serialization.Ssz

namespace Prysm.DataColumnsByRootIdentifier

/-- **Reject completeness (spec).** An input that EthLib rejects is in one of the four reject paths of the
decoder: size < 36 (size reject), offset ≠ 36 (offset reject), misaligned (alignment reject), more than 128 elements
(overflow reject). This is a statement about EthLib only. -/
def Decode.reject_complete_statement : Prop :=
  ∀ bs : Array UInt8, (¬ ∃ v, deserialize desc bs = .ok v) →
    bs.size < 36 ∨ (36 ≤ bs.size ∧ (bs.toList.drop 32).take 4 ≠ offsetBytes)
    ∨ (36 ≤ bs.size ∧ (bs.toList.drop 32).take 4 = offsetBytes ∧ (bs.size - 36) % 8 ≠ 0)
    ∨ (36 ≤ bs.size ∧ (bs.toList.drop 32).take 4 = offsetBytes ∧ (bs.size - 36) % 8 = 0 ∧ 128 < (bs.size - 36) / 8)

end Prysm.DataColumnsByRootIdentifier
