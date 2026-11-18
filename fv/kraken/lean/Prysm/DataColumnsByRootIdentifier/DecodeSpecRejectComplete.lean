import Prysm.DataColumnsByRootIdentifier.SpecDecodeBridge
import Prysm.DataColumnsByRootIdentifier.StatementsDecodeRejectComplete

/-!
# Reject completeness of the DataColumnsByRootIdentifier decoder

The statement is `Decode.reject_complete_statement` (`Prysm/DataColumnsByRootIdentifier/StatementsDecodeRejectComplete.lean`).
The proof is the proof of `Prysm.IndexedAttestation.Decode.reject_cases` with the fixed part of 36 bytes and the offset at `bs[32:36]`.
An input that EthLib rejects fails one check of `decodeChecks` (`spec_accepts_iff`).
-/

open EthLib.Serialization.Ssz

namespace Prysm.DataColumnsByRootIdentifier

theorem Decode.reject_complete : Decode.reject_complete_statement := by
  intro bs h
  have hn : ¬ decodeChecks bs := fun hc => h ((spec_accepts_iff bs).mpr hc)
  simp only [decodeChecks] at hn
  by_cases h1 : bs.size < 36
  · exact Or.inl h1
  by_cases h2 : (bs.toList.drop 32).take 4 = offsetBytes
  · by_cases h3 : (bs.size - 36) % 8 = 0
    · exact Or.inr (Or.inr (Or.inr ⟨by omega, h2, h3, by
        apply Nat.lt_of_not_le; intro h4; exact hn ⟨by omega, h2, h3, h4⟩⟩))
    · exact Or.inr (Or.inr (Or.inl ⟨by omega, h2, h3⟩))
  · exact Or.inr (Or.inl ⟨by omega, h2⟩)

end Prysm.DataColumnsByRootIdentifier
