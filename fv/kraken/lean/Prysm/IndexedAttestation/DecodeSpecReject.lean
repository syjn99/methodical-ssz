import Prysm.IndexedAttestation.DecodeRejectSize
import Prysm.IndexedAttestation.Spec
import Prysm.IndexedAttestation.DecodeRejectOffset

/-!
# Spec alignment of the IndexedAttestation decoder's size and offset rejects, and the reject cases

The statements are the frozen `Decode.reject_size_spec_statement`, `Decode.reject_offset_spec_statement` and `Decode.reject_cases_statement`
(`Prysm/IndexedAttestation/Statements.lean`). `Decode.reject_cases` is about EthLib only. It gives reject completeness of the machine code only for the reject
paths with a machine theorem (the alignment and overflow rejects only under `e0 ≠ 0`, `Prysm/IndexedAttestation/StatementsErrorWordNonzero.lean`).
-/

open Machine Runtime EthLib.Serialization.Ssz Prysm.IndexedAttestation.Code
variable [Host]

namespace Prysm.IndexedAttestation

theorem Decode.reject_size_spec : Decode.reject_size_spec_statement := by
  intro k hk hf bs hbs s ra guard e0 e1 fp s2 hfp h2 R h_mem hguard hlen
  exact ⟨spec_rejects bs (fun h => by have := h.1; omega),
    Decode.reject_size k hk hf s ra guard e0 e1 fp s2 hfp h2 R h_mem hguard (by omega)⟩

theorem Decode.reject_offset_spec : Decode.reject_offset_spec_statement := by
  intro k hk hf bs hbs hoff s ra guard e0 e1 fp s2 hfp h2 R h_mem hguard hlen
  exact ⟨spec_rejects bs (fun h => hoff h.2.1),
    Decode.reject_offset k hk hf s ra guard e0 e1 fp s2 hfp h2 (bs.toList.take 4) (by simp; omega) hoff R
      h_mem hguard (by omega)⟩

theorem Decode.reject_cases : Decode.reject_cases_statement := by
  intro bs h
  have hn : ¬ decodeChecks bs := fun hc => h ((spec_accepts_iff bs).mpr hc)
  simp only [decodeChecks] at hn
  by_cases h1 : bs.size < 228
  · exact Or.inl h1
  by_cases h2 : bs.toList.take 4 = offsetBytes
  · by_cases h3 : (bs.size - 228) % 8 = 0
    · exact Or.inr (Or.inr (Or.inr ⟨by omega, h2, h3, by
        apply Nat.lt_of_not_le; intro h4; exact hn ⟨by omega, h2, h3, h4⟩⟩))
    · exact Or.inr (Or.inr (Or.inl ⟨by omega, h2, h3⟩))
  · exact Or.inr (Or.inl ⟨by omega, h2⟩)

end Prysm.IndexedAttestation
