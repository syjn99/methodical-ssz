import E2eList.IaReject
import E2eList.IaSpec

/-!
# Spec alignment of the IndexedAttestation decoder's size and offset rejects, and the reject cases

The statements are the frozen `ia_reject_size_spec_stmt`, `ia_reject_offset_spec_stmt` and `ia_reject_cases_stmt`
(`StmtIa.lean`). `ia_e2e_reject_cases` is about EthLib only. It gives reject completeness of the machine code only for the reject
paths with a machine theorem (the alignment and overflow rejects only under `e0 ≠ 0`, `StmtIaNz.lean`).
-/

open Machine Runtime TestTarget E2e EthLib.Serialization.Ssz E2eList.Code
variable [Host]

namespace E2eList

theorem ia_e2e_reject_size_spec : ia_reject_size_spec_stmt := by
  intro k hk hf bs hbs s ra guard e0 e1 fp s2 hfp h2 R h_mem hguard hlen
  exact ⟨pia_spec_rejects bs (fun h => by have := h.1; omega),
    ia_e2e_reject_size_main k hk hf s ra guard e0 e1 fp s2 hfp h2 R h_mem hguard (by omega)⟩

theorem ia_e2e_reject_offset_spec : ia_reject_offset_spec_stmt := by
  intro k hk hf bs hbs hoff s ra guard e0 e1 fp s2 hfp h2 R h_mem hguard hlen
  exact ⟨pia_spec_rejects bs (fun h => hoff h.2.1),
    ia_e2e_reject_offset_main k hk hf s ra guard e0 e1 fp s2 hfp h2 (bs.toList.take 4) (by simp; omega) hoff R
      h_mem hguard (by omega)⟩

theorem ia_e2e_reject_cases : ia_reject_cases_stmt := by
  intro bs h
  have hn : ¬ iaChecks bs := fun hc => h ((pia_spec_accepts_iff bs).mpr hc)
  simp only [iaChecks] at hn
  by_cases h1 : bs.size < 228
  · exact Or.inl h1
  by_cases h2 : bs.toList.take 4 = iaOff
  · by_cases h3 : (bs.size - 228) % 8 = 0
    · exact Or.inr (Or.inr (Or.inr ⟨by omega, h2, h3, by
        apply Nat.lt_of_not_le; intro h4; exact hn ⟨by omega, h2, h3, h4⟩⟩))
    · exact Or.inr (Or.inr (Or.inl ⟨by omega, h2, h3⟩))
  · exact Or.inr (Or.inl ⟨by omega, h2⟩)

end E2eList
