import Prysm.SingleAttestation.DecodeRejectSize
import Prysm.SingleAttestation.Spec

/-!
# Spec alignment of the SingleAttestation decoder

The statements are
`Decode.reject_size_spec_statement` and `Decode.reject_complete_statement` (`Prysm/SingleAttestation/Statements.lean`).
-/

open Machine Runtime EthLib.Serialization.Ssz
variable [Host]

namespace Prysm.SingleAttestation

theorem Decode.reject_size_spec : Decode.reject_size_spec_statement := by
  intro k hk hf bs hbs s ra guard e0 e1 fp s2 hfp h2 R h_mem hguard hlen
  exact ⟨SszValue.spec_rejects bs hbs, Decode.reject_size k hk hf s ra guard e0 e1 fp s2 hfp h2 R h_mem hguard
    (fun h => hbs (by rw [← hlen, h]; rfl))⟩

omit [Host] in
theorem Decode.reject_complete : Decode.reject_complete_statement :=
  fun bs h h240 => h ((SszValue.spec_accepts_iff bs).mpr h240)

end Prysm.SingleAttestation
