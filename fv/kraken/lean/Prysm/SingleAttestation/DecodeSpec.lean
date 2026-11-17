import Prysm.SingleAttestation.DecodeAccept
import Prysm.SingleAttestation.DecodeRejectSize
import Prysm.SingleAttestation.Spec

/-!
# Spec alignment of the SingleAttestation decoder

The statements are `Decode.accept_spec_statement`, `Decode.reject_size_spec_statement` and
`Decode.reject_complete_statement` (`Prysm/SingleAttestation/Statements.lean`).
-/

open Machine Runtime EthLib.Serialization.Ssz
variable [Host]

namespace Prysm.SingleAttestation

theorem Decode.accept_spec : Decode.accept_spec_statement := by
  intro k hk hf kA hkA hfA kS hkS hfS kI hkI hfI kV hkV hfV kC hkC hfC kE hkE hfE bsA v hd s ra guard
    fp s1 s2 s4 l28 l30 l38 spl rslot lo ast aCI aAI aD aP aL aC
    hfp h1 h2 h4 hl28 hl30 hl38 hspl hrs hast haCI haAI haD haP haL haC
    R Sd hSd8 hSd hlo Heap avail Pm hguard hlen hav hno hms hmm hmsD hmmD hmsD' hmmD' hnoD
  obtain ⟨g, rfl, rfl⟩ := SszValue.accepted_is_encoding hd
  refine ⟨g, rfl, rfl, ?_⟩
  have h240 : s.regs.rcx = 240 := by
    apply UInt64.toNat_inj.mp; rw [hlen, SszValue.encode_size]; rfl
  exact Decode.accept k hk hf kA hkA hfA kS hkS hfS kI hkI hfI kV hkV hfV kC hkC hfC kE hkE hfE _ _ _ _ _ _ _ _ _ _
    (by simp [Spec.uintBytes_size]) (by simp [Spec.uintBytes_size]) (by simp [Spec.uintBytes_size])
    (by simp [Spec.uintBytes_size]) (by simp) (by simp [Spec.uintBytes_size]) (by simp) (by simp [Spec.uintBytes_size])
    (by simp) (by simp) s ra guard
    fp s1 s2 s4 l28 l30 l38 spl rslot lo ast aCI aAI aD aP aL aC
    hfp h1 h2 h4 hl28 hl30 hl38 hspl hrs hast haCI haAI haD haP haL haC
    R Sd hSd8 hSd hlo Heap avail (Pm g rfl) hguard h240 hav hno hms hmm hmsD hmmD hmsD' hmmD' hnoD

theorem Decode.reject_size_spec : Decode.reject_size_spec_statement := by
  intro k hk hf bs hbs s ra guard e0 e1 fp s2 hfp h2 R h_mem hguard hlen
  exact ⟨SszValue.spec_rejects bs hbs, Decode.reject_size k hk hf s ra guard e0 e1 fp s2 hfp h2 R h_mem hguard
    (fun h => hbs (by rw [← hlen, h]; rfl))⟩

omit [Host] in
theorem Decode.reject_complete : Decode.reject_complete_statement :=
  fun bs h h240 => h ((SszValue.spec_accepts_iff bs).mpr h240)

end Prysm.SingleAttestation
