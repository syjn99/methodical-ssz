import Prysm.IndexedAttestation.DecodeAccept
import Prysm.IndexedAttestation.Spec

/-!
# `(*v1alpha1.IndexedAttestation).UnmarshalSSZ`: accept path against EthLib

`Decode.accept_spec : Decode.accept_spec_statement` (frozen, `Prysm/IndexedAttestation/Statements.lean`): an input that EthLib accepts against
`desc` is `SszValue.encode g` for a `g : SszValue` with `g.toValue = v` (`accepted_is_encode`), and the machine code
decodes it into `g` (`Decode.accept` with `n = g.idx.length`). The text of `Prysm/AttestationData/DecodeSpec.lean`.
-/

open Machine Runtime EthLib.Serialization.Ssz Prysm.IndexedAttestation.Code
variable [Host]

namespace Prysm.IndexedAttestation

theorem Decode.accept_spec : Decode.accept_spec_statement := by
  intro k hk hf kA hkA hfA kS hkS hfS kI hkI hfI kC hkC hfC kE hkE hfE bsA v hd s ra guard
    fp s1 s2 s4 l28 l30 l38 l40 l48 la0 spl rslot lo ast aP1 aL1 aC1 aD aP2 aL2 aC2
    hfp h1 h2 h4 hl28 hl30 hl38 hl40 hl48 hla0 hspl hrs hast haP1 haL1 haC1 haD haP2 haL2 haC2
    R Sd hSd8 hSd hlo Heap avail Pm hguard hlen hcap hcap63 hav hmsU hms hmm hno hmsD hmmD hmsD' hmmD' hnoD
  obtain ⟨g, rfl, hb⟩ := accepted_is_encode hd
  refine ⟨g, rfl, hb, ?_⟩
  have hsz := encode_size g
  rw [hb, hsz] at hlen hav
  exact Decode.accept k hk hf kA hkA hfA kS hkS hfS kI hkI hfI kC hkC hfC kE hkE hfE g.idx.length g.hidx
    _ _ _ _ _ _ _ _ _
    (by simp [Spec.uintBytes_size]) (by simp [Spec.uintBytes_size]) (by simp) (by simp [Spec.uintBytes_size]) (by simp)
    (by simp [Spec.uintBytes_size]) (by simp) (by simp) (by simp [Spec.uint64Bytes_size])
    s ra guard fp s1 s2 s4 l28 l30 l38 l40 l48 la0 spl rslot lo ast aP1 aL1 aC1 aD aP2 aL2 aC2
    hfp h1 h2 h4 hl28 hl30 hl38 hl40 hl48 hla0 hspl hrs hast haP1 haL1 haC1 haD haP2 haL2 haC2
    R Sd hSd8 hSd hlo Heap avail (Pm g hb) hguard hlen hcap hcap63 (by omega)
    hmsU hms hmm hno hmsD hmmD hmsD' hmmD' hnoD

end Prysm.IndexedAttestation
