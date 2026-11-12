import E2eList.IaAccept
import E2eList.IaSpec

/-!
# `(*v1alpha1.IndexedAttestation).UnmarshalSSZ`: accept path against EthLib

`ia_e2e_accept_spec : ia_accept_spec_stmt` (frozen, `StmtIa.lean`): an input that EthLib accepts against
`prysmIaDesc` is `piaEnc g` for a `g : PIa` with `g.toValue = v` (`pia_accepted_is_enc`), and the machine code
decodes it into `g` (`ia_e2e_accept_main` with `n = g.idx.length`). The text of `E2eAd/AdSpecK.lean`.
-/

open Fk E2e EthLib.Serialization.Ssz E2eList.Code
variable [Host]

namespace E2eList

theorem ia_e2e_accept_spec : ia_accept_spec_stmt := by
  intro k hk hf kA hkA hfA kS hkS hfS kI hkI hfI kC hkC hfC kE hkE hfE bsA v hd s ra guard
    fp s1 s2 s4 l28 l30 l38 l40 l48 la0 spl rslot lo ast aP1 aL1 aC1 aD aP2 aL2 aC2
    hfp h1 h2 h4 hl28 hl30 hl38 hl40 hl48 hla0 hspl hrs hast haP1 haL1 haC1 haD haP2 haL2 haC2
    R Sd hSd8 hSd hlo Heap avail Pm hguard hlen hcap hcap63 hav hmsU hms hmm hno hmsD hmmD hmsD' hmmD' hnoD
  obtain ⟨g, rfl, hb⟩ := pia_accepted_is_enc hd
  refine ⟨g, rfl, hb, ?_⟩
  have hsz := pia_enc_size g
  rw [hb, hsz] at hlen hav
  exact ia_e2e_accept_main k hk hf kA hkA hfA kS hkS hfS kI hkI hfI kC hkC hfC kE hkE hfE g.idx.length g.hidx
    _ _ _ _ _ _ _ _ _
    (by simp [Fv.uintBytes_size]) (by simp [Fv.uintBytes_size]) (by simp) (by simp [Fv.uintBytes_size]) (by simp)
    (by simp [Fv.uintBytes_size]) (by simp) (by simp) (by simp [Fv1.u64Bytes_size])
    s ra guard fp s1 s2 s4 l28 l30 l38 l40 l48 la0 spl rslot lo ast aP1 aL1 aC1 aD aP2 aL2 aC2
    hfp h1 h2 h4 hl28 hl30 hl38 hl40 hl48 hla0 hspl hrs hast haP1 haL1 haC1 haD haP2 haL2 haC2
    R Sd hSd8 hSd hlo Heap avail (Pm g hb) hguard hlen hcap hcap63 (by omega)
    hmsU hms hmm hno hmsD hmmD hmsD' hmmD' hnoD

end E2eList
