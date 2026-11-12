import Prysm.IndexedAttestation.DecodeRejectAlignment
import Prysm.IndexedAttestation.Spec

/-!
# Spec alignment of the IndexedAttestation alignment reject and overflow reject

Statements: the corrected `Decode.reject_alignment_spec_error_word_nonzero_statement` and `Decode.reject_overflow_spec_error_word_nonzero_statement` (`Prysm/IndexedAttestation/StatementsErrorWordNonzero.lean`):
EthLib rejects (`spec_rejects`: the Go check that fails is one of `decodeChecks`) and the machine code returns the
`fmt.errorf` error (`Decode.reject_alignment_error_word_nonzero`, `Decode.reject_overflow_error_word_nonzero`). The text of `Prysm/IndexedAttestation/DecodeSpecReject.lean`.
-/

open Machine Runtime TestTarget EthLib.Serialization.Ssz Prysm.IndexedAttestation.Code
variable [Host]

namespace Prysm.IndexedAttestation

theorem Decode.reject_alignment_spec_error_word_nonzero : Decode.reject_alignment_spec_error_word_nonzero_statement := by
  intro k hk hf bs hbs hoff hmis s ra guard e0 e1 esp msg ity he0 he0nz hity fp s2 aw spl rslot lo hfp h2 haw hspl
    hrs S hlo Heap avail R h_mem hguard hlen hav hcv hfe
  exact ⟨spec_rejects bs (fun h => hmis h.2.2.1),
    Decode.reject_alignment_error_word_nonzero k hk hf s ra guard e0 e1 esp msg ity he0 he0nz hity fp s2 aw spl rslot lo hfp h2 haw
      hspl hrs S hlo Heap avail R h_mem hguard (by omega) (by rw [hlen]; exact hmis) hav hcv hfe⟩

theorem Decode.reject_overflow_spec_error_word_nonzero : Decode.reject_overflow_spec_error_word_nonzero_statement := by
  intro k hk hf bs hbs hoff hal hbig s ra guard e0 e1 esp msg ity he0 he0nz hity fp s2 aw spl rslot lo hfp h2 haw hspl
    hrs S hlo Heap avail R h_mem hguard hlen hav hcv hfe
  exact ⟨spec_rejects bs (fun h => by have := h.2.2.2; omega),
    Decode.reject_overflow_error_word_nonzero k hk hf s ra guard e0 e1 esp msg ity he0 he0nz hity fp s2 aw spl rslot lo hfp h2 haw
      hspl hrs S hlo Heap avail R h_mem hguard (by omega) (by rw [hlen]; exact hal) (by rw [hlen]; exact hbig) hav hcv
      hfe⟩

end Prysm.IndexedAttestation
