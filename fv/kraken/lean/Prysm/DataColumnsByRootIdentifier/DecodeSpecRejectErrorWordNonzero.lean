import Prysm.DataColumnsByRootIdentifier.DecodeRejectAlignment
import Prysm.DataColumnsByRootIdentifier.DecodeRejectOverflow
import Prysm.DataColumnsByRootIdentifier.SpecDecodeBridge
import Prysm.DataColumnsByRootIdentifier.StatementsDecodeSpecRejectErrorWordNonzero

/-!
# Spec alignment of the DataColumnsByRootIdentifier alignment reject and overflow reject

Statements: `Decode.reject_alignment_spec_error_word_nonzero_statement` and `Decode.reject_overflow_spec_error_word_nonzero_statement`
(`Prysm/DataColumnsByRootIdentifier/StatementsDecodeSpecRejectErrorWordNonzero.lean`).
EthLib rejects by `spec_rejects`, because the input fails the third or the fourth check of `decodeChecks`.
The machine code returns the `fmt.errorf` error (`Decode.reject_alignment_error_word_nonzero`, `Decode.reject_overflow_error_word_nonzero`).
The root bytes are `bs[0:32]` and the offset bytes are `bs[32:36]`.
-/

open Machine Runtime EthLib.Serialization.Ssz
variable [Host]

namespace Prysm.DataColumnsByRootIdentifier

theorem Decode.reject_alignment_spec_error_word_nonzero : Decode.reject_alignment_spec_error_word_nonzero_statement := by
  intro k hk hf bs hbs hoff hmis s ra guard e0 e1 esp msg ity he0 he0nz hity fp s1 s2 s3 s4 l28 l38 l40 aw spl rslot lo
    aP1 aL1 aC1 hfp h1 h2 h3 h4 hl28 hl38 hl40 haw hspl hrs haP1 haL1 haC1 S hlo Heap avail R h_mem hguard hlen hav hms hmm
    hcv hfe
  rw [hoff] at h_mem ⊢
  exact ⟨spec_rejects bs (fun h => hmis h.2.2.1),
    Decode.reject_alignment_error_word_nonzero k hk hf (bs.toList.take 32) (by simp; omega) s ra guard e0 e1 esp msg ity
      he0 he0nz hity fp s1 s2 s3 s4 l28 l38 l40 aw spl rslot lo aP1 aL1 aC1 hfp h1 h2 h3 h4 hl28 hl38 hl40 haw hspl hrs
      haP1 haL1 haC1 S hlo Heap avail R h_mem hguard (by omega) (by rw [hlen]; exact hmis) hav hms hmm hcv hfe⟩

theorem Decode.reject_overflow_spec_error_word_nonzero : Decode.reject_overflow_spec_error_word_nonzero_statement := by
  intro k hk hf bs hbs hoff hal hbig s ra guard e0 e1 esp msg ity he0 he0nz hity fp s1 s2 s3 s4 l28 l38 l40 aw spl rslot lo
    aP1 aL1 aC1 hfp h1 h2 h3 h4 hl28 hl38 hl40 haw hspl hrs haP1 haL1 haC1 S hlo Heap avail R h_mem hguard hlen hav hms hmm
    hcv hfe
  rw [hoff] at h_mem ⊢
  exact ⟨spec_rejects bs (fun h => by have := h.2.2.2; omega),
    Decode.reject_overflow_error_word_nonzero k hk hf (bs.toList.take 32) (by simp; omega) s ra guard e0 e1 esp msg ity
      he0 he0nz hity fp s1 s2 s3 s4 l28 l38 l40 aw spl rslot lo aP1 aL1 aC1 hfp h1 h2 h3 h4 hl28 hl38 hl40 haw hspl hrs
      haP1 haL1 haC1 S hlo Heap avail R h_mem hguard (by omega) (by rw [hlen]; exact hal) (by rw [hlen]; exact hbig) hav hms
      hmm hcv hfe⟩

end Prysm.DataColumnsByRootIdentifier
