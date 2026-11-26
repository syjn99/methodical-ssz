module

public import Prysm.DataColumnsByRootIdentifier.DecodeRejectSize
public import Prysm.DataColumnsByRootIdentifier.SpecDecodeBridge
public import Prysm.DataColumnsByRootIdentifier.StatementsDecodeSpecReject

@[expose] public section

/-!
# Spec alignment of the DataColumnsByRootIdentifier decoder's size and offset rejects

The statements are `Decode.reject_size_spec_statement` and `Decode.reject_offset_spec_statement`
(`Prysm/DataColumnsByRootIdentifier/StatementsDecodeSpecReject.lean`).
The text of `Prysm/IndexedAttestation/DecodeSpecReject.lean` with the fixed part of 36 bytes and the offset at `bs[32:36]`.
EthLib rejects by `spec_rejects`, because the input fails the first or the second check of `decodeChecks`.
The alignment and overflow rejects have no machine theorem, so this module has no reject completeness theorem.
-/

open Machine Runtime EthLib.Serialization.Ssz Prysm.DataColumnsByRootIdentifier.Code
variable [Host]

namespace Prysm.DataColumnsByRootIdentifier

theorem Decode.reject_size_spec : Decode.reject_size_spec_statement := by
  intro k hk hf bs hbs s ra guard e0 e1 fp s2 hfp h2 R h_mem hguard hlen
  exact ⟨spec_rejects bs (fun h => by have := h.1; omega),
    Decode.reject_size k hk hf s ra guard e0 e1 fp s2 hfp h2 R h_mem hguard (by omega)⟩

theorem Decode.reject_offset_spec : Decode.reject_offset_spec_statement := by
  intro k hk hf bs hbs hoff s ra guard e0 e1 fp s2 hfp h2 R h_mem hguard hlen
  exact ⟨spec_rejects bs (fun h => hoff h.2.1),
    Decode.reject_offset k hk hf s ra guard e0 e1 fp s2 hfp h2 ((bs.toList.drop 32).take 4) (by simp; omega) hoff R
      h_mem hguard (by omega)⟩

end Prysm.DataColumnsByRootIdentifier
