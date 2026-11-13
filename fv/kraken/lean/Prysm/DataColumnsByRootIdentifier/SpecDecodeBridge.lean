import Prysm.Checkpoint.Spec
import Prysm.Checkpoint.SpecEquivalence
import Codec.ReadUint64List
import EthLib.Serialization.Proofs.Ssz.Codec.Table
import EthLib.Serialization.Proofs.Ssz.Codec.CanonicalTable
import Prysm.IndexedAttestation.Spec
import Prysm.DataColumnsByRootIdentifier.Spec

/-!
# Decoder-side spec bridge for `DataColumnsByRootIdentifier` (round trip)

The text of `Prysm/IndexedAttestation/Spec.lean` (`pia_*`, `iaChecks`) for `SszValue`: `toValue` fits, every fitting value is a `SszValue`,
the EthLib round trip, accepted inputs are encodings, and the three checks of the Go decoder in its order
(`size ≥ 36`, offset 36, `(size − 36) mod 8 = 0`, `(size − 36)/8 ≤ 128`).
-/

namespace Prysm.DataColumnsByRootIdentifier
open EthLib.Serialization.Ssz Spec

theorem desc_wellFormed : desc.wellFormed = .ok () := by rfl

theorem toValue_fits (g : SszValue) : Value.fits desc g.toValue = true := by
  have h2 := g.hcols
  simp only [desc, SszValue.toValue, receiverValue, Value.fits, Value.fieldsFit]
  simp [allFit_u64, h2]

theorem toValue_surjective (v : Value) (h : Value.fits desc v = true) : ∃ g : SszValue, g.toValue = v := by
  obtain ⟨vs, rfl, hf⟩ := fits_container h
  have hl := fieldsFit_length hf
  match vs, hl with
  | [v0, v1], _ =>
    simp only [fieldsFit_cons] at hf
    obtain ⟨h0, h1, -⟩ := hf
    obtain ⟨z, rfl, hz⟩ : ∃ d, v0 = .bytes d ∧ d.size = 32 := by
      cases v0 <;> simp [Value.fits] at h0 ⊢; exact h0
    obtain ⟨es, rfl, hlen, hall⟩ : ∃ es, v1 = .seq es ∧ es.length ≤ 128 ∧ Value.allFit (.uint 8) es = true := by
      cases v1 <;> simp [Value.fits] at h1 ⊢; exact h1
    obtain ⟨l, rfl⟩ := allFit_u64_inv es hall
    exact ⟨⟨⟨z, hz⟩, l, by simpa using hlen⟩, rfl⟩

/-- **Spec roundtrip.** -/
theorem encode_roundtrip (g : SszValue) : deserialize desc (SszValue.encode g) = .ok g.toValue :=
  deserialize_encoding (G := SszValue) (toV := SszValue.toValue) (enc := SszValue.encode) desc_wellFormed toValue_serialize
    toValue_fits g

theorem accepted_is_encode {bs : Array UInt8} {v : Value} (h : deserialize desc bs = .ok v) :
    ∃ g : SszValue, v = g.toValue ∧ bs = SszValue.encode g :=
  accepted_input_is_encoding (G := SszValue) (toV := SszValue.toValue) (enc := SszValue.encode) desc_wellFormed toValue_serialize
    toValue_surjective h

/-- The checks of the Go decoder, in its order. -/
def decodeChecks (bs : Array UInt8) : Prop :=
  36 ≤ bs.size ∧ (bs.toList.drop 32).take 4 = offsetBytes ∧ (bs.size - 36) % 8 = 0 ∧ (bs.size - 36) / 8 ≤ 128

theorem encode_decodeChecks (g : SszValue) : decodeChecks (SszValue.encode g) := by
  have hs := encode_size g
  have hl := g.hcols
  refine ⟨by omega, ?_, by omega, by omega⟩
  rw [encode_toList]
  simp [offsetBytes]

theorem decodeChecks_encode (bs : Array UInt8) (h : decodeChecks bs) : ∃ g : SszValue, bs = SszValue.encode g := by
  obtain ⟨h36, hoff, hmod, hn⟩ := h
  obtain ⟨n, hndef⟩ : ∃ n, n = (bs.size - 36) / 8 := ⟨_, rfl⟩
  have hsz : bs.size = 36 + 8 * n := by omega
  refine ⟨⟨⟨bs.extract 0 32, by simp; omega⟩, Codec.readUint64List bs 36 n, by simp [Codec.readUint64List_length]; omega⟩, ?_⟩
  have h4 : bs.extract 32 36 = offsetBytes.toArray := by
    apply Array.toList_inj.mp
    simp only [Array.toList_extract, List.extract, ← hoff]
  have e0 : bs.extract 0 32 ++ bs.extract 32 36 = bs.extract 0 36 := extract_join bs (by omega) (by omega)
  have e2 : bs.extract 0 36 ++ bs.extract 36 (36 + 8 * n) = bs.extract 0 bs.size := by
    rw [extract_join bs (by omega) (by omega), ← hsz]
  simp only [SszValue.encode, ← h4, Codec.u64Bytes_readUint64List bs n 36 (by omega)]
  rw [e0, e2]; simp

/-- **EthLib accepts exactly the inputs that pass the checks.** -/
theorem spec_accepts_iff (bs : Array UInt8) : (∃ v, deserialize desc bs = .ok v) ↔ decodeChecks bs := by
  constructor
  · rintro ⟨v, hd⟩
    obtain ⟨g, rfl, rfl⟩ := accepted_is_encode hd
    exact encode_decodeChecks g
  · intro h
    obtain ⟨g, rfl⟩ := decodeChecks_encode bs h
    exact ⟨_, encode_roundtrip g⟩

/-- A failing check makes EthLib reject. -/
theorem spec_rejects (bs : Array UInt8) (h : ¬ decodeChecks bs) : ∃ e, deserialize desc bs = .error e := by
  cases hd : deserialize desc bs with
  | error e => exact ⟨e, rfl⟩
  | ok v => exact absurd ((spec_accepts_iff bs).mp ⟨v, hd⟩) h

end Prysm.DataColumnsByRootIdentifier
