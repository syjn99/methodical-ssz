import E2e.Spec
import E2e.SpecEq
import Fk.LuErr
import EthLib.Serialization.Proofs.Ssz.Codec.Table
import EthLib.Serialization.Proofs.Ssz.Codec.CanonicalTable
import E2eList.IaSpec
import E2eEnc.Spec

/-!
# Decoder-side spec bridge for `DataColumnsByRootIdentifier` (ENC round trip)

The text of `E2eList/IaSpec.lean` (`pia_*`, `iaChecks`) for `PDc`: `toValue` fits, every fitting value is a `PDc`,
the EthLib round trip, accepted inputs are encodings, and the three checks of the Go decoder in its order
(`size ≥ 36`, offset 36, `(size − 36) mod 8 = 0`, `(size − 36)/8 ≤ 128`).
-/

namespace E2eEnc
open EthLib.Serialization.Ssz Fv1

theorem prysmDcDesc_wellFormed : prysmDcDesc.wellFormed = .ok () := by rfl

theorem pdc_toValue_fits (g : PDc) : Value.fits prysmDcDesc g.toValue = true := by
  have h2 := g.hcols
  simp only [prysmDcDesc, PDc.toValue, dcValue, Value.fits, Value.fieldsFit]
  simp [allFit_u64, h2]

theorem pdc_toValue_surjective (v : Value) (h : Value.fits prysmDcDesc v = true) : ∃ g : PDc, g.toValue = v := by
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
theorem pdc_roundtrip (g : PDc) : deserialize prysmDcDesc (pdcEnc g) = .ok g.toValue :=
  deserialize_enc (G := PDc) (toV := PDc.toValue) (enc := pdcEnc) prysmDcDesc_wellFormed pdc_serialize
    pdc_toValue_fits g

theorem pdc_accepted_is_enc {bs : Array UInt8} {v : Value} (h : deserialize prysmDcDesc bs = .ok v) :
    ∃ g : PDc, v = g.toValue ∧ bs = pdcEnc g :=
  accepted_is_enc (G := PDc) (toV := PDc.toValue) (enc := pdcEnc) prysmDcDesc_wellFormed pdc_serialize
    pdc_toValue_surjective h

/-- The checks of the Go decoder, in its order. -/
def dcChecks (bs : Array UInt8) : Prop :=
  36 ≤ bs.size ∧ (bs.toList.drop 32).take 4 = dcOff ∧ (bs.size - 36) % 8 = 0 ∧ (bs.size - 36) / 8 ≤ 128

theorem pdcEnc_checks (g : PDc) : dcChecks (pdcEnc g) := by
  have hs := pdc_enc_size g
  have hl := g.hcols
  refine ⟨by omega, ?_, by omega, by omega⟩
  rw [pdc_enc_toList]
  simp [dcOff]

theorem dc_checks_enc (bs : Array UInt8) (h : dcChecks bs) : ∃ g : PDc, bs = pdcEnc g := by
  obtain ⟨h36, hoff, hmod, hn⟩ := h
  obtain ⟨n, hndef⟩ : ∃ n, n = (bs.size - 36) / 8 := ⟨_, rfl⟩
  have hsz : bs.size = 36 + 8 * n := by omega
  refine ⟨⟨⟨bs.extract 0 32, by simp; omega⟩, luElems bs 36 n, by simp [luElems_length]; omega⟩, ?_⟩
  have h4 : bs.extract 32 36 = dcOff.toArray := by
    apply Array.toList_inj.mp
    simp only [Array.toList_extract, List.extract, ← hoff]
  have e0 : bs.extract 0 32 ++ bs.extract 32 36 = bs.extract 0 36 := extract_join bs (by omega) (by omega)
  have e2 : bs.extract 0 36 ++ bs.extract 36 (36 + 8 * n) = bs.extract 0 bs.size := by
    rw [extract_join bs (by omega) (by omega), ← hsz]
  simp only [pdcEnc, ← h4, u64Bytes_luElems bs n 36 (by omega)]
  rw [e0, e2]; simp

/-- **EthLib accepts exactly the inputs that pass the checks.** -/
theorem pdc_spec_accepts_iff (bs : Array UInt8) : (∃ v, deserialize prysmDcDesc bs = .ok v) ↔ dcChecks bs := by
  constructor
  · rintro ⟨v, hd⟩
    obtain ⟨g, rfl, rfl⟩ := pdc_accepted_is_enc hd
    exact pdcEnc_checks g
  · intro h
    obtain ⟨g, rfl⟩ := dc_checks_enc bs h
    exact ⟨_, pdc_roundtrip g⟩

/-- A failing check makes EthLib reject. -/
theorem pdc_spec_rejects (bs : Array UInt8) (h : ¬ dcChecks bs) : ∃ e, deserialize prysmDcDesc bs = .error e := by
  cases hd : deserialize prysmDcDesc bs with
  | error e => exact ⟨e, rfl⟩
  | ok v => exact absurd ((pdc_spec_accepts_iff bs).mp ⟨v, hd⟩) h

end E2eEnc
