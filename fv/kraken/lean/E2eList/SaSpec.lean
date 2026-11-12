import E2e.Spec
import E2e.SpecEq
import EthLib.Serialization.Proofs.Ssz.Codec.Canonical
import EthLib.Serialization.Proofs.Ssz.Codec.RoundTripScalar
import E2eList.Defs

/-!
# Spec bridge for the real Prysm `v1alpha1.SyncAggregate`

The text of `E2eScal`'s `DdSpec.lean` with the two SyncAggregate fields. The Bitvector[512] field uses two EthLib
theorems: `unpackBits_packBits` (bits → bytes → bits) and `packBits_unpackBits` (bytes → bits → bytes; the
padding premise is empty because 512 = 8 · 64).
-/

namespace E2eList
open EthLib.Serialization.Ssz Fv1

theorem prysmSaDesc_wellFormed : prysmSaDesc.wellFormed = .ok () := by rfl
theorem prysmSaDesc_fixedSize : prysmSaDesc.fixedSize = some 160 := by rfl

theorem psa_enc_size (g : PSa) : (psaEnc g).size = 160 := by
  simp [psaEnc]

theorem psa_unpack_size (b : Vector UInt8 64) : (unpackBits b.toArray 512).size = 512 := by
  simp [unpackBits]

/-- 64 bytes → 512 bits → 64 bytes. -/
theorem psa_pack_unpack (b : Vector UInt8 64) : packBits (unpackBits b.toArray 512) 64 = b.toArray := by
  have h := packBits_unpackBits (data := b.toArray) (count := 512) (by
    intro index hi offset ho hc
    simp only [Vector.size_toArray] at hi
    omega)
  simpa using h

theorem psa_toValue_fits (g : PSa) : Value.fits prysmSaDesc g.toValue = true := by
  simp [prysmSaDesc, PSa.toValue, Value.fits, Value.fieldsFit, unpackBits]

theorem psa_toValue_surjective (v : Value) (h : Value.fits prysmSaDesc v = true) : ∃ g : PSa, g.toValue = v := by
  obtain ⟨vs, rfl, hf⟩ := fits_container h
  have hl := fieldsFit_length hf
  match vs, hl with
  | [v0, v1], _ =>
    simp only [fieldsFit_cons] at hf
    obtain ⟨h0, h1, -⟩ := hf
    obtain ⟨a, rfl, ha⟩ : ∃ a, v0 = .bits a ∧ a.size = 512 := by
      cases v0 <;> simp [Value.fits] at h0 ⊢; exact h0
    obtain ⟨z, rfl, hz⟩ : ∃ d, v1 = .bytes d ∧ d.size = 96 := by
      cases v1 <;> simp [Value.fits] at h1 ⊢; exact h1
    have hp : (packBits a 64).size = 64 := by simp [packBits]
    refine ⟨⟨⟨packBits a 64, hp⟩, ⟨z, hz⟩⟩, ?_⟩
    have hu := unpackBits_packBits a 64 (by omega)
    rw [ha] at hu
    simp only [PSa.toValue, hu]

/-- **`serialize g = bits ‖ signature`.** -/
theorem psa_serialize (g : PSa) : serialize prysmSaDesc g.toValue = .ok (psaEnc g) := by
  obtain ⟨b, ⟨z, hz⟩⟩ := g
  have hs := psa_unpack_size b
  have hpu := psa_pack_unpack b
  simp only [prysmSaDesc, PSa.toValue, serialize, serializeStruct, serializeFields, hs, hz,
    bne_self_eq_false, beq_self_eq_true, ↓reduceIte, Nat.reduceAdd, Nat.reduceDiv, hpu]
  simp (config := {decide := true}) [bind, Except.bind, pure, Except.pure, assemble, headWidth, bodyWidth,
    headOf, bodiesOf, Desc.isFixed, Desc.fixedSize, bytesPerOffset, psaEnc, Desc.fieldsFixedSize, Array.append_assoc, hz]

/-- **Spec roundtrip.** -/
theorem psa_roundtrip (g : PSa) : deserialize prysmSaDesc (psaEnc g) = .ok g.toValue :=
  deserialize_enc (G := PSa) (toV := PSa.toValue) (enc := psaEnc) prysmSaDesc_wellFormed psa_serialize
    psa_toValue_fits g

theorem psa_accepted_is_enc {bs : Array UInt8} {v : Value} (h : deserialize prysmSaDesc bs = .ok v) :
    ∃ g : PSa, v = g.toValue ∧ bs = psaEnc g :=
  accepted_is_enc (G := PSa) (toV := PSa.toValue) (enc := psaEnc) prysmSaDesc_wellFormed psa_serialize
    psa_toValue_surjective h

/-- **EthLib accepts exactly the 160-byte inputs.** -/
theorem psa_spec_accepts_iff (bs : Array UInt8) : (∃ v, deserialize prysmSaDesc bs = .ok v) ↔ bs.size = 160 := by
  constructor
  · rintro ⟨v, hd⟩
    obtain ⟨g, rfl, hb⟩ := psa_accepted_is_enc hd
    rw [hb]; exact psa_enc_size g
  · intro h
    let g : PSa := ⟨⟨bs.extract 0 64, by simp; omega⟩, ⟨bs.extract 64 160, by simp; omega⟩⟩
    have e : bs = psaEnc g := by
      simp only [g, psaEnc]
      simp (config := {decide := true}) only [Array.extract_append_extract, Nat.min_def, Nat.max_def, ↓reduceIte]
      rw [← h]; simp
    rw [e]
    exact ⟨_, psa_roundtrip g⟩

/-- `len(buf) ≠ 160`: EthLib rejects. -/
theorem psa_spec_rejects (bs : Array UInt8) (h : bs.size ≠ 160) : ∃ e, deserialize prysmSaDesc bs = .error e := by
  cases hd : deserialize prysmSaDesc bs with
  | error e => exact ⟨e, rfl⟩
  | ok v => exact absurd ((psa_spec_accepts_iff bs).mp ⟨v, hd⟩) h

end E2eList
