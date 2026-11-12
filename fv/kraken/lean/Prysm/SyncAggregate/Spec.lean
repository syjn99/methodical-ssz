import Prysm.Checkpoint.Spec
import Prysm.Checkpoint.SpecEquivalence
import EthLib.Serialization.Proofs.Ssz.Codec.Canonical
import EthLib.Serialization.Proofs.Ssz.Codec.RoundTripScalar
import Prysm.SyncCommittee.SpecDefinitions

/-!
# Spec bridge for the real Prysm `v1alpha1.SyncAggregate`

The text of `E2eScal`'s `DdSpec.lean` with the two SyncAggregate fields. The Bitvector[512] field uses two EthLib
theorems: `unpackBits_packBits` (bits → bytes → bits) and `packBits_unpackBits` (bytes → bits → bytes; the
padding premise is empty because 512 = 8 · 64).
-/

namespace Prysm.SyncAggregate
open EthLib.Serialization.Ssz Spec TestTarget

theorem desc_wellFormed : desc.wellFormed = .ok () := by rfl
theorem desc_fixedSize : desc.fixedSize = some 160 := by rfl

theorem encode_size (g : SszValue) : (SszValue.encode g).size = 160 := by
  simp [SszValue.encode]

theorem unpack_size (b : Vector UInt8 64) : (unpackBits b.toArray 512).size = 512 := by
  simp [unpackBits]

/-- 64 bytes → 512 bits → 64 bytes. -/
theorem pack_unpack (b : Vector UInt8 64) : packBits (unpackBits b.toArray 512) 64 = b.toArray := by
  have h := packBits_unpackBits (data := b.toArray) (count := 512) (by
    intro index hi offset ho hc
    simp only [Vector.size_toArray] at hi
    omega)
  simpa using h

theorem toValue_fits (g : SszValue) : Value.fits desc g.toValue = true := by
  simp [desc, SszValue.toValue, Value.fits, Value.fieldsFit, unpackBits]

theorem toValue_surjective (v : Value) (h : Value.fits desc v = true) : ∃ g : SszValue, g.toValue = v := by
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
    simp only [SszValue.toValue, hu]

/-- **`serialize g = bits ‖ signature`.** -/
theorem toValue_serialize (g : SszValue) : serialize desc g.toValue = .ok (SszValue.encode g) := by
  obtain ⟨b, ⟨z, hz⟩⟩ := g
  have hs := unpack_size b
  have hpu := pack_unpack b
  simp only [desc, SszValue.toValue, serialize, serializeStruct, serializeFields, hs, hz,
    bne_self_eq_false, beq_self_eq_true, ↓reduceIte, Nat.reduceAdd, Nat.reduceDiv, hpu]
  simp (config := {decide := true}) [bind, Except.bind, pure, Except.pure, assemble, headWidth, bodyWidth,
    headOf, bodiesOf, Desc.isFixed, Desc.fixedSize, bytesPerOffset, SszValue.encode, Desc.fieldsFixedSize, Array.append_assoc, hz]

/-- **Spec roundtrip.** -/
theorem encode_roundtrip (g : SszValue) : deserialize desc (SszValue.encode g) = .ok g.toValue :=
  deserialize_enc (G := SszValue) (toV := SszValue.toValue) (enc := SszValue.encode) desc_wellFormed toValue_serialize
    toValue_fits g

theorem accepted_is_encode {bs : Array UInt8} {v : Value} (h : deserialize desc bs = .ok v) :
    ∃ g : SszValue, v = g.toValue ∧ bs = SszValue.encode g :=
  accepted_is_enc (G := SszValue) (toV := SszValue.toValue) (enc := SszValue.encode) desc_wellFormed toValue_serialize
    toValue_surjective h

/-- **EthLib accepts exactly the 160-byte inputs.** -/
theorem spec_accepts_iff (bs : Array UInt8) : (∃ v, deserialize desc bs = .ok v) ↔ bs.size = 160 := by
  constructor
  · rintro ⟨v, hd⟩
    obtain ⟨g, rfl, hb⟩ := accepted_is_encode hd
    rw [hb]; exact encode_size g
  · intro h
    let g : SszValue := ⟨⟨bs.extract 0 64, by simp; omega⟩, ⟨bs.extract 64 160, by simp; omega⟩⟩
    have e : bs = SszValue.encode g := by
      simp only [g, SszValue.encode]
      simp (config := {decide := true}) only [Array.extract_append_extract, Nat.min_def, Nat.max_def, ↓reduceIte]
      rw [← h]; simp
    rw [e]
    exact ⟨_, encode_roundtrip g⟩

/-- `len(buf) ≠ 160`: EthLib rejects. -/
theorem spec_rejects (bs : Array UInt8) (h : bs.size ≠ 160) : ∃ e, deserialize desc bs = .error e := by
  cases hd : deserialize desc bs with
  | error e => exact ⟨e, rfl⟩
  | ok v => exact absurd ((spec_accepts_iff bs).mp ⟨v, hd⟩) h

end Prysm.SyncAggregate
