import Codec.Segment.Bytes32VectorSpec
import Prysm.Deposit.StatementsSpec

/-!
# Spec bridge for the real Prysm `v1alpha1.Deposit`

The order of `Prysm.HistoricalBatch.Spec`. Imported, not copied: the `Vector[Bytes32, n]` lemmas for any n (`Codec.Segment.Bytes32VectorSpec`), the
32-byte element lemmas (`Prysm.HistoricalBatch.Spec`), the Deposit_Data spec bridge (`Prysm.Deposit_Data.SszValue.*`, `Prysm/Deposit_Data/Spec.lean`). New here:
the two-field container lemmas (one vector field, one nested container field).
-/

namespace Prysm.Deposit
open EthLib.Serialization.Ssz Spec Codec.Segment

theorem desc_wellFormed : desc.wellFormed = .ok () := by rfl
theorem desc_fixedSize : desc.fixedSize = some 1240 := by rfl

theorem proofs_flatten_length (g : SszValue) : g.proofs.flatten.length = 1056 := vN_flatten_length 33 g.proof

theorem encode_size (g : SszValue) : (SszValue.encode g).size = 1240 := by
  rw [SszValue.encode, Array.size_append, List.size_toArray, proofs_flatten_length, Prysm.Deposit_Data.SszValue.enc_size]

theorem toValue_fits (g : SszValue) : Value.fits desc g.toValue = true := by
  have h := Prysm.Deposit_Data.SszValue.toValue_fits g.data
  simp [desc, SszValue.toValue, Value.fits, Value.fieldsFit, Prysm.HistoricalBatch.allFit_map_bv32, h]

theorem toValue_surjective (v : Value) (h : Value.fits desc v = true) : ∃ g : SszValue, g.toValue = v := by
  obtain ⟨vs, rfl, hf⟩ := fits_container h
  have hl := fieldsFit_length hf
  match vs, hl with
  | [v0, v1], _ =>
    simp only [fieldsFit_cons] at hf
    obtain ⟨h0, h1, -⟩ := hf
    obtain ⟨es, rfl, hes, hall⟩ : ∃ es, v0 = .seq es ∧ es.length = 33 ∧ Value.allFit (.byteVector 32) es = true := by
      cases v0 <;> simp [Value.fits] at h0 ⊢; exact h0
    obtain ⟨d, rfl⟩ := Prysm.Deposit_Data.SszValue.toValue_surjective' v1 h1
    refine ⟨⟨⟨(es.map Prysm.HistoricalBatch.toV32).toArray, by simp [hes]⟩, d⟩, ?_⟩
    simp only [SszValue.toValue, Vector.toList_mk, List.toList_toArray]
    rw [Prysm.HistoricalBatch.allFit_bv32 es hall]

/-- **`serialize g = proof[0] ‖ … ‖ proof[32] ‖ data`.** -/
theorem toValue_serialize (g : SszValue) : serialize desc g.toValue = .ok (SszValue.encode g) := by
  obtain ⟨pr, d⟩ := g
  have hl1 := vN_flatten_length 33 pr
  have hs1 := vN_serialize 33 (by decide) pr
  have hs2 := Prysm.Deposit_Data.SszValue.serialize_eq d
  have hl2 := Prysm.Deposit_Data.SszValue.enc_size d
  simp only [desc, SszValue.toValue, serialize, serializeStruct, serializeFields] at hs1 ⊢
  simp only [List.length_map, Vector.length_toList, beq_self_eq_true, ↓reduceIte] at hs1 ⊢
  rw [hs1, hs2]
  simp (config := {decide := true}) [bind, Except.bind, pure, Except.pure, assemble, headWidth, bodyWidth,
    headOf, bodiesOf, Desc.isFixed, Desc.fixedSize, bytesPerOffset, SszValue.encode, SszValue.proofs, Desc.fieldsFixedSize,
    Array.append_assoc, hl1, hl2, Prysm.Deposit_Data.desc]

/-- **Spec roundtrip.** -/
theorem encode_roundtrip (g : SszValue) : deserialize desc (SszValue.encode g) = .ok g.toValue :=
  deserialize_enc (G := SszValue) (toV := SszValue.toValue) (enc := SszValue.encode) desc_wellFormed toValue_serialize
    toValue_fits g

theorem accepted_is_encode {bs : Array UInt8} {v : Value} (h : deserialize desc bs = .ok v) :
    ∃ g : SszValue, v = g.toValue ∧ bs = SszValue.encode g :=
  accepted_is_enc (G := SszValue) (toV := SszValue.toValue) (enc := SszValue.encode) desc_wellFormed toValue_serialize
    toValue_surjective h

/-- **EthLib accepts exactly the 1240-byte inputs.** -/
theorem spec_accepts_iff (bs : Array UInt8) : (∃ v, deserialize desc bs = .ok v) ↔ bs.size = 1240 := by
  constructor
  · rintro ⟨v, hd⟩
    obtain ⟨g, rfl, hb⟩ := accepted_is_encode hd
    rw [hb]; exact encode_size g
  · intro h
    obtain ⟨pr, hpr⟩ := vN_of_bytes 33 (bs.extract 0 1056) (by simp; omega)
    obtain ⟨vd, hvd⟩ := (Prysm.Deposit_Data.SszValue.spec_accepts_iff (bs.extract 1056 1240)).mpr (by simp; omega)
    obtain ⟨d, -, hd⟩ := Prysm.Deposit_Data.SszValue.accepted_is_encoding hvd
    have e : bs = SszValue.encode ⟨pr, d⟩ := by
      simp only [SszValue.encode, SszValue.proofs, hpr, ← hd]
      simp (config := {decide := true}) only [Array.extract_append_extract, Nat.min_def, Nat.max_def, ↓reduceIte]
      rw [← h]; simp
    rw [e]
    exact ⟨_, encode_roundtrip _⟩

/-- `len(buf) ≠ 1240`: EthLib rejects. -/
theorem spec_rejects (bs : Array UInt8) (h : bs.size ≠ 1240) : ∃ e, deserialize desc bs = .error e := by
  cases hd : deserialize desc bs with
  | error e => exact ⟨e, rfl⟩
  | ok v => exact absurd ((spec_accepts_iff bs).mp ⟨v, hd⟩) h

end Prysm.Deposit
