import Codec.Segment.Bytes32VectorSpec
import E2eDep.SpecStmt

/-!
# Spec bridge for the real Prysm `v1alpha1.Deposit`

The order of `E2eHb.HbSpec`. Imported, not copied: the `Vector[Bytes32, n]` lemmas for any n (`Codec.Segment.Bytes32VectorSpec`), the
32-byte element lemmas (`E2eHb.HbSpec`), the Deposit_Data spec bridge (`E2e.pdd_*`, `E2eScal/DdSpec.lean`). New here:
the two-field container lemmas (one vector field, one nested container field).
-/

namespace E2eDep
open EthLib.Serialization.Ssz Spec TestTarget E2e E2eHb Codec.Segment

theorem prysmDepDesc_wellFormed : prysmDepDesc.wellFormed = .ok () := by rfl
theorem prysmDepDesc_fixedSize : prysmDepDesc.fixedSize = some 1240 := by rfl

theorem dep_proofs_flatten_length (g : PDep) : g.proofs.flatten.length = 1056 := vN_flatten_length 33 g.proof

theorem dep_enc_size (g : PDep) : (depEnc g).size = 1240 := by
  rw [depEnc, Array.size_append, List.size_toArray, dep_proofs_flatten_length, pdd_enc_size]

theorem dep_toValue_fits (g : PDep) : Value.fits prysmDepDesc g.toValue = true := by
  have h := pdd_toValue_fits g.data
  simp [prysmDepDesc, PDep.toValue, Value.fits, Value.fieldsFit, allFit_map_bv32, h]

theorem dep_toValue_surjective (v : Value) (h : Value.fits prysmDepDesc v = true) : ∃ g : PDep, g.toValue = v := by
  obtain ⟨vs, rfl, hf⟩ := fits_container h
  have hl := fieldsFit_length hf
  match vs, hl with
  | [v0, v1], _ =>
    simp only [fieldsFit_cons] at hf
    obtain ⟨h0, h1, -⟩ := hf
    obtain ⟨es, rfl, hes, hall⟩ : ∃ es, v0 = .seq es ∧ es.length = 33 ∧ Value.allFit (.byteVector 32) es = true := by
      cases v0 <;> simp [Value.fits] at h0 ⊢; exact h0
    obtain ⟨d, rfl⟩ := pdd_toValue_surjective' v1 h1
    refine ⟨⟨⟨(es.map toV32).toArray, by simp [hes]⟩, d⟩, ?_⟩
    simp only [PDep.toValue, Vector.toList_mk, List.toList_toArray]
    rw [allFit_bv32 es hall]

/-- **`serialize g = proof[0] ‖ … ‖ proof[32] ‖ data`.** -/
theorem dep_serialize (g : PDep) : serialize prysmDepDesc g.toValue = .ok (depEnc g) := by
  obtain ⟨pr, d⟩ := g
  have hl1 := vN_flatten_length 33 pr
  have hs1 := vN_serialize 33 (by decide) pr
  have hs2 := pdd_serialize d
  have hl2 := pdd_enc_size d
  simp only [prysmDepDesc, PDep.toValue, serialize, serializeStruct, serializeFields] at hs1 ⊢
  simp only [List.length_map, Vector.length_toList, beq_self_eq_true, ↓reduceIte] at hs1 ⊢
  rw [hs1, hs2]
  simp (config := {decide := true}) [bind, Except.bind, pure, Except.pure, assemble, headWidth, bodyWidth,
    headOf, bodiesOf, Desc.isFixed, Desc.fixedSize, bytesPerOffset, depEnc, PDep.proofs, Desc.fieldsFixedSize,
    Array.append_assoc, hl1, hl2, prysmDdDesc]

/-- **Spec roundtrip.** -/
theorem dep_roundtrip (g : PDep) : deserialize prysmDepDesc (depEnc g) = .ok g.toValue :=
  deserialize_enc (G := PDep) (toV := PDep.toValue) (enc := depEnc) prysmDepDesc_wellFormed dep_serialize
    dep_toValue_fits g

theorem dep_accepted_is_enc {bs : Array UInt8} {v : Value} (h : deserialize prysmDepDesc bs = .ok v) :
    ∃ g : PDep, v = g.toValue ∧ bs = depEnc g :=
  accepted_is_enc (G := PDep) (toV := PDep.toValue) (enc := depEnc) prysmDepDesc_wellFormed dep_serialize
    dep_toValue_surjective h

/-- **EthLib accepts exactly the 1240-byte inputs.** -/
theorem dep_spec_accepts_iff (bs : Array UInt8) : (∃ v, deserialize prysmDepDesc bs = .ok v) ↔ bs.size = 1240 := by
  constructor
  · rintro ⟨v, hd⟩
    obtain ⟨g, rfl, hb⟩ := dep_accepted_is_enc hd
    rw [hb]; exact dep_enc_size g
  · intro h
    obtain ⟨pr, hpr⟩ := vN_of_bytes 33 (bs.extract 0 1056) (by simp; omega)
    obtain ⟨vd, hvd⟩ := (pdd_spec_accepts_iff (bs.extract 1056 1240)).mpr (by simp; omega)
    obtain ⟨d, -, hd⟩ := pdd_accepted_is_enc hvd
    have e : bs = depEnc ⟨pr, d⟩ := by
      simp only [depEnc, PDep.proofs, hpr, ← hd]
      simp (config := {decide := true}) only [Array.extract_append_extract, Nat.min_def, Nat.max_def, ↓reduceIte]
      rw [← h]; simp
    rw [e]
    exact ⟨_, dep_roundtrip _⟩

/-- `len(buf) ≠ 1240`: EthLib rejects. -/
theorem dep_spec_rejects (bs : Array UInt8) (h : bs.size ≠ 1240) : ∃ e, deserialize prysmDepDesc bs = .error e := by
  cases hd : deserialize prysmDepDesc bs with
  | error e => exact ⟨e, rfl⟩
  | ok v => exact absurd ((dep_spec_accepts_iff bs).mp ⟨v, hd⟩) h

end E2eDep
