import Prysm.SyncCommittee.Spec
import Prysm.HistoricalBatch.SpecDefinitions

/-!
# Spec bridge for the real Prysm `v1alpha1.HistoricalBatch`

The order of `Prysm.SyncCommittee.Spec`. Imported from it as is: `assemble_inline_ok` (any list of inline parts),
`headWidth_inline`, `bodyWidth_inline`, and EthLib's `concatParts_size`, `concat_fixed_slices`, `deserialize_enc`,
`accepted_is_enc` (through `Spec`). New here: the SyncCommittee lemmas whose statements fix 48-byte elements (`toV48`,
`allFit_bv48`, `allFit_map_bv48`, `serializeEach_bv48`, `concatParts_v48`) with 32, a vector lemma stated once and
used for both fields (`v32_serialize`, `v32_of_bytes`), and the container lemmas for two vector fields.
-/

namespace Prysm.HistoricalBatch
open EthLib.Serialization.Ssz Spec

theorem desc_wellFormed : desc.wellFormed = .ok () := by rfl
theorem desc_fixedSize : desc.fixedSize = some 524288 := by rfl

/-- A total reading of a value as 32 bytes (the zero vector if it is not 32 bytes). -/
def toV32 : Value → Vector UInt8 32
  | .bytes d => if h : d.size = 32 then ⟨d, h⟩ else ⟨Array.replicate 32 0, by simp⟩
  | _ => ⟨Array.replicate 32 0, by simp⟩

theorem allFit_bv32 : ∀ (vs : List Value), Value.allFit (.byteVector 32) vs = true →
    (vs.map toV32).map (fun p => Value.bytes p.toArray) = vs
  | [], _ => rfl
  | v :: vs, h => by
    simp only [Value.allFit, Bool.and_eq_true] at h
    obtain ⟨h0, h1⟩ := h
    simp only [List.map_cons, allFit_bv32 vs h1, List.cons.injEq, and_true]
    cases v <;> simp [Value.fits] at h0
    simp [toV32, h0]

theorem allFit_map_bv32 : ∀ (l : List (Vector UInt8 32)),
    Value.allFit (.byteVector 32) (l.map fun p => Value.bytes p.toArray) = true
  | [] => by simp [Value.allFit]
  | p :: l => by simp [Value.allFit, Value.fits, allFit_map_bv32 l]

theorem serializeEach_bv32 : ∀ (l : List (Vector UInt8 32)),
    serializeEach (.byteVector 32) (l.map fun p => Value.bytes p.toArray) = .ok (l.map (·.toArray))
  | [] => by simp [serializeEach]
  | p :: l => by
    simp only [List.map_cons, serializeEach, serializeEach_bv32 l]
    simp (config := {decide := true}) [serialize, bind, Except.bind, pure, Except.pure, bytesPerOffset]

theorem concatParts_v32 : ∀ (l : List (Vector UInt8 32)),
    concatParts (l.map (·.toArray)) = (l.map (·.toList)).flatten.toArray
  | [] => rfl
  | p :: l => by simp [concatParts, concatParts_v32 l]; rfl

theorem concatParts_v32_size (l : List (Vector UInt8 32)) : (concatParts (l.map (·.toArray))).size = 32 * l.length := by
  rw [concatParts_size 32 _ (by simp)]; simp; omega

theorem v32_flatten_length (v : Vector (Vector UInt8 32) 8192) : (v.toList.map (·.toList)).flatten.length = 262144 := by
  have h := concatParts_v32_size v.toList
  rw [concatParts_v32] at h
  simpa using h

/-- One `Vector[Bytes32, 8192]` field serializes to its elements laid end to end. -/
theorem v32_serialize (v : Vector (Vector UInt8 32) 8192) :
    serialize (.vector (.byteVector 32) 8192) (.seq (v.toList.map fun p => .bytes p.toArray))
      = .ok (v.toList.map (·.toList)).flatten.toArray := by
  have hs := concatParts_v32_size v.toList
  simp only [serialize, List.length_map, Vector.length_toList, beq_self_eq_true, ↓reduceIte, serializeSequence,
    serializeEach_bv32, bind, Except.bind]
  rw [show (v.toList.map (·.toArray)).map (fun _ => Desc.isFixed (.byteVector 32))
      = (v.toList.map (·.toArray)).map (fun _ => true) from rfl,
    Prysm.SyncCommittee.assemble_inline_ok _ (by rw [hs]; simp), concatParts_v32]

/-- Every 262144-byte array is the end-to-end layout of some `Vector[Bytes32, 8192]`. -/
theorem v32_of_bytes (d : Array UInt8) (hd : d.size = 262144) :
    ∃ v : Vector (Vector UInt8 32) 8192, (v.toList.map (·.toList)).flatten.toArray = d := by
  let chunks : List (Vector UInt8 32) := (List.range 8192).map fun i =>
    toV32 (.bytes (d.extract (i * 32) ((i + 1) * 32)))
  refine ⟨⟨chunks.toArray, by simp [chunks]⟩, ?_⟩
  have hm : chunks.map (·.toArray) = (List.range 8192).map (fun i => d.extract (i * 32) ((i + 1) * 32)) := by
    simp only [chunks, List.map_map]
    apply List.map_congr_left
    intro i hi
    simp only [List.mem_range] at hi
    have hsz : (d.extract (i * 32) ((i + 1) * 32)).size = 32 := by simp; omega
    show (toV32 (.bytes (d.extract (i * 32) ((i + 1) * 32)))).toArray = _
    simp only [toV32]
    rw [dif_pos hsz]
  rw [← concatParts_v32]
  have := concat_fixed_slices d 32 8192 (by omega)
  simp only [Vector.toList_mk, List.toList_toArray]
  rw [hm, this, show 8192 * 32 = d.size by omega]
  simp

theorem brs_flatten_length (g : SszValue) : g.brs.flatten.length = 262144 := v32_flatten_length g.blockRoots
theorem srs_flatten_length (g : SszValue) : g.srs.flatten.length = 262144 := v32_flatten_length g.stateRoots

theorem encode_size (g : SszValue) : (SszValue.encode g).size = 524288 := by
  rw [SszValue.encode, Array.size_append, List.size_toArray, List.size_toArray, brs_flatten_length,
    srs_flatten_length]

theorem toValue_fits (g : SszValue) : Value.fits desc g.toValue = true := by
  simp [desc, SszValue.toValue, Value.fits, Value.fieldsFit, allFit_map_bv32]

theorem toValue_surjective (v : Value) (h : Value.fits desc v = true) : ∃ g : SszValue, g.toValue = v := by
  obtain ⟨vs, rfl, hf⟩ := fits_container h
  have hl := fieldsFit_length hf
  match vs, hl with
  | [v0, v1], _ =>
    simp only [fieldsFit_cons] at hf
    obtain ⟨h0, h1, -⟩ := hf
    obtain ⟨es, rfl, hes, hall⟩ : ∃ es, v0 = .seq es ∧ es.length = 8192 ∧ Value.allFit (.byteVector 32) es = true := by
      cases v0 <;> simp [Value.fits] at h0 ⊢; exact h0
    obtain ⟨fs, rfl, hfs, hall2⟩ : ∃ fs, v1 = .seq fs ∧ fs.length = 8192 ∧ Value.allFit (.byteVector 32) fs = true := by
      cases v1 <;> simp [Value.fits] at h1 ⊢; exact h1
    refine ⟨⟨⟨(es.map toV32).toArray, by simp [hes]⟩, ⟨(fs.map toV32).toArray, by simp [hfs]⟩⟩, ?_⟩
    simp only [SszValue.toValue, Vector.toList_mk, List.toList_toArray]
    rw [allFit_bv32 es hall, allFit_bv32 fs hall2]

/-- **`serialize g = blockRoots[0] ‖ … ‖ blockRoots[8191] ‖ stateRoots[0] ‖ … ‖ stateRoots[8191]`.** -/
theorem toValue_serialize (g : SszValue) : serialize desc g.toValue = .ok (SszValue.encode g) := by
  obtain ⟨br, sr⟩ := g
  have hl1 := v32_flatten_length br
  have hl2 := v32_flatten_length sr
  have hs1 := v32_serialize br
  have hs2 := v32_serialize sr
  simp only [desc, SszValue.toValue, serialize, serializeStruct, serializeFields] at hs1 hs2 ⊢
  simp only [List.length_map, Vector.length_toList, beq_self_eq_true, ↓reduceIte] at hs1 hs2 ⊢
  rw [hs1, hs2]
  simp (config := {decide := true}) [bind, Except.bind, pure, Except.pure, assemble, headWidth, bodyWidth,
    headOf, bodiesOf, Desc.isFixed, Desc.fixedSize, bytesPerOffset, SszValue.encode, SszValue.brs, SszValue.srs, Desc.fieldsFixedSize,
    Array.append_assoc, hl1, hl2]

/-- **Spec roundtrip.** -/
theorem encode_roundtrip (g : SszValue) : deserialize desc (SszValue.encode g) = .ok g.toValue :=
  deserialize_enc (G := SszValue) (toV := SszValue.toValue) (enc := SszValue.encode) desc_wellFormed toValue_serialize
    toValue_fits g

theorem accepted_is_encode {bs : Array UInt8} {v : Value} (h : deserialize desc bs = .ok v) :
    ∃ g : SszValue, v = g.toValue ∧ bs = SszValue.encode g :=
  accepted_is_enc (G := SszValue) (toV := SszValue.toValue) (enc := SszValue.encode) desc_wellFormed toValue_serialize
    toValue_surjective h

/-- **EthLib accepts exactly the 524288-byte inputs.** -/
theorem spec_accepts_iff (bs : Array UInt8) : (∃ v, deserialize desc bs = .ok v) ↔ bs.size = 524288 := by
  constructor
  · rintro ⟨v, hd⟩
    obtain ⟨g, rfl, hb⟩ := accepted_is_encode hd
    rw [hb]; exact encode_size g
  · intro h
    obtain ⟨v1, hv1⟩ := v32_of_bytes (bs.extract 0 262144) (by simp; omega)
    obtain ⟨v2, hv2⟩ := v32_of_bytes (bs.extract 262144 524288) (by simp; omega)
    have e : bs = SszValue.encode ⟨v1, v2⟩ := by
      simp only [SszValue.encode, SszValue.brs, SszValue.srs, hv1, hv2]
      simp (config := {decide := true}) only [Array.extract_append_extract, Nat.min_def, Nat.max_def, ↓reduceIte]
      rw [← h]; simp
    rw [e]
    exact ⟨_, encode_roundtrip _⟩

/-- `len(buf) ≠ 524288`: EthLib rejects. -/
theorem spec_rejects (bs : Array UInt8) (h : bs.size ≠ 524288) : ∃ e, deserialize desc bs = .error e := by
  cases hd : deserialize desc bs with
  | error e => exact ⟨e, rfl⟩
  | ok v => exact absurd ((spec_accepts_iff bs).mp ⟨v, hd⟩) h

end Prysm.HistoricalBatch
