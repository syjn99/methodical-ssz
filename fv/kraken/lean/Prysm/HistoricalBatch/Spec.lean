import Prysm.SyncCommittee.Spec
import Prysm.HistoricalBatch.SpecDefinitions
import Codec.ByteVector32Values

/-!
# Spec bridge for the real Prysm `v1alpha1.HistoricalBatch`

The order of `Prysm.SyncCommittee.Spec`. Imported as is: `Codec.assemble_inline_ok` (any list of inline parts),
`Codec.headWidth_inline`, `Codec.bodyWidth_inline` (`Codec/SerializeInline.lean`), and EthLib's `concatParts_size`, `concat_fixed_slices`, `deserialize_encoding`,
`accepted_input_is_encoding` (through `Spec`). New here: the SyncCommittee lemmas whose statements fix 48-byte elements (`toByteVector48`,
`allFit_byteVector48`, `allFit_map_byteVector48`, `serializeEach_byteVector48`, `concatParts_byteVector48`) with 32, a vector lemma stated once and
used for both fields (`roots_vector_serialize`, `roots_vector_of_bytes`), and the container lemmas for two vector fields.
The 32-byte helpers are `Codec.toByteVector32`, `Codec.allFit_byteVector32` and `Codec.allFit_map_byteVector32`
(`Codec/ByteVector32Values.lean`).
-/

namespace Prysm.HistoricalBatch
open EthLib.Serialization.Ssz Spec

theorem desc_wellFormed : desc.wellFormed = .ok () := by rfl
theorem desc_fixedSize : desc.fixedSize = some 524288 := by rfl

theorem serializeEach_byteVector32 : ∀ (l : List (Vector UInt8 32)),
    serializeEach (.byteVector 32) (l.map fun p => Value.bytes p.toArray) = .ok (l.map (·.toArray))
  | [] => by simp [serializeEach]
  | p :: l => by
    simp only [List.map_cons, serializeEach, serializeEach_byteVector32 l]
    simp (config := {decide := true}) [serialize, bind, Except.bind, pure, Except.pure, bytesPerOffset]

theorem concatParts_byteVector32 : ∀ (l : List (Vector UInt8 32)),
    concatParts (l.map (·.toArray)) = (l.map (·.toList)).flatten.toArray
  | [] => rfl
  | p :: l => by simp [concatParts, concatParts_byteVector32 l]; rfl

theorem concatParts_byteVector32_size (l : List (Vector UInt8 32)) : (concatParts (l.map (·.toArray))).size = 32 * l.length := by
  rw [concatParts_size 32 _ (by simp)]; simp; omega

theorem roots_vector_flatten_length (v : Vector (Vector UInt8 32) 8192) : (v.toList.map (·.toList)).flatten.length = 262144 := by
  have h := concatParts_byteVector32_size v.toList
  rw [concatParts_byteVector32] at h
  simpa using h

/-- One `Vector[Bytes32, 8192]` field serializes to its elements laid end to end. -/
theorem roots_vector_serialize (v : Vector (Vector UInt8 32) 8192) :
    serialize (.vector (.byteVector 32) 8192) (.seq (v.toList.map fun p => .bytes p.toArray))
      = .ok (v.toList.map (·.toList)).flatten.toArray := by
  have hs := concatParts_byteVector32_size v.toList
  simp only [serialize, List.length_map, Vector.length_toList, beq_self_eq_true, ↓reduceIte, serializeSequence,
    serializeEach_byteVector32, bind, Except.bind]
  rw [show (v.toList.map (·.toArray)).map (fun _ => Desc.isFixed (.byteVector 32))
      = (v.toList.map (·.toArray)).map (fun _ => true) from rfl,
    Codec.assemble_inline_ok _ (by rw [hs]; simp), concatParts_byteVector32]

/-- Every 262144-byte array is the end-to-end layout of some `Vector[Bytes32, 8192]`. -/
theorem roots_vector_of_bytes (d : Array UInt8) (hd : d.size = 262144) :
    ∃ v : Vector (Vector UInt8 32) 8192, (v.toList.map (·.toList)).flatten.toArray = d := by
  let chunks : List (Vector UInt8 32) := (List.range 8192).map fun i =>
    Codec.toByteVector32 (.bytes (d.extract (i * 32) ((i + 1) * 32)))
  refine ⟨⟨chunks.toArray, by simp [chunks]⟩, ?_⟩
  have hm : chunks.map (·.toArray) = (List.range 8192).map (fun i => d.extract (i * 32) ((i + 1) * 32)) := by
    simp only [chunks, List.map_map]
    apply List.map_congr_left
    intro i hi
    simp only [List.mem_range] at hi
    have hsz : (d.extract (i * 32) ((i + 1) * 32)).size = 32 := by simp; omega
    show (Codec.toByteVector32 (.bytes (d.extract (i * 32) ((i + 1) * 32)))).toArray = _
    simp only [Codec.toByteVector32]
    rw [dif_pos hsz]
  rw [← concatParts_byteVector32]
  have := concat_fixed_slices d 32 8192 (by omega)
  simp only [Vector.toList_mk, List.toList_toArray]
  rw [hm, this, show 8192 * 32 = d.size by omega]
  simp

theorem blockRootBytes_flatten_length (g : SszValue) : g.blockRootBytes.flatten.length = 262144 := roots_vector_flatten_length g.blockRoots
theorem stateRootBytes_flatten_length (g : SszValue) : g.stateRootBytes.flatten.length = 262144 := roots_vector_flatten_length g.stateRoots

theorem encode_size (g : SszValue) : (SszValue.encode g).size = 524288 := by
  rw [SszValue.encode, Array.size_append, List.size_toArray, List.size_toArray, blockRootBytes_flatten_length,
    stateRootBytes_flatten_length]

theorem toValue_fits (g : SszValue) : Value.fits desc g.toValue = true := by
  simp [desc, SszValue.toValue, Value.fits, Value.fieldsFit, Codec.allFit_map_byteVector32]

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
    refine ⟨⟨⟨(es.map Codec.toByteVector32).toArray, by simp [hes]⟩, ⟨(fs.map Codec.toByteVector32).toArray, by simp [hfs]⟩⟩, ?_⟩
    simp only [SszValue.toValue, Vector.toList_mk, List.toList_toArray]
    rw [Codec.allFit_byteVector32 es hall, Codec.allFit_byteVector32 fs hall2]

/-- **`serialize g = blockRoots[0] ‖ … ‖ blockRoots[8191] ‖ stateRoots[0] ‖ … ‖ stateRoots[8191]`.** -/
theorem toValue_serialize (g : SszValue) : serialize desc g.toValue = .ok (SszValue.encode g) := by
  obtain ⟨br, sr⟩ := g
  have hl1 := roots_vector_flatten_length br
  have hl2 := roots_vector_flatten_length sr
  have hs1 := roots_vector_serialize br
  have hs2 := roots_vector_serialize sr
  simp only [desc, SszValue.toValue, serialize, serializeStruct, serializeFields] at hs1 hs2 ⊢
  simp only [List.length_map, Vector.length_toList, beq_self_eq_true, ↓reduceIte] at hs1 hs2 ⊢
  rw [hs1, hs2]
  simp (config := {decide := true}) [bind, Except.bind, pure, Except.pure, assemble, headWidth, bodyWidth,
    headOf, bodiesOf, Desc.isFixed, Desc.fixedSize, bytesPerOffset, SszValue.encode, SszValue.blockRootBytes, SszValue.stateRootBytes, Desc.fieldsFixedSize,
    Array.append_assoc, hl1, hl2]

/-- **Spec roundtrip.** -/
theorem encode_roundtrip (g : SszValue) : deserialize desc (SszValue.encode g) = .ok g.toValue :=
  deserialize_encoding (G := SszValue) (toV := SszValue.toValue) (enc := SszValue.encode) desc_wellFormed toValue_serialize
    toValue_fits g

theorem accepted_is_encode {bs : Array UInt8} {v : Value} (h : deserialize desc bs = .ok v) :
    ∃ g : SszValue, v = g.toValue ∧ bs = SszValue.encode g :=
  accepted_input_is_encoding (G := SszValue) (toV := SszValue.toValue) (enc := SszValue.encode) desc_wellFormed toValue_serialize
    toValue_surjective h

/-- **EthLib accepts exactly the 524288-byte inputs.** -/
theorem spec_accepts_iff (bs : Array UInt8) : (∃ v, deserialize desc bs = .ok v) ↔ bs.size = 524288 := by
  constructor
  · rintro ⟨v, hd⟩
    obtain ⟨g, rfl, hb⟩ := accepted_is_encode hd
    rw [hb]; exact encode_size g
  · intro h
    obtain ⟨v1, hv1⟩ := roots_vector_of_bytes (bs.extract 0 262144) (by simp; omega)
    obtain ⟨v2, hv2⟩ := roots_vector_of_bytes (bs.extract 262144 524288) (by simp; omega)
    have e : bs = SszValue.encode ⟨v1, v2⟩ := by
      simp only [SszValue.encode, SszValue.blockRootBytes, SszValue.stateRootBytes, hv1, hv2]
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
