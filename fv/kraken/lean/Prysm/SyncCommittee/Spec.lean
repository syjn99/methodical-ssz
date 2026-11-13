import Prysm.Checkpoint.Spec
import Prysm.Checkpoint.SpecEquivalence
import EthLib.Serialization.Proofs.Ssz.Codec.Table
import EthLib.Serialization.Proofs.Ssz.Codec.CanonicalTable
import Prysm.SyncCommittee.SpecDefinitions

/-!
# Spec bridge for the real Prysm `v1alpha1.SyncCommittee`

The order of `Prysm/Deposit_Data/Spec.lean`. The Vector[Bytes48, 512] field is not unfolded element by element: the
lemmas below are stated for any list of 48-byte vectors (`serializeEach_bv48`, `assemble_inline_ok`,
`concatParts_v48`) and use EthLib's `headOf_inline`, `bodiesOf_inline` and `concat_fixed_slices`.
-/

namespace Prysm.SyncCommittee
open EthLib.Serialization.Ssz Spec

theorem desc_wellFormed : desc.wellFormed = .ok () := by rfl
theorem desc_fixedSize : desc.fixedSize = some 24624 := by rfl

/-- A total reading of a value as 48 bytes (the zero vector if it is not 48 bytes). -/
def toV48 : Value → Vector UInt8 48
  | .bytes d => if h : d.size = 48 then ⟨d, h⟩ else ⟨Array.replicate 48 0, by simp⟩
  | _ => ⟨Array.replicate 48 0, by simp⟩

theorem allFit_bv48 : ∀ (vs : List Value), Value.allFit (.byteVector 48) vs = true →
    (vs.map toV48).map (fun p => Value.bytes p.toArray) = vs
  | [], _ => rfl
  | v :: vs, h => by
    simp only [Value.allFit, Bool.and_eq_true] at h
    obtain ⟨h0, h1⟩ := h
    simp only [List.map_cons, allFit_bv48 vs h1, List.cons.injEq, and_true]
    cases v <;> simp [Value.fits] at h0
    simp [toV48, h0]

theorem allFit_map_bv48 : ∀ (l : List (Vector UInt8 48)),
    Value.allFit (.byteVector 48) (l.map fun p => Value.bytes p.toArray) = true
  | [] => by simp [Value.allFit]
  | p :: l => by simp [Value.allFit, Value.fits, allFit_map_bv48 l]

theorem serializeEach_bv48 : ∀ (l : List (Vector UInt8 48)),
    serializeEach (.byteVector 48) (l.map fun p => Value.bytes p.toArray) = .ok (l.map (·.toArray))
  | [] => by simp [serializeEach]
  | p :: l => by
    simp only [List.map_cons, serializeEach, serializeEach_bv48 l]
    simp (config := {decide := true}) [serialize, bind, Except.bind, pure, Except.pure, bytesPerOffset]

theorem headWidth_inline : ∀ (parts : List Bytes),
    headWidth ((parts.map fun _ => true).zip parts) = (concatParts parts).size
  | [] => rfl
  | p :: ps => by simp [headWidth, concatParts, headWidth_inline ps]

theorem bodyWidth_inline : ∀ (parts : List Bytes), bodyWidth ((parts.map fun _ => true).zip parts) = 0
  | [] => rfl
  | p :: ps => by simp [bodyWidth, bodyWidth_inline ps]

theorem assemble_inline_ok (parts : List Bytes) (h : (concatParts parts).size < 2 ^ 32) :
    assemble (parts.map fun _ => true) parts = .ok (concatParts parts) := by
  have h1 := headWidth_inline parts
  have h2 := bodyWidth_inline parts
  have h3 := headOf_inline parts
  have h4 := bodiesOf_inline parts
  simp only [assemble, h1, h2, bytesPerOffset]
  simp only [Nat.add_zero, show ¬ (concatParts parts).size ≥ 2 ^ (8 * 4) by omega, ↓reduceIte, pure, Except.pure]
  rw [h3, h4, Array.append_empty]

theorem concatParts_v48 : ∀ (l : List (Vector UInt8 48)),
    concatParts (l.map (·.toArray)) = (l.map (·.toList)).flatten.toArray
  | [] => rfl
  | p :: l => by simp [concatParts, concatParts_v48 l]; rfl

theorem concatParts_v48_size (l : List (Vector UInt8 48)) : (concatParts (l.map (·.toArray))).size = 48 * l.length := by
  rw [concatParts_size 48 _ (by simp)]; simp; omega

theorem pks_flatten_length (g : SszValue) : g.pks.flatten.length = 24576 := by
  have h := concatParts_v48_size g.pubkeys.toList
  rw [concatParts_v48] at h
  simpa [SszValue.pks] using h

theorem encode_size (g : SszValue) : (SszValue.encode g).size = 24624 := by
  rw [SszValue.encode, Array.size_append, List.size_toArray, pks_flatten_length]; simp

theorem seq_serialize (g : SszValue) :
    serialize (.vector (.byteVector 48) 512) (.seq (g.pubkeys.toList.map fun p => .bytes p.toArray))
      = .ok g.pks.flatten.toArray := by
  have hs := concatParts_v48_size g.pubkeys.toList
  simp only [serialize, List.length_map, Vector.length_toList, beq_self_eq_true, ↓reduceIte, serializeSequence,
    serializeEach_bv48, bind, Except.bind]
  rw [show (g.pubkeys.toList.map (·.toArray)).map (fun _ => Desc.isFixed (.byteVector 48))
      = (g.pubkeys.toList.map (·.toArray)).map (fun _ => true) from rfl,
    assemble_inline_ok _ (by rw [hs]; simp), concatParts_v48]
  rfl

theorem toValue_fits (g : SszValue) : Value.fits desc g.toValue = true := by
  simp [desc, SszValue.toValue, Value.fits, Value.fieldsFit, allFit_map_bv48]

theorem toValue_surjective (v : Value) (h : Value.fits desc v = true) : ∃ g : SszValue, g.toValue = v := by
  obtain ⟨vs, rfl, hf⟩ := fits_container h
  have hl := fieldsFit_length hf
  match vs, hl with
  | [v0, v1], _ =>
    simp only [fieldsFit_cons] at hf
    obtain ⟨h0, h1, -⟩ := hf
    obtain ⟨es, rfl, hes, hall⟩ : ∃ es, v0 = .seq es ∧ es.length = 512 ∧ Value.allFit (.byteVector 48) es = true := by
      cases v0 <;> simp [Value.fits] at h0 ⊢; exact h0
    obtain ⟨z, rfl, hz⟩ : ∃ d, v1 = .bytes d ∧ d.size = 48 := by
      cases v1 <;> simp [Value.fits] at h1 ⊢; exact h1
    refine ⟨⟨⟨(es.map toV48).toArray, by simp [hes]⟩, ⟨z, hz⟩⟩, ?_⟩
    simp only [SszValue.toValue, Vector.toList_mk, List.toList_toArray]
    rw [allFit_bv48 es hall]

/-- **`serialize g = pubkeys[0] ‖ … ‖ pubkeys[511] ‖ aggregatePubkey`.** -/
theorem toValue_serialize (g : SszValue) : serialize desc g.toValue = .ok (SszValue.encode g) := by
  obtain ⟨pk, ⟨z, hz⟩⟩ := g
  have hfl := pks_flatten_length ⟨pk, ⟨z, hz⟩⟩
  have hseq := seq_serialize ⟨pk, ⟨z, hz⟩⟩
  simp only [SszValue.pks] at hfl hseq
  simp only [desc, SszValue.toValue, serialize, serializeStruct, serializeFields] at hseq ⊢
  simp only [List.length_map, Vector.length_toList, beq_self_eq_true, ↓reduceIte] at hseq ⊢
  rw [hseq]
  simp (config := {decide := true}) [bind, Except.bind, pure, Except.pure, assemble, headWidth, bodyWidth,
    headOf, bodiesOf, Desc.isFixed, Desc.fixedSize, bytesPerOffset, SszValue.encode, SszValue.pks, Desc.fieldsFixedSize,
    Array.append_assoc, hz, hfl]

/-- **Spec roundtrip.** -/
theorem encode_roundtrip (g : SszValue) : deserialize desc (SszValue.encode g) = .ok g.toValue :=
  deserialize_enc (G := SszValue) (toV := SszValue.toValue) (enc := SszValue.encode) desc_wellFormed toValue_serialize
    toValue_fits g

theorem accepted_is_encode {bs : Array UInt8} {v : Value} (h : deserialize desc bs = .ok v) :
    ∃ g : SszValue, v = g.toValue ∧ bs = SszValue.encode g :=
  accepted_is_enc (G := SszValue) (toV := SszValue.toValue) (enc := SszValue.encode) desc_wellFormed toValue_serialize
    toValue_surjective h

/-- **EthLib accepts exactly the 24624-byte inputs.** -/
theorem spec_accepts_iff (bs : Array UInt8) : (∃ v, deserialize desc bs = .ok v) ↔ bs.size = 24624 := by
  constructor
  · rintro ⟨v, hd⟩
    obtain ⟨g, rfl, hb⟩ := accepted_is_encode hd
    rw [hb]; exact encode_size g
  · intro h
    let chunks : List (Vector UInt8 48) := (List.range 512).map fun i =>
      toV48 (.bytes (bs.extract (i * 48) ((i + 1) * 48)))
    let g : SszValue := ⟨⟨chunks.toArray, by simp [chunks]⟩, ⟨bs.extract 24576 24624, by simp; omega⟩⟩
    have hm : chunks.map (·.toArray) = (List.range 512).map (fun i => bs.extract (i * 48) ((i + 1) * 48)) := by
      simp only [chunks, List.map_map]
      apply List.map_congr_left
      intro i hi
      simp only [List.mem_range] at hi
      have hsz : (bs.extract (i * 48) ((i + 1) * 48)).size = 48 := by simp; omega
      show (toV48 (.bytes (bs.extract (i * 48) ((i + 1) * 48)))).toArray = _
      simp only [toV48]
      rw [dif_pos hsz]
    have hc : g.pks.flatten.toArray = bs.extract 0 24576 := by
      show (g.pubkeys.toList.map (·.toList)).flatten.toArray = _
      rw [← concatParts_v48]
      have := concat_fixed_slices bs 48 512 (by omega)
      simp only [g, Vector.toList_mk, List.toList_toArray]
      rw [hm, this]
    have e : bs = SszValue.encode g := by
      simp only [SszValue.encode, hc]
      simp (config := {decide := true}) only [g, Array.extract_append_extract, Nat.min_def, Nat.max_def, ↓reduceIte]
      rw [← h]; simp
    rw [e]
    exact ⟨_, encode_roundtrip g⟩

/-- `len(buf) ≠ 24624`: EthLib rejects. -/
theorem spec_rejects (bs : Array UInt8) (h : bs.size ≠ 24624) : ∃ e, deserialize desc bs = .error e := by
  cases hd : deserialize desc bs with
  | error e => exact ⟨e, rfl⟩
  | ok v => exact absurd ((spec_accepts_iff bs).mp ⟨v, hd⟩) h

end Prysm.SyncCommittee
