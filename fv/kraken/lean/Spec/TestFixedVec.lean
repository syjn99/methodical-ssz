import Spec.TestListU64

/-!
# Spec: `target.FixedVec`

    type FixedVec struct {
        R [32]byte `ssz-size:"32"`
        W []uint64 `ssz-size:"4"`
    }

    class FixedVec(Container):
        r: Bytes32                 # ByteVector[32]
        w: Vector[uint64, 4]

Go layout (amd64): R @0 (32 bytes), W @0x20 (ptr), @0x28 (len), @0x30 (cap).
The Go values EthLib accepts have len(W) = 4 (`FixedVecG` fixes it; the
encoder returns `ssz.ErrBytesLength` otherwise).
-/

namespace Spec
open EthLib.Serialization.Ssz

def fvDesc : Desc := .container ["r", "w"] [.byteVector 32, .vector (.uint 8) 4]

theorem fvDesc_wellFormed : fvDesc.wellFormed = .ok () := by rfl
theorem fvDesc_fixedSize : fvDesc.fixedSize = some 64 := by rfl

/-- A Go value of type `target.FixedVec` with `len(W) = 4`. -/
structure FixedVecG where
  r : Vector UInt8 32
  w : Vector UInt64 4

def FixedVecG.toValue (g : FixedVecG) : Value :=
  .seq [.bytes g.r.toArray, .seq (g.w.toList.map fun x => .uint x.toNat)]

def fvEncode (g : FixedVecG) : Array UInt8 := g.r.toArray ++ u64Bytes g.w.toList

theorem fv_encode_size (g : FixedVecG) : (fvEncode g).size = 64 := by
  simp [fvEncode, u64Bytes_size]

theorem fv_toValue_fits (g : FixedVecG) : Value.fits fvDesc g.toValue = true := by
  simp [FixedVecG.toValue, fvDesc, Value.fits, Value.fieldsFit, allFit_u64]

theorem fv_toValue_injective (g h : FixedVecG) (e : g.toValue = h.toValue) : g = h := by
  obtain ⟨r, w⟩ := g; obtain ⟨r', w'⟩ := h
  simp only [FixedVecG.toValue, Value.seq.injEq, List.cons.injEq, Value.bytes.injEq, and_true] at e
  obtain ⟨e1, e2⟩ := e
  have : w.toList = w'.toList := by
    have := lu_toValue_injective ⟨w.toList⟩ ⟨w'.toList⟩ (by simp [ListU64.toValue, e2])
    simpa using this
  congr 1
  · exact Vector.toArray_inj.mp e1
  · exact Vector.toList_inj.mp this

theorem fv_toValue_surjective (v : Value) (h : Value.fits fvDesc v = true) :
    ∃ g : FixedVecG, g.toValue = v := by
  obtain ⟨vs, rfl, hf⟩ := fits_container h
  have hl := fieldsFit_length hf
  match vs, hl with
  | [v1, v2], _ =>
    simp only [fieldsFit_cons] at hf
    obtain ⟨h1, h2, -⟩ := hf
    obtain ⟨d, rfl, hd⟩ : ∃ d, v1 = .bytes d ∧ d.size = 32 := by
      cases v1 <;> simp [Value.fits] at h1 ⊢; exact h1
    obtain ⟨es, rfl, hlen, hall⟩ : ∃ es, v2 = .seq es ∧ es.length = 4 ∧ Value.allFit (.uint 8) es = true := by
      cases v2 <;> simp [Value.fits] at h2 ⊢; exact h2
    obtain ⟨l, rfl⟩ := allFit_u64_inv es hall
    exact ⟨⟨⟨d, hd⟩, ⟨l.toArray, by simpa using hlen⟩⟩, by simp [FixedVecG.toValue]⟩

theorem fv_serialize (g : FixedVecG) : serialize fvDesc g.toValue = .ok (fvEncode g) := by
  obtain ⟨⟨r, hr⟩, ⟨⟨w⟩, hw⟩⟩ := g
  simp only [List.size_toArray] at hw
  have hl4 : (w.map fun x => Value.uint x.toNat).length = 4 := by simpa using hw
  simp only [fvDesc, FixedVecG.toValue, serialize, serializeStruct, serializeFields, serializeSequence,
    Vector.toList_mk, List.toList_toArray, Vector.toArray_mk, hr, hl4, serializeEach_u64]
  simp (config := {decide := true}) [bind, Except.bind, pure, Except.pure, assemble, headWidth, bodyWidth,
    headOf, bodiesOf, Desc.isFixed, Desc.fixedSize, bytesPerOffset, fvEncode, inl_headOf, inl_headWidth,
    inl_bodyWidth, inl_bodiesOf, u64Bytes_size, hw]
  have e : (List.map (fun _ => true) w) = (List.map (fun _ => true) (List.map (fun x => uintBytes 8 x.toNat) w)) := by
    simp [List.map_map]
  simp only [e, inl_headWidth, inl_bodyWidth, inl_headOf, inl_bodiesOf, hw]
  simp (config := {decide := true}) [headWidth, bodyWidth, headOf, bodiesOf, hr, u64Bytes_size, hw, bytesPerOffset]

end Spec
