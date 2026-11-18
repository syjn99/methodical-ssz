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
The Go values EthLib accepts have len(W) = 4 (`FixedVecValue` fixes it; the
encoder returns `ssz.ErrBytesLength` otherwise).
-/

namespace Spec
open EthLib.Serialization.Ssz

def fixedVecDesc : Desc := .container ["r", "w"] [.byteVector 32, .vector (.uint 8) 4]

theorem fixedVecDesc_wellFormed : fixedVecDesc.wellFormed = .ok () := by rfl
theorem fixedVecDesc_fixedSize : fixedVecDesc.fixedSize = some 64 := by rfl

/-- A Go value of type `target.FixedVec` with `len(W) = 4`. -/
structure FixedVecValue where
  r : Vector UInt8 32
  w : Vector UInt64 4

def FixedVecValue.toValue (g : FixedVecValue) : Value :=
  .seq [.bytes g.r.toArray, .seq (g.w.toList.map fun x => .uint x.toNat)]

def fixedVecEncode (g : FixedVecValue) : Array UInt8 := g.r.toArray ++ uint64Bytes g.w.toList

theorem fixedVec_encode_size (g : FixedVecValue) : (fixedVecEncode g).size = 64 := by
  simp [fixedVecEncode, uint64Bytes_size]

theorem fixedVec_toValue_fits (g : FixedVecValue) : Value.fits fixedVecDesc g.toValue = true := by
  simp [Spec.FixedVecValue.toValue, fixedVecDesc, Value.fits, Value.fieldsFit, allFit_uint64]

theorem fixedVec_toValue_injective (g h : FixedVecValue) (e : g.toValue = h.toValue) : g = h := by
  obtain ⟨r, w⟩ := g; obtain ⟨r', w'⟩ := h
  simp only [Spec.FixedVecValue.toValue, Value.seq.injEq, List.cons.injEq, Value.bytes.injEq, and_true] at e
  obtain ⟨e1, e2⟩ := e
  have : w.toList = w'.toList := by
    have := listU64_toValue_injective ⟨w.toList⟩ ⟨w'.toList⟩ (by simp [ListU64.toValue, e2])
    simpa using this
  congr 1
  · exact Vector.toArray_inj.mp e1
  · exact Vector.toList_inj.mp this

theorem fixedVec_toValue_surjective (v : Value) (h : Value.fits fixedVecDesc v = true) :
    ∃ g : FixedVecValue, g.toValue = v := by
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
    obtain ⟨l, rfl⟩ := allFit_uint64_inv es hall
    exact ⟨⟨⟨d, hd⟩, ⟨l.toArray, by simpa using hlen⟩⟩, by simp [Spec.FixedVecValue.toValue]⟩

theorem fixedVec_serialize (g : FixedVecValue) : serialize fixedVecDesc g.toValue = .ok (fixedVecEncode g) := by
  obtain ⟨⟨r, hr⟩, ⟨⟨w⟩, hw⟩⟩ := g
  simp only [List.size_toArray] at hw
  have hl4 : (w.map fun x => Value.uint x.toNat).length = 4 := by simpa using hw
  simp only [fixedVecDesc, Spec.FixedVecValue.toValue, serialize, serializeStruct, serializeFields, serializeSequence,
    Vector.toList_mk, List.toList_toArray, Vector.toArray_mk, hr, hl4, serializeEach_uint64]
  simp (config := {decide := true}) [bind, Except.bind, pure, Except.pure, assemble, headWidth, bodyWidth,
    headOf, bodiesOf, Desc.isFixed, Desc.fixedSize, bytesPerOffset, fixedVecEncode, inlineParts_headOf, inlineParts_headWidth,
    inlineParts_bodyWidth, inlineParts_bodiesOf, uint64Bytes_size, hw]
  have e : (List.map (fun _ => true) w) = (List.map (fun _ => true) (List.map (fun x => uintBytes 8 x.toNat) w)) := by
    simp [List.map_map]
  simp only [e, inlineParts_headWidth, inlineParts_bodyWidth, inlineParts_headOf, inlineParts_bodiesOf, hw]
  simp (config := {decide := true}) [headWidth, bodyWidth, headOf, bodiesOf, hr, uint64Bytes_size, hw, bytesPerOffset]

end Spec
