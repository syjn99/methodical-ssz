import Spec.TestScalars

/-!
# Spec: `target.BitVec`

    type BitVec struct {
        J bitfield.Bitvector4 `ssz-size:"1"`
    }

    class BitVec(Container):
        j: Bitvector[4]

Go layout: J @0 (ptr), @8 (len), @16 (cap). A Go value EthLib can produce has
len(J) = 1 and the four padding bits of the byte at 0 (`BitVecG`: b < 16).
-/

namespace Spec
open EthLib.Serialization.Ssz

def bvDesc : Desc := .container ["j"] [.bitVector 4]

theorem bvDesc_wellFormed : bvDesc.wellFormed = .ok () := by rfl
theorem bvDesc_fixedSize : bvDesc.fixedSize = some 1 := by rfl

/-- A Go value of type `target.BitVec` with len(J) = 1 and no padding bit set. -/
structure BitVecG where
  b : UInt8
  hb : b.toNat < 16

def BitVecG.toValue (g : BitVecG) : Value := .seq [.bits (unpackBits #[g.b] 4)]

def bvEncode (g : BitVecG) : Array UInt8 := #[g.b]

theorem bv_pack_unpack : ∀ b : Fin 16,
    packBits (unpackBits #[UInt8.ofNat b] 4) ((4 + 7) / 8) = #[UInt8.ofNat b] := by decide +kernel

theorem bv_unpack_pack : ∀ x0 x1 x2 x3 : Bool,
    unpackBits (packBits #[x0, x1, x2, x3] 1) 4 = #[x0, x1, x2, x3] ∧ ((packBits #[x0, x1, x2, x3] 1)[0]!).toNat < 16 ∧
    (packBits #[x0, x1, x2, x3] 1).size = 1 := by decide +kernel

theorem bv_unpack_inj : ∀ b c : Fin 16,
    unpackBits #[UInt8.ofNat b] 4 = unpackBits #[UInt8.ofNat c] 4 → b = c := by decide +kernel

theorem uint8_fin16 (b : UInt8) (h : b.toNat < 16) : ∃ f : Fin 16, b = UInt8.ofNat f :=
  ⟨⟨b.toNat, h⟩, by simp⟩

theorem arr1 (a : Array UInt8) (h : a.size = 1) : #[a[0]!] = a := by
  obtain ⟨l⟩ := a
  match l, h with
  | [x], _ => rfl

theorem bv_serialize (g : BitVecG) : serialize bvDesc g.toValue = .ok (bvEncode g) := by
  obtain ⟨b, hb⟩ := g
  obtain ⟨f, rfl⟩ := uint8_fin16 b hb
  have hs : (unpackBits #[UInt8.ofNat f] 4).size = 4 := by simp [unpackBits]
  simp only [bvDesc, BitVecG.toValue, serialize, serializeStruct, serializeFields, hs, bne_self_eq_false,
    beq_self_eq_true, ↓reduceIte, bv_pack_unpack f]
  simp (config := {decide := true}) [bind, Except.bind, pure, Except.pure, assemble, headWidth, bodyWidth,
    headOf, bodiesOf, Desc.isFixed, Desc.fixedSize, bytesPerOffset, bvEncode]

theorem bv_toValue_fits (g : BitVecG) : Value.fits bvDesc g.toValue = true := by
  simp [BitVecG.toValue, bvDesc, Value.fits, Value.fieldsFit, unpackBits]

theorem bv_toValue_injective (g h : BitVecG) (e : g.toValue = h.toValue) : g = h := by
  obtain ⟨b, hb⟩ := g; obtain ⟨c, hc⟩ := h
  obtain ⟨f, rfl⟩ := uint8_fin16 b hb; obtain ⟨f', rfl⟩ := uint8_fin16 c hc
  simp only [BitVecG.toValue, Value.seq.injEq, List.cons.injEq, Value.bits.injEq, and_true] at e
  have := bv_unpack_inj f f' e
  subst this; rfl

theorem bv_toValue_surjective (v : Value) (h : Value.fits bvDesc v = true) :
    ∃ g : BitVecG, g.toValue = v := by
  obtain ⟨vs, rfl, hf⟩ := fits_container h
  have hl := fieldsFit_length hf
  match vs, hl with
  | [v1], _ =>
    simp only [fieldsFit_cons] at hf
    obtain ⟨h1, -⟩ := hf
    obtain ⟨a, rfl, ha⟩ : ∃ a, v1 = .bits a ∧ a.size = 4 := by
      cases v1 <;> simp [Value.fits] at h1 ⊢; exact h1
    obtain ⟨l⟩ := a
    match l, ha with
    | [x0, x1, x2, x3], _ =>
      obtain ⟨h1, h2, h3⟩ := bv_unpack_pack x0 x1 x2 x3
      refine ⟨⟨(packBits #[x0, x1, x2, x3] 1)[0]!, h2⟩, ?_⟩
      simp only [BitVecG.toValue]
      rw [arr1 _ h3, h1]

theorem bv_encode_size (g : BitVecG) : (bvEncode g).size = 1 := rfl

/-- **The decoder's missing check, in EthLib.** A byte with a padding bit set is
not a canonical Bitvector[4]: EthLib rejects it (`paddingBits`). -/
theorem bv_spec_rejects_padding : deserialize bvDesc #[0x10] = .error .paddingBits := by
  simp (config := {decide := true}) [bvDesc, deserialize, deserializeStruct, structSlots, structBudget, readSlots,
    bodyStarts, structBodies, deserializeFields, checkInline, takeSlots, offsetSpans, Desc.fieldsFixedSize,
    Desc.fixedSize, bind, Except.bind, pure, Except.pure, Functor.map, Except.map, throw, throwThe,
    MonadExceptOf.throw, Slot.held]

end Spec
