import Fv1.SpecBitVec
import Fv1.Transfer

/-!
# Spec: `target.BitL`

    type BitL struct { B bitfield.Bitlist `ssz-max:"2048"` }

    class BitL(Container):
        b: Bitlist[2048]

Encoding: offset 4 (4) ‖ the bitlist bytes (`packBitsDelimited`: the bits,
then a delimiter bit, `size / 8 + 1` bytes, so at most 257 bytes).
-/

namespace Fv1
open EthLib.Serialization.Ssz

def blDesc : Desc := .container ["b"] [.bitList 2048]

theorem blDesc_wellFormed : blDesc.wellFormed = .ok () := by rfl

/-- The bits of a `target.BitL` value (`c.B` without its delimiter), at most 2048. -/
abbrev BitLG := { bits : Array Bool // bits.size ≤ 2048 }

def blToValue (g : BitLG) : Value := .seq [.bits g.1]

def blEncode (g : BitLG) : Array UInt8 := uintBytes 4 4 ++ packBitsDelimited g.1

theorem bl_encode_size (g : BitLG) : (blEncode g).size = 4 + (g.1.size + 8) / 8 := by
  simp [blEncode, packBitsDelimited, packBits, Fv.uintBytes_size]

theorem bl_serialize (g : BitLG) : serialize blDesc (blToValue g) = .ok (blEncode g) := by
  obtain ⟨b, hb⟩ := g
  have hs : (packBitsDelimited b).size = (b.size + 8) / 8 := by simp [packBitsDelimited, packBits]
  simp only [blDesc, blToValue, serialize, serializeStruct, serializeFields, hb, decide_true, ite_true]
  simp (config := {decide := true}) [bind, Except.bind, pure, Except.pure, assemble, headWidth, bodyWidth,
    headOf, bodiesOf, Desc.isFixed, Desc.fixedSize, bytesPerOffset, blEncode, hs, Desc.fieldsFixedSize]
  omega

theorem bl_toValue_surjective (v : Value) (h : Value.fits blDesc v = true) : ∃ g : BitLG, blToValue g = v := by
  obtain ⟨vs, rfl, hf⟩ := fits_container h
  have hl := fieldsFit_length hf
  match vs, hl with
  | [v1], _ =>
    simp only [fieldsFit_cons] at hf
    obtain ⟨h1, -⟩ := hf
    obtain ⟨d, rfl, hd⟩ : ∃ d, v1 = .bits d ∧ d.size ≤ 2048 := by
      cases v1 <;> simp [Value.fits] at h1 ⊢; exact h1
    exact ⟨⟨d, hd⟩, rfl⟩

theorem bl_toValue_fits (g : BitLG) : Value.fits blDesc (blToValue g) = true := by
  obtain ⟨b, hb⟩ := g
  simp [blDesc, blToValue, Value.fits, Value.fieldsFit, hb]

/-- Every input EthLib accepts has at most 4 + 257 bytes. -/
theorem bl_accepted_size (bs : Array UInt8) (v : Value) (hd : deserialize blDesc bs = .ok v) : bs.size ≤ 261 := by
  obtain ⟨g, -, rfl⟩ := accepted_is_enc (G := BitLG) (toV := blToValue) (enc := blEncode)
    blDesc_wellFormed bl_serialize bl_toValue_surjective hd
  rw [bl_encode_size]; have := g.2; omega

/-- 258 bytes: 257 zero bytes, then 0x01 (delimiter at bit 2056, over 2048). -/
def blOverlong : Array UInt8 := Array.replicate 257 0 ++ #[1]

/-- EthLib rejects `offset 4 ‖ blOverlong` (finding F2, EthLib side). -/
theorem bl_spec_rejects_overlong : ∃ e, deserialize blDesc (#[4, 0, 0, 0] ++ blOverlong) = .error e := by
  cases hd : deserialize blDesc (#[4, 0, 0, 0] ++ blOverlong) with
  | error e => exact ⟨e, rfl⟩
  | ok v => have := bl_accepted_size _ v hd; simp [blOverlong] at this

end Fv1
