import Spec.TestBitVec
import Spec.DeserializeOfSerialize

/-!
# Spec: `target.BitL`

    type BitL struct { B bitfield.Bitlist `ssz-max:"2048"` }

    class BitL(Container):
        b: Bitlist[2048]

Encoding: offset 4 (4) ‖ the bitlist bytes (`packBitsDelimited`: the bits,
then a delimiter bit, `size / 8 + 1` bytes, so at most 257 bytes).
-/

namespace Spec
open EthLib.Serialization.Ssz

def bitListDesc : Desc := .container ["b"] [.bitList 2048]

theorem bitListDesc_wellFormed : bitListDesc.wellFormed = .ok () := by rfl

/-- The bits of a `target.BitL` value (`c.B` without its delimiter), at most 2048. -/
abbrev BitListValue := { bits : Array Bool // bits.size ≤ 2048 }

def bitListToValue (g : BitListValue) : Value := .seq [.bits g.1]

def bitListEncode (g : BitListValue) : Array UInt8 := uintBytes 4 4 ++ packBitsDelimited g.1

theorem bitList_encode_size (g : BitListValue) : (bitListEncode g).size = 4 + (g.1.size + 8) / 8 := by
  simp [bitListEncode, packBitsDelimited, packBits, Spec.uintBytes_size]

theorem bitList_serialize (g : BitListValue) : serialize bitListDesc (bitListToValue g) = .ok (bitListEncode g) := by
  obtain ⟨b, hb⟩ := g
  have hs : (packBitsDelimited b).size = (b.size + 8) / 8 := by simp [packBitsDelimited, packBits]
  simp only [bitListDesc, bitListToValue, serialize, serializeStruct, serializeFields, hb, decide_true, ite_true]
  simp (config := {decide := true}) [bind, Except.bind, pure, Except.pure, assemble, headWidth, bodyWidth,
    headOf, bodiesOf, Desc.isFixed, Desc.fixedSize, bytesPerOffset, bitListEncode, hs, Desc.fieldsFixedSize]
  omega

theorem bitList_toValue_surjective (v : Value) (h : Value.fits bitListDesc v = true) : ∃ g : BitListValue, bitListToValue g = v := by
  obtain ⟨vs, rfl, hf⟩ := fits_container h
  have hl := fieldsFit_length hf
  match vs, hl with
  | [v1], _ =>
    simp only [fieldsFit_cons] at hf
    obtain ⟨h1, -⟩ := hf
    obtain ⟨d, rfl, hd⟩ : ∃ d, v1 = .bits d ∧ d.size ≤ 2048 := by
      cases v1 <;> simp [Value.fits] at h1 ⊢; exact h1
    exact ⟨⟨d, hd⟩, rfl⟩

theorem bitList_toValue_fits (g : BitListValue) : Value.fits bitListDesc (bitListToValue g) = true := by
  obtain ⟨b, hb⟩ := g
  simp [bitListDesc, bitListToValue, Value.fits, Value.fieldsFit, hb]

/-- Every input EthLib accepts has at most 4 + 257 bytes. -/
theorem bitList_accepted_size (bs : Array UInt8) (v : Value) (hd : deserialize bitListDesc bs = .ok v) : bs.size ≤ 261 := by
  obtain ⟨g, -, rfl⟩ := accepted_input_is_encoding (G := BitListValue) (toV := bitListToValue) (enc := bitListEncode)
    bitListDesc_wellFormed bitList_serialize bitList_toValue_surjective hd
  rw [bitList_encode_size]; have := g.2; omega

/-- 258 bytes: 257 zero bytes, then 0x01 (delimiter at bit 2056, over 2048). -/
def bitListOverlong : Array UInt8 := Array.replicate 257 0 ++ #[1]

/-- EthLib rejects `offset 4 ‖ bitListOverlong` (EthLib side of the fixed generator defect: the Bitlist encoder checked the length in bytes, not in bits). -/
theorem bitList_spec_rejects_overlong : ∃ e, deserialize bitListDesc (#[4, 0, 0, 0] ++ bitListOverlong) = .error e := by
  cases hd : deserialize bitListDesc (#[4, 0, 0, 0] ++ bitListOverlong) with
  | error e => exact ⟨e, rfl⟩
  | ok v => have := bitList_accepted_size _ v hd; simp [bitListOverlong] at this

end Spec
