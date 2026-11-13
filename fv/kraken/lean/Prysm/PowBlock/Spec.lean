import Prysm.Checkpoint.Spec
import Prysm.Checkpoint.SpecEquivalence
import Prysm.PowBlock.SpecDescription
import Prysm.PowBlock.SpecChecker

/-!
# Spec bridge for the real Prysm `v1alpha1.PowBlock` (hold-out, full-proof type)

Hand-written (the shape of `DdSpec.lean`).
`desc` (`PbDesc.lean`) is the independent hand `Desc` from consensus-specs bellatrix; it was committed
before `checkerDesc` was rendered and printed. The two Descs DIFFER in one field kind:
consensus-specs `total_difficulty: uint256` (`.uint 32`), the producer (Prysm, `TotalDifficulty []byte`,
`ssz-size:"32"`) `.byteVector 32`. So the codec equality of the earlier types (same values) does not hold here.
Proved instead: both Descs accept exactly the 96-byte inputs (`Decode.accepts_same`), and on every input the hand
Desc decodes the third field to `.uint n` exactly when the checker Desc decodes it to `.bytes (uintBytes 32 n)`,
the 32 little-endian bytes of `n` (`Decode.codec_checker`). The machine code stores those bytes.
`SszValue` is the SSZ content of a PowBlock: two 32-byte hashes and a total difficulty `< 2^256`.
-/

namespace Prysm.PowBlock
open EthLib.Serialization.Ssz
open Spec hiding readUint_lt

/-- The two Descs: same names order and widths; the third kind differs (`uint 32` vs `byteVector 32`). -/
theorem desc_checker :
    desc = .container ["block_hash", "parent_hash", "total_difficulty"]
      [.byteVector 32, .byteVector 32, .uint 32]
    ∧ checkerDesc = .container ["BlockHash", "ParentHash", "TotalDifficulty"]
      [.byteVector 32, .byteVector 32, .byteVector 32] :=
  ⟨rfl, rfl⟩

theorem desc_wellFormed : desc.wellFormed = .ok () := by rfl
theorem desc_fixedSize : desc.fixedSize = some 96 := by rfl
theorem checker_wellFormed : checkerDesc.wellFormed = .ok () := by rfl
theorem checker_fixedSize : checkerDesc.fixedSize = some 96 := by rfl

/-- The SSZ content of a PowBlock (consensus-specs view: total difficulty is a number below `2^256`). -/
structure SszValue where
  blockHash : Vector UInt8 32
  parentHash : Vector UInt8 32
  totalDifficulty : Fin (2 ^ 256)

/-- Value under the hand (spec) Desc. -/
def SszValue.toValue (g : SszValue) : Value :=
  .seq [.bytes g.blockHash.toArray, .bytes g.parentHash.toArray, .uint g.totalDifficulty.val]

/-- Value under the checker (Prysm) Desc: the third field is the 32 little-endian bytes of the number. -/
def SszValue.toValueC (g : SszValue) : Value :=
  .seq [.bytes g.blockHash.toArray, .bytes g.parentHash.toArray, .bytes (uintBytes 32 g.totalDifficulty.val)]

/-- `blockHash ++ parentHash ++ uintBytes 32 totalDifficulty`. -/
def SszValue.encode (g : SszValue) : Array UInt8 :=
  g.blockHash.toArray ++ g.parentHash.toArray ++ uintBytes 32 g.totalDifficulty.val

theorem SszValue.enc_size (g : SszValue) : (SszValue.encode g).size = 96 := by
  simp [SszValue.encode, Spec.uintBytes_size]

theorem SszValue.toValue_fits (g : SszValue) : Value.fits desc g.toValue = true := by
  have := g.totalDifficulty.isLt
  simp [desc, SszValue.toValue, Value.fits, Value.fieldsFit]

theorem SszValue.toValueC_fits (g : SszValue) : Value.fits checkerDesc g.toValueC = true := by
  simp [checkerDesc, SszValue.toValueC, Value.fits, Value.fieldsFit, Spec.uintBytes_size]

theorem SszValue.toValue_injective (g h : SszValue) (e : g.toValue = h.toValue) : g = h := by
  obtain ⟨p, r, a⟩ := g; obtain ⟨p', r', a'⟩ := h
  simp only [SszValue.toValue, Value.seq.injEq, List.cons.injEq, Value.uint.injEq, Value.bytes.injEq,
    and_true] at e
  obtain ⟨e0, e1, e2⟩ := e
  rw [Vector.toArray_inj.mp e0, Vector.toArray_inj.mp e1, Fin.ext e2]

theorem SszValue.toValueC_injective (g h : SszValue) (e : g.toValueC = h.toValueC) : g = h := by
  obtain ⟨p, r, a⟩ := g; obtain ⟨p', r', a'⟩ := h
  simp only [SszValue.toValueC, Value.seq.injEq, List.cons.injEq, Value.bytes.injEq, and_true] at e
  obtain ⟨e0, e1, e2⟩ := e
  have ha : a.val = a'.val := by
    have h1 := readUint_uintBytes 32 a.val (by simpa using a.isLt)
    have h2 := readUint_uintBytes 32 a'.val (by simpa using a'.isLt)
    rw [← h1, ← h2, e2]
  rw [Vector.toArray_inj.mp e0, Vector.toArray_inj.mp e1, Fin.ext ha]

theorem SszValue.toValue_surjective' (v : Value) (h : Value.fits desc v = true) : ∃ g : SszValue, g.toValue = v := by
  obtain ⟨vs, rfl, hf⟩ := fits_container h
  have hl := fieldsFit_length hf
  match vs, hl with
  | [v0, v1, v2], _ =>
    simp only [fieldsFit_cons] at hf
    obtain ⟨h0, h1, h2, -⟩ := hf
    obtain ⟨q, rfl, hq⟩ : ∃ d, v0 = .bytes d ∧ d.size = 32 := by
      cases v0 <;> simp [Value.fits] at h0 ⊢; exact h0
    obtain ⟨d, rfl, hd⟩ : ∃ d, v1 = .bytes d ∧ d.size = 32 := by
      cases v1 <;> simp [Value.fits] at h1 ⊢; exact h1
    obtain ⟨a, rfl, ha⟩ := fits_uint h2
    exact ⟨⟨⟨q, hq⟩, ⟨d, hd⟩, ⟨a, by simpa using ha⟩⟩, by simp [SszValue.toValue]⟩

theorem SszValue.toValueC_surjective' (v : Value) (h : Value.fits checkerDesc v = true) :
    ∃ g : SszValue, g.toValueC = v := by
  obtain ⟨vs, rfl, hf⟩ := fits_container h
  have hl := fieldsFit_length hf
  match vs, hl with
  | [v0, v1, v2], _ =>
    simp only [fieldsFit_cons] at hf
    obtain ⟨h0, h1, h2, -⟩ := hf
    obtain ⟨q, rfl, hq⟩ : ∃ d, v0 = .bytes d ∧ d.size = 32 := by
      cases v0 <;> simp [Value.fits] at h0 ⊢; exact h0
    obtain ⟨d, rfl, hd⟩ : ∃ d, v1 = .bytes d ∧ d.size = 32 := by
      cases v1 <;> simp [Value.fits] at h1 ⊢; exact h1
    obtain ⟨c, rfl, hc⟩ : ∃ d, v2 = .bytes d ∧ d.size = 32 := by
      cases v2 <;> simp [Value.fits] at h2 ⊢; exact h2
    have r := readUint_lt c 0 32
    have hu : uintBytes 32 (readUint c 0 32) = c := by
      rw [uintBytes_readUint_slice c 0 32 (by omega)]; simp [← hc]
    exact ⟨⟨⟨q, hq⟩, ⟨d, hd⟩, ⟨readUint c 0 32, by simpa using r⟩⟩, by simp [SszValue.toValueC, hu]⟩

/-- **`serialize g = blockHash ‖ parentHash ‖ uintBytes 32 totalDifficulty`** (hand Desc). -/
theorem SszValue.serialize_eq (g : SszValue) : serialize desc g.toValue = .ok (SszValue.encode g) := by
  obtain ⟨⟨q, hq⟩, ⟨r, hr⟩, a⟩ := g
  have := a.isLt
  simp only [desc, SszValue.toValue, serialize, serializeStruct, serializeFields, Vector.toArray_mk, hq, hr]
  simp (config := {decide := true}) [*, bind, Except.bind, pure, Except.pure, assemble, headWidth, bodyWidth,
    headOf, bodiesOf, Desc.isFixed, Desc.fixedSize, Spec.uintBytes_size, bytesPerOffset, SszValue.encode,
    Desc.fieldsFixedSize, Array.append_assoc]

/-- The same bytes under the checker Desc. -/
theorem SszValue.serialize_eq_checker (g : SszValue) : serialize checkerDesc g.toValueC = .ok (SszValue.encode g) := by
  obtain ⟨⟨q, hq⟩, ⟨r, hr⟩, a⟩ := g
  simp only [checkerDesc, SszValue.toValueC, serialize, serializeStruct, serializeFields, Vector.toArray_mk, hq, hr]
  simp (config := {decide := true}) [*, bind, Except.bind, pure, Except.pure, assemble, headWidth, bodyWidth,
    headOf, bodiesOf, Desc.isFixed, Desc.fixedSize, Spec.uintBytes_size, bytesPerOffset, SszValue.encode,
    Desc.fieldsFixedSize, Array.append_assoc]

/-- **Spec roundtrip.** -/
theorem SszValue.roundtrip (g : SszValue) : deserialize desc (SszValue.encode g) = .ok g.toValue :=
  deserialize_enc (G := SszValue) (toV := SszValue.toValue) (enc := SszValue.encode) desc_wellFormed SszValue.serialize_eq
    SszValue.toValue_fits g

theorem SszValue.roundtrip_checker (g : SszValue) : deserialize checkerDesc (SszValue.encode g) = .ok g.toValueC :=
  deserialize_enc (G := SszValue) (toV := SszValue.toValueC) (enc := SszValue.encode) checker_wellFormed SszValue.serialize_eq_checker
    SszValue.toValueC_fits g

theorem SszValue.accepted_is_encoding {bs : Array UInt8} {v : Value} (h : deserialize desc bs = .ok v) :
    ∃ g : SszValue, v = g.toValue ∧ bs = SszValue.encode g :=
  accepted_is_enc (G := SszValue) (toV := SszValue.toValue) (enc := SszValue.encode) desc_wellFormed SszValue.serialize_eq
    SszValue.toValue_surjective' h

theorem SszValue.accepted_is_encoding_checker {bs : Array UInt8} {v : Value} (h : deserialize checkerDesc bs = .ok v) :
    ∃ g : SszValue, v = g.toValueC ∧ bs = SszValue.encode g :=
  accepted_is_enc (G := SszValue) (toV := SszValue.toValueC) (enc := SszValue.encode) checker_wellFormed SszValue.serialize_eq_checker
    SszValue.toValueC_surjective' h

/-- **EthLib accepts exactly the 96-byte inputs** (hand Desc). -/
theorem SszValue.spec_accepts_iff (bs : Array UInt8) : (∃ v, deserialize desc bs = .ok v) ↔ bs.size = 96 := by
  constructor
  · rintro ⟨v, hd⟩
    obtain ⟨g, rfl, hb⟩ := SszValue.accepted_is_encoding hd
    rw [hb]; exact SszValue.enc_size g
  · intro h
    have r0 := readUint_lt bs 64 32
    let g : SszValue := ⟨⟨bs.extract 0 32, by simp; omega⟩, ⟨bs.extract 32 64, by simp; omega⟩,
      ⟨readUint bs 64 32, by simpa using r0⟩⟩
    have e : bs = SszValue.encode g := by
      simp only [g, SszValue.encode, uintBytes_readUint_slice bs 64 32 (by omega)]
      simp only [Nat.zero_add, Nat.reduceAdd]
      simp (config := {decide := true}) only [Array.extract_append_extract, Nat.min_def, Nat.max_def, ↓reduceIte]
      rw [← h]; simp
    rw [e]
    exact ⟨_, SszValue.roundtrip g⟩

/-- `len(buf) ≠ 96`: EthLib rejects. -/
theorem SszValue.spec_rejects (bs : Array UInt8) (h : bs.size ≠ 96) : ∃ e, deserialize desc bs = .error e := by
  cases hd : deserialize desc bs with
  | error e => exact ⟨e, rfl⟩
  | ok v => exact absurd ((SszValue.spec_accepts_iff bs).mp ⟨v, hd⟩) h

/-! ### Hand Desc vs checker Desc -/

/-- **Same accepted inputs** under the two Descs. -/
theorem Decode.accepts_same (bs : Array UInt8) :
    (∃ v, deserialize desc bs = .ok v) ↔ (∃ v, deserialize checkerDesc bs = .ok v) := by
  constructor
  · rintro ⟨v, hd⟩
    obtain ⟨g, rfl, hb⟩ := SszValue.accepted_is_encoding hd
    exact ⟨_, hb ▸ SszValue.roundtrip_checker g⟩
  · rintro ⟨v, hd⟩
    obtain ⟨g, rfl, hb⟩ := SszValue.accepted_is_encoding_checker hd
    exact ⟨_, hb ▸ SszValue.roundtrip g⟩

/-- **Codec correspondence**: on every input, the hand Desc decodes to `g.toValue` (total difficulty a number)
exactly when the checker Desc decodes to `g.toValueC` (its 32 little-endian bytes). -/
theorem Decode.codec_checker (bs : Array UInt8) (g : SszValue) :
    deserialize desc bs = .ok g.toValue ↔ deserialize checkerDesc bs = .ok g.toValueC := by
  constructor
  · intro h
    obtain ⟨g', e, hb⟩ := SszValue.accepted_is_encoding h
    rw [SszValue.toValue_injective _ _ e, hb]; exact SszValue.roundtrip_checker g'
  · intro h
    obtain ⟨g', e, hb⟩ := SszValue.accepted_is_encoding_checker h
    rw [SszValue.toValueC_injective _ _ e, hb]; exact SszValue.roundtrip g'

end Prysm.PowBlock
