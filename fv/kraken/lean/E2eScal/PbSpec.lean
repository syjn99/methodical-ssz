import E2e.Spec
import E2e.SpecEq
import E2eScal.PbDesc
import E2eScal.PbSpecChecker

/-!
# Spec bridge for the real Prysm `v1alpha1.PowBlock` (H6 hold-out, full-proof type)

Hand-written by the H6 evaluation session (the shape of `DdSpec.lean`, H4).
`prysmPbDesc` (`PbDesc.lean`) is the independent hand `Desc` from consensus-specs bellatrix; it was committed
before `pbCheckerDesc` was rendered and printed. The two Descs DIFFER in one field kind:
consensus-specs `total_difficulty: uint256` (`.uint 32`), the producer (Prysm, `TotalDifficulty []byte`,
`ssz-size:"32"`) `.byteVector 32`. So the codec equality of the earlier types (same values) does not hold here.
Proved instead: both Descs accept exactly the 96-byte inputs (`pb_accepts_same`), and on every input the hand
Desc decodes the third field to `.uint n` exactly when the checker Desc decodes it to `.bytes (uintBytes 32 n)`,
the 32 little-endian bytes of `n` (`pb_codec_checker`). The machine code stores those bytes.
`PPb` is the SSZ content of a PowBlock: two 32-byte hashes and a total difficulty `< 2^256`.
-/

namespace E2e
open EthLib.Serialization.Ssz Fv1

/-- The two Descs: same names order and widths; the third kind differs (`uint 32` vs `byteVector 32`). -/
theorem prysmPbDesc_checker :
    prysmPbDesc = .container ["block_hash", "parent_hash", "total_difficulty"]
      [.byteVector 32, .byteVector 32, .uint 32]
    ∧ pbCheckerDesc = .container ["BlockHash", "ParentHash", "TotalDifficulty"]
      [.byteVector 32, .byteVector 32, .byteVector 32] :=
  ⟨rfl, rfl⟩

theorem prysmPbDesc_wellFormed : prysmPbDesc.wellFormed = .ok () := by rfl
theorem prysmPbDesc_fixedSize : prysmPbDesc.fixedSize = some 96 := by rfl
theorem pbChecker_wellFormed : pbCheckerDesc.wellFormed = .ok () := by rfl
theorem pbChecker_fixedSize : pbCheckerDesc.fixedSize = some 96 := by rfl

/-- The SSZ content of a PowBlock (consensus-specs view: total difficulty is a number below `2^256`). -/
structure PPb where
  blockHash : Vector UInt8 32
  parentHash : Vector UInt8 32
  totalDifficulty : Fin (2 ^ 256)

/-- Value under the hand (spec) Desc. -/
def PPb.toValue (g : PPb) : Value :=
  .seq [.bytes g.blockHash.toArray, .bytes g.parentHash.toArray, .uint g.totalDifficulty.val]

/-- Value under the checker (Prysm) Desc: the third field is the 32 little-endian bytes of the number. -/
def PPb.toValueC (g : PPb) : Value :=
  .seq [.bytes g.blockHash.toArray, .bytes g.parentHash.toArray, .bytes (uintBytes 32 g.totalDifficulty.val)]

/-- `blockHash ++ parentHash ++ uintBytes 32 totalDifficulty`. -/
def ppbEnc (g : PPb) : Array UInt8 :=
  g.blockHash.toArray ++ g.parentHash.toArray ++ uintBytes 32 g.totalDifficulty.val

theorem ppb_enc_size (g : PPb) : (ppbEnc g).size = 96 := by
  simp [ppbEnc, Fv.uintBytes_size]

theorem ppb_toValue_fits (g : PPb) : Value.fits prysmPbDesc g.toValue = true := by
  have := g.totalDifficulty.isLt
  simp [prysmPbDesc, PPb.toValue, Value.fits, Value.fieldsFit]

theorem ppb_toValueC_fits (g : PPb) : Value.fits pbCheckerDesc g.toValueC = true := by
  simp [pbCheckerDesc, PPb.toValueC, Value.fits, Value.fieldsFit, Fv.uintBytes_size]

theorem ppb_toValue_injective (g h : PPb) (e : g.toValue = h.toValue) : g = h := by
  obtain ⟨p, r, a⟩ := g; obtain ⟨p', r', a'⟩ := h
  simp only [PPb.toValue, Value.seq.injEq, List.cons.injEq, Value.uint.injEq, Value.bytes.injEq,
    and_true] at e
  obtain ⟨e0, e1, e2⟩ := e
  rw [Vector.toArray_inj.mp e0, Vector.toArray_inj.mp e1, Fin.ext e2]

theorem ppb_toValueC_injective (g h : PPb) (e : g.toValueC = h.toValueC) : g = h := by
  obtain ⟨p, r, a⟩ := g; obtain ⟨p', r', a'⟩ := h
  simp only [PPb.toValueC, Value.seq.injEq, List.cons.injEq, Value.bytes.injEq, and_true] at e
  obtain ⟨e0, e1, e2⟩ := e
  have ha : a.val = a'.val := by
    have h1 := readUint_uintBytes 32 a.val (by simpa using a.isLt)
    have h2 := readUint_uintBytes 32 a'.val (by simpa using a'.isLt)
    rw [← h1, ← h2, e2]
  rw [Vector.toArray_inj.mp e0, Vector.toArray_inj.mp e1, Fin.ext ha]

theorem ppb_toValue_surjective' (v : Value) (h : Value.fits prysmPbDesc v = true) : ∃ g : PPb, g.toValue = v := by
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
    exact ⟨⟨⟨q, hq⟩, ⟨d, hd⟩, ⟨a, by simpa using ha⟩⟩, by simp [PPb.toValue]⟩

theorem ppb_toValueC_surjective' (v : Value) (h : Value.fits pbCheckerDesc v = true) :
    ∃ g : PPb, g.toValueC = v := by
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
    exact ⟨⟨⟨q, hq⟩, ⟨d, hd⟩, ⟨readUint c 0 32, by simpa using r⟩⟩, by simp [PPb.toValueC, hu]⟩

/-- **`serialize g = blockHash ‖ parentHash ‖ uintBytes 32 totalDifficulty`** (hand Desc). -/
theorem ppb_serialize (g : PPb) : serialize prysmPbDesc g.toValue = .ok (ppbEnc g) := by
  obtain ⟨⟨q, hq⟩, ⟨r, hr⟩, a⟩ := g
  have := a.isLt
  simp only [prysmPbDesc, PPb.toValue, serialize, serializeStruct, serializeFields, Vector.toArray_mk, hq, hr]
  simp (config := {decide := true}) [*, bind, Except.bind, pure, Except.pure, assemble, headWidth, bodyWidth,
    headOf, bodiesOf, Desc.isFixed, Desc.fixedSize, Fv.uintBytes_size, bytesPerOffset, ppbEnc,
    Desc.fieldsFixedSize, Array.append_assoc]

/-- The same bytes under the checker Desc. -/
theorem ppb_serialize_checker (g : PPb) : serialize pbCheckerDesc g.toValueC = .ok (ppbEnc g) := by
  obtain ⟨⟨q, hq⟩, ⟨r, hr⟩, a⟩ := g
  simp only [pbCheckerDesc, PPb.toValueC, serialize, serializeStruct, serializeFields, Vector.toArray_mk, hq, hr]
  simp (config := {decide := true}) [*, bind, Except.bind, pure, Except.pure, assemble, headWidth, bodyWidth,
    headOf, bodiesOf, Desc.isFixed, Desc.fixedSize, Fv.uintBytes_size, bytesPerOffset, ppbEnc,
    Desc.fieldsFixedSize, Array.append_assoc]

/-- **Spec roundtrip.** -/
theorem ppb_roundtrip (g : PPb) : deserialize prysmPbDesc (ppbEnc g) = .ok g.toValue :=
  deserialize_enc (G := PPb) (toV := PPb.toValue) (enc := ppbEnc) prysmPbDesc_wellFormed ppb_serialize
    ppb_toValue_fits g

theorem ppb_roundtrip_checker (g : PPb) : deserialize pbCheckerDesc (ppbEnc g) = .ok g.toValueC :=
  deserialize_enc (G := PPb) (toV := PPb.toValueC) (enc := ppbEnc) pbChecker_wellFormed ppb_serialize_checker
    ppb_toValueC_fits g

theorem ppb_accepted_is_enc {bs : Array UInt8} {v : Value} (h : deserialize prysmPbDesc bs = .ok v) :
    ∃ g : PPb, v = g.toValue ∧ bs = ppbEnc g :=
  accepted_is_enc (G := PPb) (toV := PPb.toValue) (enc := ppbEnc) prysmPbDesc_wellFormed ppb_serialize
    ppb_toValue_surjective' h

theorem ppb_accepted_is_enc_checker {bs : Array UInt8} {v : Value} (h : deserialize pbCheckerDesc bs = .ok v) :
    ∃ g : PPb, v = g.toValueC ∧ bs = ppbEnc g :=
  accepted_is_enc (G := PPb) (toV := PPb.toValueC) (enc := ppbEnc) pbChecker_wellFormed ppb_serialize_checker
    ppb_toValueC_surjective' h

/-- **EthLib accepts exactly the 96-byte inputs** (hand Desc). -/
theorem ppb_spec_accepts_iff (bs : Array UInt8) : (∃ v, deserialize prysmPbDesc bs = .ok v) ↔ bs.size = 96 := by
  constructor
  · rintro ⟨v, hd⟩
    obtain ⟨g, rfl, hb⟩ := ppb_accepted_is_enc hd
    rw [hb]; exact ppb_enc_size g
  · intro h
    have r0 := readUint_lt bs 64 32
    let g : PPb := ⟨⟨bs.extract 0 32, by simp; omega⟩, ⟨bs.extract 32 64, by simp; omega⟩,
      ⟨readUint bs 64 32, by simpa using r0⟩⟩
    have e : bs = ppbEnc g := by
      simp only [g, ppbEnc, uintBytes_readUint_slice bs 64 32 (by omega)]
      simp only [Nat.zero_add, Nat.reduceAdd]
      simp (config := {decide := true}) only [Array.extract_append_extract, Nat.min_def, Nat.max_def, ↓reduceIte]
      rw [← h]; simp
    rw [e]
    exact ⟨_, ppb_roundtrip g⟩

/-- `len(buf) ≠ 96`: EthLib rejects. -/
theorem ppb_spec_rejects (bs : Array UInt8) (h : bs.size ≠ 96) : ∃ e, deserialize prysmPbDesc bs = .error e := by
  cases hd : deserialize prysmPbDesc bs with
  | error e => exact ⟨e, rfl⟩
  | ok v => exact absurd ((ppb_spec_accepts_iff bs).mp ⟨v, hd⟩) h

/-! ### Hand Desc vs checker Desc -/

/-- **Same accepted inputs** under the two Descs. -/
theorem pb_accepts_same (bs : Array UInt8) :
    (∃ v, deserialize prysmPbDesc bs = .ok v) ↔ (∃ v, deserialize pbCheckerDesc bs = .ok v) := by
  constructor
  · rintro ⟨v, hd⟩
    obtain ⟨g, rfl, hb⟩ := ppb_accepted_is_enc hd
    exact ⟨_, hb ▸ ppb_roundtrip_checker g⟩
  · rintro ⟨v, hd⟩
    obtain ⟨g, rfl, hb⟩ := ppb_accepted_is_enc_checker hd
    exact ⟨_, hb ▸ ppb_roundtrip g⟩

/-- **Codec correspondence**: on every input, the hand Desc decodes to `g.toValue` (total difficulty a number)
exactly when the checker Desc decodes to `g.toValueC` (its 32 little-endian bytes). -/
theorem pb_codec_checker (bs : Array UInt8) (g : PPb) :
    deserialize prysmPbDesc bs = .ok g.toValue ↔ deserialize pbCheckerDesc bs = .ok g.toValueC := by
  constructor
  · intro h
    obtain ⟨g', e, hb⟩ := ppb_accepted_is_enc h
    rw [ppb_toValue_injective _ _ e, hb]; exact ppb_roundtrip_checker g'
  · intro h
    obtain ⟨g', e, hb⟩ := ppb_accepted_is_enc_checker h
    rw [ppb_toValueC_injective _ _ e, hb]; exact ppb_roundtrip g'

end E2e
