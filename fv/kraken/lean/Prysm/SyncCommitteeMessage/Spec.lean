module

public import Spec.TestScalars
public import Spec.DeserializeOfSerialize
public import Prysm.SyncCommitteeMessage.SpecDescription
public import Prysm.SyncCommitteeMessage.SpecChecker

@[expose] public section

/-!
# Spec bridge for the Prysm `v1alpha1.SyncCommitteeMessage`

Written by `gen/flat-types/flat_types_spec.py`.
`desc` (`Prysm/SyncCommitteeMessage/SpecDescription.lean`) is the independent hand `Desc`, written from consensus-specs.
`checkerDesc` (`Prysm/SyncCommitteeMessage/SpecChecker.lean`, rendered by `gen/checks/desc_to_lean.py`) is the Desc checker's Desc of the type
(the producer output recorded in `gen/desc/results/main.result.json`, same sha256; copy in `prysm/go1.26.10/evidence/`).
`SszValue` is the SSZ content of a Go `v1alpha1.SyncCommitteeMessage`.
-/

namespace Prysm.SyncCommitteeMessage
open EthLib.Serialization.Ssz
open Spec hiding readUint_lt

theorem desc_kinds : desc = .container ["slot", "beacon_block_root", "validator_index", "signature"]
      [.uint 8, .byteVector 32, .uint 8, .byteVector 96] := rfl

theorem desc_wellFormed : desc.wellFormed = .ok () := by rfl
theorem desc_fixedSize : desc.fixedSize = some 144 := by rfl

/-- EthLib's `serialize` ignores container names. -/
theorem desc_serialize_checker (v : Value) : serialize desc v = serialize checkerDesc v := by
  unfold desc checkerDesc
  cases v <;> (try simp only [serialize, serializeStruct]) <;> rfl

/-- The SSZ content of a Go `v1alpha1.SyncCommitteeMessage`. -/
structure SszValue where
  slot : UInt64
  blockRoot : Vector UInt8 32
  validatorIndex : UInt64
  signature : Vector UInt8 96

def SszValue.toValue (g : SszValue) : Value :=
  .seq [.uint g.slot.toNat, .bytes g.blockRoot.toArray, .uint g.validatorIndex.toNat, .bytes g.signature.toArray]

def SszValue.encode (g : SszValue) : Array UInt8 :=
  uintBytes 8 g.slot.toNat ++ g.blockRoot.toArray ++ uintBytes 8 g.validatorIndex.toNat ++ g.signature.toArray

theorem SszValue.encode_size (g : SszValue) : (SszValue.encode g).size = 144 := by
  simp [SszValue.encode, Spec.uintBytes_size]

theorem SszValue.toValue_fits (g : SszValue) : Value.fits desc g.toValue = true := by
  have := g.slot.toNat_lt; have := g.validatorIndex.toNat_lt
  simp only [desc, SszValue.toValue, Value.fits, Value.fieldsFit] at *
  simp; omega

theorem SszValue.toValue_injective (g h : SszValue) (e : g.toValue = h.toValue) : g = h := by
  obtain ⟨a0, a1, a2, a3⟩ := g; obtain ⟨b0, b1, b2, b3⟩ := h
  simp only [SszValue.toValue, Value.seq.injEq, List.cons.injEq, Value.uint.injEq, Value.bytes.injEq,
    and_true] at e
  obtain ⟨e0, e1, e2, e3⟩ := e
  rw [UInt64.toNat_inj.mp e0, Vector.toArray_inj.mp e1, UInt64.toNat_inj.mp e2, Vector.toArray_inj.mp e3]

theorem SszValue.toValue_surjective' (v : Value) (h : Value.fits desc v = true) : ∃ g : SszValue, g.toValue = v := by
  obtain ⟨vs, rfl, hf⟩ := fits_container h
  have hl := fieldsFit_length hf
  match vs, hl with
  | [v0, v1, v2, v3], _ =>
    simp only [fieldsFit_cons] at hf
    obtain ⟨h0, h1, h2, h3, -⟩ := hf
    obtain ⟨a0, rfl, ha0⟩ := fits_uint h0
    obtain ⟨a1, rfl, ha1⟩ : ∃ d, v1 = .bytes d ∧ d.size = 32 := by
      cases v1 <;> simp [Value.fits] at h1 ⊢; exact h1
    obtain ⟨a2, rfl, ha2⟩ := fits_uint h2
    obtain ⟨a3, rfl, ha3⟩ : ∃ d, v3 = .bytes d ∧ d.size = 96 := by
      cases v3 <;> simp [Value.fits] at h3 ⊢; exact h3
    simp only [Nat.reduceMul, Nat.reducePow] at ha0 ha2
    exact ⟨⟨UInt64.ofNat a0, ⟨a1, ha1⟩, UInt64.ofNat a2, ⟨a3, ha3⟩⟩,
      by simp [SszValue.toValue, Nat.mod_eq_of_lt ha0, Nat.mod_eq_of_lt ha2]⟩

theorem SszValue.serialize_eq (g : SszValue) : serialize desc g.toValue = .ok (SszValue.encode g) := by
  obtain ⟨a0, ⟨r1, hr1⟩, a2, ⟨r3, hr3⟩⟩ := g
  have := a0.toNat_lt; have := a2.toNat_lt
  simp only [desc, SszValue.toValue, serialize, serializeStruct, serializeFields, Vector.toArray_mk, hr1, hr3]
  simp (config := {decide := true}) [*, bind, Except.bind, pure, Except.pure, assemble, headWidth, bodyWidth,
    headOf, bodiesOf, Desc.isFixed, Desc.fixedSize, Spec.uintBytes_size, bytesPerOffset, SszValue.encode,
    Desc.fieldsFixedSize, Array.append_assoc]

/-- **Spec roundtrip.** -/
theorem SszValue.roundtrip (g : SszValue) : deserialize desc (SszValue.encode g) = .ok g.toValue :=
  deserialize_encoding (G := SszValue) (toV := SszValue.toValue) (enc := SszValue.encode) desc_wellFormed SszValue.serialize_eq
    SszValue.toValue_fits g

theorem SszValue.accepted_is_encoding {bs : Array UInt8} {v : Value} (h : deserialize desc bs = .ok v) :
    ∃ g : SszValue, v = g.toValue ∧ bs = SszValue.encode g :=
  accepted_input_is_encoding (G := SszValue) (toV := SszValue.toValue) (enc := SszValue.encode) desc_wellFormed SszValue.serialize_eq
    SszValue.toValue_surjective' h

/-- **EthLib accepts exactly the 144-byte inputs.** -/
theorem SszValue.spec_accepts_iff (bs : Array UInt8) : (∃ v, deserialize desc bs = .ok v) ↔ bs.size = 144 := by
  constructor
  · rintro ⟨v, hd⟩
    obtain ⟨g, rfl, hb⟩ := SszValue.accepted_is_encoding hd
    rw [hb]; exact SszValue.encode_size g
  · intro h
    have r0 := readUint_lt bs 0 8
    have r2 := readUint_lt bs 40 8
    simp only [Nat.reducePow, Nat.reduceMul] at r0 r2
    let g : SszValue := ⟨UInt64.ofNat (readUint bs 0 8), ⟨bs.extract 8 40, by simp; omega⟩, UInt64.ofNat (readUint bs 40 8), ⟨bs.extract 48 144, by simp; omega⟩⟩
    have e : bs = SszValue.encode g := by
      simp only [g, SszValue.encode, UInt64.toNat_ofNat_of_lt' r0, UInt64.toNat_ofNat_of_lt' r2, uintBytes_readUint_slice bs 0 8 (by omega), uintBytes_readUint_slice bs 40 8 (by omega)]
      simp only [Nat.zero_add, Nat.reduceAdd]
      simp (config := {decide := true}) only [Array.extract_append_extract, Nat.min_def, Nat.max_def, ↓reduceIte]
      rw [← h]; simp
    rw [e]
    exact ⟨_, SszValue.roundtrip g⟩

/-- `len(buf) ≠ 144`: EthLib rejects. -/
theorem SszValue.spec_rejects (bs : Array UInt8) (h : bs.size ≠ 144) : ∃ e, deserialize desc bs = .error e := by
  cases hd : deserialize desc bs with
  | error e => exact ⟨e, rfl⟩
  | ok v => exact absurd ((SszValue.spec_accepts_iff bs).mp ⟨v, hd⟩) h

/-! ### The checker Desc decodes like the hand Desc (accepted inputs and values) -/

theorem checker_wellFormed : checkerDesc.wellFormed = .ok () := by rfl

theorem SszValue.serialize_eq_checker (g : SszValue) : serialize checkerDesc g.toValue = .ok (SszValue.encode g) := by
  rw [← desc_serialize_checker]; exact SszValue.serialize_eq g

theorem SszValue.toValue_fits_checker (g : SszValue) : Value.fits checkerDesc g.toValue = true := by
  have := g.slot.toNat_lt; have := g.validatorIndex.toNat_lt
  simp [checkerDesc, SszValue.toValue, Value.fits, Value.fieldsFit]; omega

theorem SszValue.toValue_surjective_checker (v : Value) (h : Value.fits checkerDesc v = true) :
    ∃ g : SszValue, g.toValue = v := by
  have h' : Value.fits desc v = true := by
    cases v <;> simp_all [desc, checkerDesc, Value.fits]
  exact SszValue.toValue_surjective' v h'

/-- **Codec equality on the accepted inputs**. -/
theorem desc_deserialize_checker (bs : Array UInt8) (v : Value) :
    deserialize desc bs = .ok v ↔ deserialize checkerDesc bs = .ok v := by
  constructor
  · intro h
    obtain ⟨g, rfl, hb⟩ := SszValue.accepted_is_encoding h
    rw [hb]
    exact deserialize_encoding (G := SszValue) (toV := SszValue.toValue) (enc := SszValue.encode) checker_wellFormed
      SszValue.serialize_eq_checker SszValue.toValue_fits_checker g
  · intro h
    obtain ⟨g, rfl, hb⟩ := accepted_input_is_encoding (G := SszValue) (toV := SszValue.toValue) (enc := SszValue.encode)
      checker_wellFormed SszValue.serialize_eq_checker SszValue.toValue_surjective_checker h
    rw [hb]; exact SszValue.roundtrip g

end Prysm.SyncCommitteeMessage
