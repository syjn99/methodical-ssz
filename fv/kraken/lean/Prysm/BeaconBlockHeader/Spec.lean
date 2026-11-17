import Spec.TestScalars
import Spec.DeserializeOfSerialize
import Prysm.BeaconBlockHeader.SpecDescription
import Prysm.BeaconBlockHeader.SpecChecker

/-!
# Spec bridge for the Prysm `v1alpha1.BeaconBlockHeader`

Written by `gen/flat-types/flat_types_spec.py`.
`desc` (`Prysm/BeaconBlockHeader/SpecDescription.lean`) is the independent hand `Desc`, written from consensus-specs.
`checkerDesc` (`Prysm/BeaconBlockHeader/SpecChecker.lean`, rendered by `gen/checks/desc_to_lean.py`) is the Desc checker's Desc of the type
(the producer output recorded in `gen/desc/results/main.result.json`, same sha256; copy in `prysm/go1.26.10/evidence/`).
`SszValue` is the SSZ content of a Go `v1alpha1.BeaconBlockHeader`.
-/

namespace Prysm.BeaconBlockHeader
open EthLib.Serialization.Ssz
open Spec hiding readUint_lt

theorem desc_kinds : desc = .container ["slot", "proposer_index", "parent_root", "state_root", "body_root"]
      [.uint 8, .uint 8, .byteVector 32, .byteVector 32, .byteVector 32] := rfl

theorem desc_wellFormed : desc.wellFormed = .ok () := by rfl
theorem desc_fixedSize : desc.fixedSize = some 112 := by rfl

/-- EthLib's `serialize` ignores container names. -/
theorem desc_serialize_checker (v : Value) : serialize desc v = serialize checkerDesc v := by
  unfold desc checkerDesc
  cases v <;> (try simp only [serialize, serializeStruct]) <;> rfl

/-- The SSZ content of a Go `v1alpha1.BeaconBlockHeader`. -/
structure SszValue where
  slot : UInt64
  proposer : UInt64
  parent : Vector UInt8 32
  state : Vector UInt8 32
  body : Vector UInt8 32

def SszValue.toValue (g : SszValue) : Value :=
  .seq [.uint g.slot.toNat, .uint g.proposer.toNat, .bytes g.parent.toArray, .bytes g.state.toArray, .bytes g.body.toArray]

def SszValue.encode (g : SszValue) : Array UInt8 :=
  uintBytes 8 g.slot.toNat ++ uintBytes 8 g.proposer.toNat ++ g.parent.toArray ++ g.state.toArray ++ g.body.toArray

theorem SszValue.encode_size (g : SszValue) : (SszValue.encode g).size = 112 := by
  simp [SszValue.encode, Spec.uintBytes_size]

theorem SszValue.toValue_fits (g : SszValue) : Value.fits desc g.toValue = true := by
  have := g.slot.toNat_lt; have := g.proposer.toNat_lt
  simp only [desc, SszValue.toValue, Value.fits, Value.fieldsFit] at *
  simp; omega

theorem SszValue.toValue_injective (g h : SszValue) (e : g.toValue = h.toValue) : g = h := by
  obtain ⟨a0, a1, a2, a3, a4⟩ := g; obtain ⟨b0, b1, b2, b3, b4⟩ := h
  simp only [SszValue.toValue, Value.seq.injEq, List.cons.injEq, Value.uint.injEq, Value.bytes.injEq,
    and_true] at e
  obtain ⟨e0, e1, e2, e3, e4⟩ := e
  rw [UInt64.toNat_inj.mp e0, UInt64.toNat_inj.mp e1, Vector.toArray_inj.mp e2, Vector.toArray_inj.mp e3, Vector.toArray_inj.mp e4]

theorem SszValue.toValue_surjective' (v : Value) (h : Value.fits desc v = true) : ∃ g : SszValue, g.toValue = v := by
  obtain ⟨vs, rfl, hf⟩ := fits_container h
  have hl := fieldsFit_length hf
  match vs, hl with
  | [v0, v1, v2, v3, v4], _ =>
    simp only [fieldsFit_cons] at hf
    obtain ⟨h0, h1, h2, h3, h4, -⟩ := hf
    obtain ⟨a0, rfl, ha0⟩ := fits_uint h0
    obtain ⟨a1, rfl, ha1⟩ := fits_uint h1
    obtain ⟨a2, rfl, ha2⟩ : ∃ d, v2 = .bytes d ∧ d.size = 32 := by
      cases v2 <;> simp [Value.fits] at h2 ⊢; exact h2
    obtain ⟨a3, rfl, ha3⟩ : ∃ d, v3 = .bytes d ∧ d.size = 32 := by
      cases v3 <;> simp [Value.fits] at h3 ⊢; exact h3
    obtain ⟨a4, rfl, ha4⟩ : ∃ d, v4 = .bytes d ∧ d.size = 32 := by
      cases v4 <;> simp [Value.fits] at h4 ⊢; exact h4
    simp only [Nat.reduceMul, Nat.reducePow] at ha0 ha1
    exact ⟨⟨UInt64.ofNat a0, UInt64.ofNat a1, ⟨a2, ha2⟩, ⟨a3, ha3⟩, ⟨a4, ha4⟩⟩,
      by simp [SszValue.toValue, Nat.mod_eq_of_lt ha0, Nat.mod_eq_of_lt ha1]⟩

theorem SszValue.serialize_eq (g : SszValue) : serialize desc g.toValue = .ok (SszValue.encode g) := by
  obtain ⟨a0, a1, ⟨r2, hr2⟩, ⟨r3, hr3⟩, ⟨r4, hr4⟩⟩ := g
  have := a0.toNat_lt; have := a1.toNat_lt
  simp only [desc, SszValue.toValue, serialize, serializeStruct, serializeFields, Vector.toArray_mk, hr2, hr3, hr4]
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

/-- **EthLib accepts exactly the 112-byte inputs.** -/
theorem SszValue.spec_accepts_iff (bs : Array UInt8) : (∃ v, deserialize desc bs = .ok v) ↔ bs.size = 112 := by
  constructor
  · rintro ⟨v, hd⟩
    obtain ⟨g, rfl, hb⟩ := SszValue.accepted_is_encoding hd
    rw [hb]; exact SszValue.encode_size g
  · intro h
    have r0 := readUint_lt bs 0 8
    have r1 := readUint_lt bs 8 8
    simp only [Nat.reducePow, Nat.reduceMul] at r0 r1
    let g : SszValue := ⟨UInt64.ofNat (readUint bs 0 8), UInt64.ofNat (readUint bs 8 8), ⟨bs.extract 16 48, by simp; omega⟩, ⟨bs.extract 48 80, by simp; omega⟩, ⟨bs.extract 80 112, by simp; omega⟩⟩
    have e : bs = SszValue.encode g := by
      simp only [g, SszValue.encode, UInt64.toNat_ofNat_of_lt' r0, UInt64.toNat_ofNat_of_lt' r1, uintBytes_readUint_slice bs 0 8 (by omega), uintBytes_readUint_slice bs 8 8 (by omega)]
      simp only [Nat.zero_add, Nat.reduceAdd]
      simp (config := {decide := true}) only [Array.extract_append_extract, Nat.min_def, Nat.max_def, ↓reduceIte]
      rw [← h]; simp
    rw [e]
    exact ⟨_, SszValue.roundtrip g⟩

/-- `len(buf) ≠ 112`: EthLib rejects. -/
theorem SszValue.spec_rejects (bs : Array UInt8) (h : bs.size ≠ 112) : ∃ e, deserialize desc bs = .error e := by
  cases hd : deserialize desc bs with
  | error e => exact ⟨e, rfl⟩
  | ok v => exact absurd ((SszValue.spec_accepts_iff bs).mp ⟨v, hd⟩) h

/-! ### The checker Desc decodes like the hand Desc (accepted inputs and values) -/

theorem checker_wellFormed : checkerDesc.wellFormed = .ok () := by rfl

theorem SszValue.serialize_eq_checker (g : SszValue) : serialize checkerDesc g.toValue = .ok (SszValue.encode g) := by
  rw [← desc_serialize_checker]; exact SszValue.serialize_eq g

theorem SszValue.toValue_fits_checker (g : SszValue) : Value.fits checkerDesc g.toValue = true := by
  have := g.slot.toNat_lt; have := g.proposer.toNat_lt
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

end Prysm.BeaconBlockHeader
