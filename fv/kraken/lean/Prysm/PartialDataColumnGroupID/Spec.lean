import Prysm.Checkpoint.Spec
import Prysm.Checkpoint.SpecEquivalence
import Prysm.DepositRequest.SpecDescription

/-!
# Spec bridge for the real Prysm `v1alpha1.PartialDataColumnGroupID` (FLAT24 / H7)

Written by the FLAT24 evaluator with its evidence script `f24spec.py` (the text of `Prysm/SyncCommitteeMessage/Spec.lean` / `Prysm/SyncAggregatorSelectionData/Spec.lean`
generalised to a field list). `desc` (`Prysm/PartialDataColumnGroupID/SpecDescription.lean`) is the independent hand `Desc` (Prysm proto).
No Desc-checker record exists for this type (`gen/desc/results/main.result.json`): no codec equality here.
`SszValue` is the SSZ content of a Go `v1alpha1.PartialDataColumnGroupID`.
-/

namespace Prysm.PartialDataColumnGroupID
open EthLib.Serialization.Ssz
open Spec hiding readUint_lt

theorem desc_kinds : desc = .container ["beacon_block_root", "slot"]
      [.byteVector 32, .uint 8] := rfl

theorem desc_wellFormed : desc.wellFormed = .ok () := by rfl
theorem desc_fixedSize : desc.fixedSize = some 40 := by rfl

/-- The SSZ content of a Go `v1alpha1.PartialDataColumnGroupID`. -/
structure SszValue where
  beaconBlockRoot : Vector UInt8 32
  slot : UInt64

def SszValue.toValue (g : SszValue) : Value :=
  .seq [.bytes g.beaconBlockRoot.toArray, .uint g.slot.toNat]

def SszValue.encode (g : SszValue) : Array UInt8 :=
  g.beaconBlockRoot.toArray ++ uintBytes 8 g.slot.toNat

theorem SszValue.enc_size (g : SszValue) : (SszValue.encode g).size = 40 := by
  simp [SszValue.encode, Spec.uintBytes_size]

theorem SszValue.toValue_fits (g : SszValue) : Value.fits desc g.toValue = true := by
  have := g.slot.toNat_lt
  simp only [desc, SszValue.toValue, Value.fits, Value.fieldsFit] at *
  simp; omega

theorem SszValue.toValue_injective (g h : SszValue) (e : g.toValue = h.toValue) : g = h := by
  obtain ⟨a0, a1⟩ := g; obtain ⟨b0, b1⟩ := h
  simp only [SszValue.toValue, Value.seq.injEq, List.cons.injEq, Value.uint.injEq, Value.bytes.injEq,
    and_true] at e
  obtain ⟨e0, e1⟩ := e
  rw [Vector.toArray_inj.mp e0, UInt64.toNat_inj.mp e1]

theorem SszValue.toValue_surjective' (v : Value) (h : Value.fits desc v = true) : ∃ g : SszValue, g.toValue = v := by
  obtain ⟨vs, rfl, hf⟩ := fits_container h
  have hl := fieldsFit_length hf
  match vs, hl with
  | [v0, v1], _ =>
    simp only [fieldsFit_cons] at hf
    obtain ⟨h0, h1, -⟩ := hf
    obtain ⟨a0, rfl, ha0⟩ : ∃ d, v0 = .bytes d ∧ d.size = 32 := by
      cases v0 <;> simp [Value.fits] at h0 ⊢; exact h0
    obtain ⟨a1, rfl, ha1⟩ := fits_uint h1
    simp only [Nat.reduceMul, Nat.reducePow] at ha1
    exact ⟨⟨⟨a0, ha0⟩, UInt64.ofNat a1⟩,
      by simp [SszValue.toValue, Nat.mod_eq_of_lt ha1]⟩

theorem SszValue.serialize_eq (g : SszValue) : serialize desc g.toValue = .ok (SszValue.encode g) := by
  obtain ⟨⟨r0, hr0⟩, a1⟩ := g
  have := a1.toNat_lt
  simp only [desc, SszValue.toValue, serialize, serializeStruct, serializeFields, Vector.toArray_mk, hr0]
  simp (config := {decide := true}) [*, bind, Except.bind, pure, Except.pure, assemble, headWidth, bodyWidth,
    headOf, bodiesOf, Desc.isFixed, Desc.fixedSize, Spec.uintBytes_size, bytesPerOffset, SszValue.encode,
    Desc.fieldsFixedSize, Array.append_assoc]

/-- **Spec roundtrip.** -/
theorem SszValue.roundtrip (g : SszValue) : deserialize desc (SszValue.encode g) = .ok g.toValue :=
  deserialize_enc (G := SszValue) (toV := SszValue.toValue) (enc := SszValue.encode) desc_wellFormed SszValue.serialize_eq
    SszValue.toValue_fits g

theorem SszValue.accepted_is_encoding {bs : Array UInt8} {v : Value} (h : deserialize desc bs = .ok v) :
    ∃ g : SszValue, v = g.toValue ∧ bs = SszValue.encode g :=
  accepted_is_enc (G := SszValue) (toV := SszValue.toValue) (enc := SszValue.encode) desc_wellFormed SszValue.serialize_eq
    SszValue.toValue_surjective' h

/-- **EthLib accepts exactly the 40-byte inputs.** -/
theorem SszValue.spec_accepts_iff (bs : Array UInt8) : (∃ v, deserialize desc bs = .ok v) ↔ bs.size = 40 := by
  constructor
  · rintro ⟨v, hd⟩
    obtain ⟨g, rfl, hb⟩ := SszValue.accepted_is_encoding hd
    rw [hb]; exact SszValue.enc_size g
  · intro h
    have r1 := readUint_lt bs 32 8
    simp only [Nat.reducePow, Nat.reduceMul] at r1
    let g : SszValue := ⟨⟨bs.extract 0 32, by simp; omega⟩, UInt64.ofNat (readUint bs 32 8)⟩
    have e : bs = SszValue.encode g := by
      simp only [g, SszValue.encode, UInt64.toNat_ofNat_of_lt' r1, uintBytes_readUint_slice bs 32 8 (by omega)]
      simp only [Nat.zero_add, Nat.reduceAdd]
      simp (config := {decide := true}) only [Array.extract_append_extract, Nat.min_def, Nat.max_def, ↓reduceIte]
      rw [← h]; simp
    rw [e]
    exact ⟨_, SszValue.roundtrip g⟩

/-- `len(buf) ≠ 40`: EthLib rejects. -/
theorem SszValue.spec_rejects (bs : Array UInt8) (h : bs.size ≠ 40) : ∃ e, deserialize desc bs = .error e := by
  cases hd : deserialize desc bs with
  | error e => exact ⟨e, rfl⟩
  | ok v => exact absurd ((SszValue.spec_accepts_iff bs).mp ⟨v, hd⟩) h

end Prysm.PartialDataColumnGroupID
