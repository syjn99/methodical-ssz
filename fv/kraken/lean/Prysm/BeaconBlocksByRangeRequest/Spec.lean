import Prysm.Checkpoint.Spec
import Prysm.Checkpoint.SpecEquivalence
import Prysm.DepositRequest.SpecDescription

/-!
# Spec bridge for the real Prysm `v1alpha1.BeaconBlocksByRangeRequest` (24 flat hold-out types)

Written by the evidence script `flat_types_spec.py` (the text of `Prysm/SyncCommitteeMessage/Spec.lean` / `Prysm/SyncAggregatorSelectionData/Spec.lean`
generalised to a field list). `desc` (`Prysm/BeaconBlocksByRangeRequest/SpecDescription.lean`) is the independent hand `Desc` (Prysm proto).
No Desc-checker record exists for this type (`gen/desc/results/main.result.json`): no codec equality here.
`SszValue` is the SSZ content of a Go `v1alpha1.BeaconBlocksByRangeRequest`.
-/

namespace Prysm.BeaconBlocksByRangeRequest
open EthLib.Serialization.Ssz
open Spec hiding readUint_lt

theorem desc_kinds : desc = .container ["start_slot", "count", "step"]
      [.uint 8, .uint 8, .uint 8] := rfl

theorem desc_wellFormed : desc.wellFormed = .ok () := by rfl
theorem desc_fixedSize : desc.fixedSize = some 24 := by rfl

/-- The SSZ content of a Go `v1alpha1.BeaconBlocksByRangeRequest`. -/
structure SszValue where
  startSlot : UInt64
  count : UInt64
  step : UInt64

def SszValue.toValue (g : SszValue) : Value :=
  .seq [.uint g.startSlot.toNat, .uint g.count.toNat, .uint g.step.toNat]

def SszValue.encode (g : SszValue) : Array UInt8 :=
  uintBytes 8 g.startSlot.toNat ++ uintBytes 8 g.count.toNat ++ uintBytes 8 g.step.toNat

theorem SszValue.enc_size (g : SszValue) : (SszValue.encode g).size = 24 := by
  simp [SszValue.encode, Spec.uintBytes_size]

theorem SszValue.toValue_fits (g : SszValue) : Value.fits desc g.toValue = true := by
  have := g.startSlot.toNat_lt; have := g.count.toNat_lt; have := g.step.toNat_lt
  simp only [desc, SszValue.toValue, Value.fits, Value.fieldsFit] at *
  simp; omega

theorem SszValue.toValue_injective (g h : SszValue) (e : g.toValue = h.toValue) : g = h := by
  obtain ⟨a0, a1, a2⟩ := g; obtain ⟨b0, b1, b2⟩ := h
  simp only [SszValue.toValue, Value.seq.injEq, List.cons.injEq, Value.uint.injEq, Value.bytes.injEq,
    and_true] at e
  obtain ⟨e0, e1, e2⟩ := e
  rw [UInt64.toNat_inj.mp e0, UInt64.toNat_inj.mp e1, UInt64.toNat_inj.mp e2]

theorem SszValue.toValue_surjective' (v : Value) (h : Value.fits desc v = true) : ∃ g : SszValue, g.toValue = v := by
  obtain ⟨vs, rfl, hf⟩ := fits_container h
  have hl := fieldsFit_length hf
  match vs, hl with
  | [v0, v1, v2], _ =>
    simp only [fieldsFit_cons] at hf
    obtain ⟨h0, h1, h2, -⟩ := hf
    obtain ⟨a0, rfl, ha0⟩ := fits_uint h0
    obtain ⟨a1, rfl, ha1⟩ := fits_uint h1
    obtain ⟨a2, rfl, ha2⟩ := fits_uint h2
    simp only [Nat.reduceMul, Nat.reducePow] at ha0 ha1 ha2
    exact ⟨⟨UInt64.ofNat a0, UInt64.ofNat a1, UInt64.ofNat a2⟩,
      by simp [SszValue.toValue, Nat.mod_eq_of_lt ha0, Nat.mod_eq_of_lt ha1, Nat.mod_eq_of_lt ha2]⟩

theorem SszValue.serialize_eq (g : SszValue) : serialize desc g.toValue = .ok (SszValue.encode g) := by
  obtain ⟨a0, a1, a2⟩ := g
  have := a0.toNat_lt; have := a1.toNat_lt; have := a2.toNat_lt
  simp only [desc, SszValue.toValue, serialize, serializeStruct, serializeFields, Vector.toArray_mk]
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

/-- **EthLib accepts exactly the 24-byte inputs.** -/
theorem SszValue.spec_accepts_iff (bs : Array UInt8) : (∃ v, deserialize desc bs = .ok v) ↔ bs.size = 24 := by
  constructor
  · rintro ⟨v, hd⟩
    obtain ⟨g, rfl, hb⟩ := SszValue.accepted_is_encoding hd
    rw [hb]; exact SszValue.enc_size g
  · intro h
    have r0 := readUint_lt bs 0 8
    have r1 := readUint_lt bs 8 8
    have r2 := readUint_lt bs 16 8
    simp only [Nat.reducePow, Nat.reduceMul] at r0 r1 r2
    let g : SszValue := ⟨UInt64.ofNat (readUint bs 0 8), UInt64.ofNat (readUint bs 8 8), UInt64.ofNat (readUint bs 16 8)⟩
    have e : bs = SszValue.encode g := by
      simp only [g, SszValue.encode, UInt64.toNat_ofNat_of_lt' r0, UInt64.toNat_ofNat_of_lt' r1, UInt64.toNat_ofNat_of_lt' r2, uintBytes_readUint_slice bs 0 8 (by omega), uintBytes_readUint_slice bs 8 8 (by omega), uintBytes_readUint_slice bs 16 8 (by omega)]
      simp only [Nat.zero_add, Nat.reduceAdd]
      simp (config := {decide := true}) only [Array.extract_append_extract, Nat.min_def, Nat.max_def, ↓reduceIte]
      rw [← h]; simp
    rw [e]
    exact ⟨_, SszValue.roundtrip g⟩

/-- `len(buf) ≠ 24`: EthLib rejects. -/
theorem SszValue.spec_rejects (bs : Array UInt8) (h : bs.size ≠ 24) : ∃ e, deserialize desc bs = .error e := by
  cases hd : deserialize desc bs with
  | error e => exact ⟨e, rfl⟩
  | ok v => exact absurd ((SszValue.spec_accepts_iff bs).mp ⟨v, hd⟩) h

end Prysm.BeaconBlocksByRangeRequest
