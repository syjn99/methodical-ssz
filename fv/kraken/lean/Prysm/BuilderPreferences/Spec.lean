import Prysm.Checkpoint.Spec
import Prysm.Checkpoint.SpecEquivalence
import Prysm.DepositRequest.SpecDescription

/-!
# Spec bridge for the real Prysm `v1alpha1.BuilderPreferences` (24 flat hold-out types)

Written by the evidence script `f24spec.py` (the text of `Prysm/SyncCommitteeMessage/Spec.lean` / `Prysm/SyncAggregatorSelectionData/Spec.lean`
generalised to a field list). `desc` (`Prysm/BuilderPreferences/SpecDescription.lean`) is the independent hand `Desc` (Prysm proto).
No Desc-checker record exists for this type (`gen/desc/results/main.result.json`): no codec equality here.
`SszValue` is the SSZ content of a Go `v1alpha1.BuilderPreferences`.
-/

namespace Prysm.BuilderPreferences
open EthLib.Serialization.Ssz
open Spec hiding readUint_lt

theorem desc_kinds : desc = .container ["max_execution_payment"]
      [.uint 8] := rfl

theorem desc_wellFormed : desc.wellFormed = .ok () := by rfl
theorem desc_fixedSize : desc.fixedSize = some 8 := by rfl

/-- The SSZ content of a Go `v1alpha1.BuilderPreferences`. -/
structure SszValue where
  maxExecutionPayment : UInt64

def SszValue.toValue (g : SszValue) : Value :=
  .seq [.uint g.maxExecutionPayment.toNat]

def SszValue.encode (g : SszValue) : Array UInt8 :=
  uintBytes 8 g.maxExecutionPayment.toNat

theorem SszValue.enc_size (g : SszValue) : (SszValue.encode g).size = 8 := by
  simp [SszValue.encode, Spec.uintBytes_size]

theorem SszValue.toValue_fits (g : SszValue) : Value.fits desc g.toValue = true := by
  have := g.maxExecutionPayment.toNat_lt
  simp only [desc, SszValue.toValue, Value.fits, Value.fieldsFit] at *
  simp; omega

theorem SszValue.toValue_injective (g h : SszValue) (e : g.toValue = h.toValue) : g = h := by
  obtain ⟨a0⟩ := g; obtain ⟨b0⟩ := h
  simp only [SszValue.toValue, Value.seq.injEq, List.cons.injEq, Value.uint.injEq, Value.bytes.injEq,
    and_true] at e
  rw [UInt64.toNat_inj.mp e]

theorem SszValue.toValue_surjective' (v : Value) (h : Value.fits desc v = true) : ∃ g : SszValue, g.toValue = v := by
  obtain ⟨vs, rfl, hf⟩ := fits_container h
  have hl := fieldsFit_length hf
  match vs, hl with
  | [v0], _ =>
    simp only [fieldsFit_cons] at hf
    obtain ⟨h0, -⟩ := hf
    obtain ⟨a0, rfl, ha0⟩ := fits_uint h0
    simp only [Nat.reduceMul, Nat.reducePow] at ha0
    exact ⟨⟨UInt64.ofNat a0⟩,
      by simp [SszValue.toValue, Nat.mod_eq_of_lt ha0]⟩

theorem SszValue.serialize_eq (g : SszValue) : serialize desc g.toValue = .ok (SszValue.encode g) := by
  obtain ⟨a0⟩ := g
  have := a0.toNat_lt
  simp only [desc, SszValue.toValue, serialize, serializeStruct, serializeFields, Vector.toArray_mk]
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

/-- **EthLib accepts exactly the 8-byte inputs.** -/
theorem SszValue.spec_accepts_iff (bs : Array UInt8) : (∃ v, deserialize desc bs = .ok v) ↔ bs.size = 8 := by
  constructor
  · rintro ⟨v, hd⟩
    obtain ⟨g, rfl, hb⟩ := SszValue.accepted_is_encoding hd
    rw [hb]; exact SszValue.enc_size g
  · intro h
    have r0 := readUint_lt bs 0 8
    simp only [Nat.reducePow, Nat.reduceMul] at r0
    let g : SszValue := ⟨UInt64.ofNat (readUint bs 0 8)⟩
    have e : bs = SszValue.encode g := by
      simp only [g, SszValue.encode, UInt64.toNat_ofNat_of_lt' r0, uintBytes_readUint_slice bs 0 8 (by omega)]
      try simp only [Nat.zero_add, Nat.reduceAdd]
      try simp (config := {decide := true}) only [Array.extract_append_extract, Nat.min_def, Nat.max_def, ↓reduceIte]
      rw [← h]; simp
    rw [e]
    exact ⟨_, SszValue.roundtrip g⟩

/-- `len(buf) ≠ 8`: EthLib rejects. -/
theorem SszValue.spec_rejects (bs : Array UInt8) (h : bs.size ≠ 8) : ∃ e, deserialize desc bs = .error e := by
  cases hd : deserialize desc bs with
  | error e => exact ⟨e, rfl⟩
  | ok v => exact absurd ((SszValue.spec_accepts_iff bs).mp ⟨v, hd⟩) h

end Prysm.BuilderPreferences
