import E2e.Spec
import E2e.SpecEq
import E2eScal.F24Desc

/-!
# Spec bridge for the real Prysm `v1alpha1.ExecutionPayloadEnvelopesByRangeRequest` (FLAT24 / H7)

Written by the FLAT24 evaluator with its evidence script `f24spec.py` (the text of `SmSpec.lean` / `SaSpec.lean`
generalised to a field list). `prysmEprDesc` (`F24Desc.lean`) is the independent hand `Desc` (Prysm proto).
No Desc-checker record exists for this type (`gen/desc/results/main.result.json`): no codec equality here.
`PEpr` is the SSZ content of a Go `v1alpha1.ExecutionPayloadEnvelopesByRangeRequest`.
-/

namespace E2e
open EthLib.Serialization.Ssz
open Spec hiding readUint_lt

theorem prysmEprDesc_kinds : prysmEprDesc = .container ["start_slot", "count"]
      [.uint 8, .uint 8] := rfl

theorem prysmEprDesc_wellFormed : prysmEprDesc.wellFormed = .ok () := by rfl
theorem prysmEprDesc_fixedSize : prysmEprDesc.fixedSize = some 16 := by rfl

/-- The SSZ content of a Go `v1alpha1.ExecutionPayloadEnvelopesByRangeRequest`. -/
structure PEpr where
  startSlot : UInt64
  count : UInt64

def PEpr.toValue (g : PEpr) : Value :=
  .seq [.uint g.startSlot.toNat, .uint g.count.toNat]

def peprEnc (g : PEpr) : Array UInt8 :=
  uintBytes 8 g.startSlot.toNat ++ uintBytes 8 g.count.toNat

theorem pepr_enc_size (g : PEpr) : (peprEnc g).size = 16 := by
  simp [peprEnc, Spec.uintBytes_size]

theorem pepr_toValue_fits (g : PEpr) : Value.fits prysmEprDesc g.toValue = true := by
  have := g.startSlot.toNat_lt; have := g.count.toNat_lt
  simp only [prysmEprDesc, PEpr.toValue, Value.fits, Value.fieldsFit] at *
  simp; omega

theorem pepr_toValue_injective (g h : PEpr) (e : g.toValue = h.toValue) : g = h := by
  obtain ⟨a0, a1⟩ := g; obtain ⟨b0, b1⟩ := h
  simp only [PEpr.toValue, Value.seq.injEq, List.cons.injEq, Value.uint.injEq, Value.bytes.injEq,
    and_true] at e
  obtain ⟨e0, e1⟩ := e
  rw [UInt64.toNat_inj.mp e0, UInt64.toNat_inj.mp e1]

theorem pepr_toValue_surjective' (v : Value) (h : Value.fits prysmEprDesc v = true) : ∃ g : PEpr, g.toValue = v := by
  obtain ⟨vs, rfl, hf⟩ := fits_container h
  have hl := fieldsFit_length hf
  match vs, hl with
  | [v0, v1], _ =>
    simp only [fieldsFit_cons] at hf
    obtain ⟨h0, h1, -⟩ := hf
    obtain ⟨a0, rfl, ha0⟩ := fits_uint h0
    obtain ⟨a1, rfl, ha1⟩ := fits_uint h1
    simp only [Nat.reduceMul, Nat.reducePow] at ha0 ha1
    exact ⟨⟨UInt64.ofNat a0, UInt64.ofNat a1⟩,
      by simp [PEpr.toValue, Nat.mod_eq_of_lt ha0, Nat.mod_eq_of_lt ha1]⟩

theorem pepr_serialize (g : PEpr) : serialize prysmEprDesc g.toValue = .ok (peprEnc g) := by
  obtain ⟨a0, a1⟩ := g
  have := a0.toNat_lt; have := a1.toNat_lt
  simp only [prysmEprDesc, PEpr.toValue, serialize, serializeStruct, serializeFields, Vector.toArray_mk]
  simp (config := {decide := true}) [*, bind, Except.bind, pure, Except.pure, assemble, headWidth, bodyWidth,
    headOf, bodiesOf, Desc.isFixed, Desc.fixedSize, Spec.uintBytes_size, bytesPerOffset, peprEnc,
    Desc.fieldsFixedSize, Array.append_assoc]

/-- **Spec roundtrip.** -/
theorem pepr_roundtrip (g : PEpr) : deserialize prysmEprDesc (peprEnc g) = .ok g.toValue :=
  deserialize_enc (G := PEpr) (toV := PEpr.toValue) (enc := peprEnc) prysmEprDesc_wellFormed pepr_serialize
    pepr_toValue_fits g

theorem pepr_accepted_is_enc {bs : Array UInt8} {v : Value} (h : deserialize prysmEprDesc bs = .ok v) :
    ∃ g : PEpr, v = g.toValue ∧ bs = peprEnc g :=
  accepted_is_enc (G := PEpr) (toV := PEpr.toValue) (enc := peprEnc) prysmEprDesc_wellFormed pepr_serialize
    pepr_toValue_surjective' h

/-- **EthLib accepts exactly the 16-byte inputs.** -/
theorem pepr_spec_accepts_iff (bs : Array UInt8) : (∃ v, deserialize prysmEprDesc bs = .ok v) ↔ bs.size = 16 := by
  constructor
  · rintro ⟨v, hd⟩
    obtain ⟨g, rfl, hb⟩ := pepr_accepted_is_enc hd
    rw [hb]; exact pepr_enc_size g
  · intro h
    have r0 := readUint_lt bs 0 8
    have r1 := readUint_lt bs 8 8
    simp only [Nat.reducePow, Nat.reduceMul] at r0 r1
    let g : PEpr := ⟨UInt64.ofNat (readUint bs 0 8), UInt64.ofNat (readUint bs 8 8)⟩
    have e : bs = peprEnc g := by
      simp only [g, peprEnc, UInt64.toNat_ofNat_of_lt' r0, UInt64.toNat_ofNat_of_lt' r1, uintBytes_readUint_slice bs 0 8 (by omega), uintBytes_readUint_slice bs 8 8 (by omega)]
      simp only [Nat.zero_add, Nat.reduceAdd]
      simp (config := {decide := true}) only [Array.extract_append_extract, Nat.min_def, Nat.max_def, ↓reduceIte]
      rw [← h]; simp
    rw [e]
    exact ⟨_, pepr_roundtrip g⟩

/-- `len(buf) ≠ 16`: EthLib rejects. -/
theorem pepr_spec_rejects (bs : Array UInt8) (h : bs.size ≠ 16) : ∃ e, deserialize prysmEprDesc bs = .error e := by
  cases hd : deserialize prysmEprDesc bs with
  | error e => exact ⟨e, rfl⟩
  | ok v => exact absurd ((pepr_spec_accepts_iff bs).mp ⟨v, hd⟩) h

end E2e
