import Prysm.Checkpoint.Spec
import Prysm.Checkpoint.SpecEquivalence
import E2eScal.F24Desc

/-!
# Spec bridge for the real Prysm `v1alpha1.BeaconBlocksByRangeRequest` (FLAT24 / H7)

Written by the FLAT24 evaluator with its evidence script `f24spec.py` (the text of `SmSpec.lean` / `SaSpec.lean`
generalised to a field list). `prysmBbrDesc` (`F24Desc.lean`) is the independent hand `Desc` (Prysm proto).
No Desc-checker record exists for this type (`gen/desc/results/main.result.json`): no codec equality here.
`PBbr` is the SSZ content of a Go `v1alpha1.BeaconBlocksByRangeRequest`.
-/

namespace E2e
open EthLib.Serialization.Ssz
open Spec hiding readUint_lt

theorem prysmBbrDesc_kinds : prysmBbrDesc = .container ["start_slot", "count", "step"]
      [.uint 8, .uint 8, .uint 8] := rfl

theorem prysmBbrDesc_wellFormed : prysmBbrDesc.wellFormed = .ok () := by rfl
theorem prysmBbrDesc_fixedSize : prysmBbrDesc.fixedSize = some 24 := by rfl

/-- The SSZ content of a Go `v1alpha1.BeaconBlocksByRangeRequest`. -/
structure PBbr where
  startSlot : UInt64
  count : UInt64
  step : UInt64

def PBbr.toValue (g : PBbr) : Value :=
  .seq [.uint g.startSlot.toNat, .uint g.count.toNat, .uint g.step.toNat]

def pbbrEnc (g : PBbr) : Array UInt8 :=
  uintBytes 8 g.startSlot.toNat ++ uintBytes 8 g.count.toNat ++ uintBytes 8 g.step.toNat

theorem pbbr_enc_size (g : PBbr) : (pbbrEnc g).size = 24 := by
  simp [pbbrEnc, Spec.uintBytes_size]

theorem pbbr_toValue_fits (g : PBbr) : Value.fits prysmBbrDesc g.toValue = true := by
  have := g.startSlot.toNat_lt; have := g.count.toNat_lt; have := g.step.toNat_lt
  simp only [prysmBbrDesc, PBbr.toValue, Value.fits, Value.fieldsFit] at *
  simp; omega

theorem pbbr_toValue_injective (g h : PBbr) (e : g.toValue = h.toValue) : g = h := by
  obtain ⟨a0, a1, a2⟩ := g; obtain ⟨b0, b1, b2⟩ := h
  simp only [PBbr.toValue, Value.seq.injEq, List.cons.injEq, Value.uint.injEq, Value.bytes.injEq,
    and_true] at e
  obtain ⟨e0, e1, e2⟩ := e
  rw [UInt64.toNat_inj.mp e0, UInt64.toNat_inj.mp e1, UInt64.toNat_inj.mp e2]

theorem pbbr_toValue_surjective' (v : Value) (h : Value.fits prysmBbrDesc v = true) : ∃ g : PBbr, g.toValue = v := by
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
      by simp [PBbr.toValue, Nat.mod_eq_of_lt ha0, Nat.mod_eq_of_lt ha1, Nat.mod_eq_of_lt ha2]⟩

theorem pbbr_serialize (g : PBbr) : serialize prysmBbrDesc g.toValue = .ok (pbbrEnc g) := by
  obtain ⟨a0, a1, a2⟩ := g
  have := a0.toNat_lt; have := a1.toNat_lt; have := a2.toNat_lt
  simp only [prysmBbrDesc, PBbr.toValue, serialize, serializeStruct, serializeFields, Vector.toArray_mk]
  simp (config := {decide := true}) [*, bind, Except.bind, pure, Except.pure, assemble, headWidth, bodyWidth,
    headOf, bodiesOf, Desc.isFixed, Desc.fixedSize, Spec.uintBytes_size, bytesPerOffset, pbbrEnc,
    Desc.fieldsFixedSize, Array.append_assoc]

/-- **Spec roundtrip.** -/
theorem pbbr_roundtrip (g : PBbr) : deserialize prysmBbrDesc (pbbrEnc g) = .ok g.toValue :=
  deserialize_enc (G := PBbr) (toV := PBbr.toValue) (enc := pbbrEnc) prysmBbrDesc_wellFormed pbbr_serialize
    pbbr_toValue_fits g

theorem pbbr_accepted_is_enc {bs : Array UInt8} {v : Value} (h : deserialize prysmBbrDesc bs = .ok v) :
    ∃ g : PBbr, v = g.toValue ∧ bs = pbbrEnc g :=
  accepted_is_enc (G := PBbr) (toV := PBbr.toValue) (enc := pbbrEnc) prysmBbrDesc_wellFormed pbbr_serialize
    pbbr_toValue_surjective' h

/-- **EthLib accepts exactly the 24-byte inputs.** -/
theorem pbbr_spec_accepts_iff (bs : Array UInt8) : (∃ v, deserialize prysmBbrDesc bs = .ok v) ↔ bs.size = 24 := by
  constructor
  · rintro ⟨v, hd⟩
    obtain ⟨g, rfl, hb⟩ := pbbr_accepted_is_enc hd
    rw [hb]; exact pbbr_enc_size g
  · intro h
    have r0 := readUint_lt bs 0 8
    have r1 := readUint_lt bs 8 8
    have r2 := readUint_lt bs 16 8
    simp only [Nat.reducePow, Nat.reduceMul] at r0 r1 r2
    let g : PBbr := ⟨UInt64.ofNat (readUint bs 0 8), UInt64.ofNat (readUint bs 8 8), UInt64.ofNat (readUint bs 16 8)⟩
    have e : bs = pbbrEnc g := by
      simp only [g, pbbrEnc, UInt64.toNat_ofNat_of_lt' r0, UInt64.toNat_ofNat_of_lt' r1, UInt64.toNat_ofNat_of_lt' r2, uintBytes_readUint_slice bs 0 8 (by omega), uintBytes_readUint_slice bs 8 8 (by omega), uintBytes_readUint_slice bs 16 8 (by omega)]
      simp only [Nat.zero_add, Nat.reduceAdd]
      simp (config := {decide := true}) only [Array.extract_append_extract, Nat.min_def, Nat.max_def, ↓reduceIte]
      rw [← h]; simp
    rw [e]
    exact ⟨_, pbbr_roundtrip g⟩

/-- `len(buf) ≠ 24`: EthLib rejects. -/
theorem pbbr_spec_rejects (bs : Array UInt8) (h : bs.size ≠ 24) : ∃ e, deserialize prysmBbrDesc bs = .error e := by
  cases hd : deserialize prysmBbrDesc bs with
  | error e => exact ⟨e, rfl⟩
  | ok v => exact absurd ((pbbr_spec_accepts_iff bs).mp ⟨v, hd⟩) h

end E2e
