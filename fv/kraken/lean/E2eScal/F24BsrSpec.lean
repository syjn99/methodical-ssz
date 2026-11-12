import Prysm.Checkpoint.Spec
import Prysm.Checkpoint.SpecEquivalence
import E2eScal.F24Desc

/-!
# Spec bridge for the real Prysm `v1alpha1.BlobSidecarsByRangeRequest` (FLAT24 / H7)

Written by the FLAT24 evaluator with its evidence script `f24spec.py` (the text of `SmSpec.lean` / `SaSpec.lean`
generalised to a field list). `prysmBsrDesc` (`F24Desc.lean`) is the independent hand `Desc` (Prysm proto).
No Desc-checker record exists for this type (`gen/desc/results/main.result.json`): no codec equality here.
`PBsr` is the SSZ content of a Go `v1alpha1.BlobSidecarsByRangeRequest`.
-/

namespace E2e
open EthLib.Serialization.Ssz
open Spec hiding readUint_lt

theorem prysmBsrDesc_kinds : prysmBsrDesc = .container ["start_slot", "count"]
      [.uint 8, .uint 8] := rfl

theorem prysmBsrDesc_wellFormed : prysmBsrDesc.wellFormed = .ok () := by rfl
theorem prysmBsrDesc_fixedSize : prysmBsrDesc.fixedSize = some 16 := by rfl

/-- The SSZ content of a Go `v1alpha1.BlobSidecarsByRangeRequest`. -/
structure PBsr where
  startSlot : UInt64
  count : UInt64

def PBsr.toValue (g : PBsr) : Value :=
  .seq [.uint g.startSlot.toNat, .uint g.count.toNat]

def pbsrEnc (g : PBsr) : Array UInt8 :=
  uintBytes 8 g.startSlot.toNat ++ uintBytes 8 g.count.toNat

theorem pbsr_enc_size (g : PBsr) : (pbsrEnc g).size = 16 := by
  simp [pbsrEnc, Spec.uintBytes_size]

theorem pbsr_toValue_fits (g : PBsr) : Value.fits prysmBsrDesc g.toValue = true := by
  have := g.startSlot.toNat_lt; have := g.count.toNat_lt
  simp only [prysmBsrDesc, PBsr.toValue, Value.fits, Value.fieldsFit] at *
  simp; omega

theorem pbsr_toValue_injective (g h : PBsr) (e : g.toValue = h.toValue) : g = h := by
  obtain ⟨a0, a1⟩ := g; obtain ⟨b0, b1⟩ := h
  simp only [PBsr.toValue, Value.seq.injEq, List.cons.injEq, Value.uint.injEq, Value.bytes.injEq,
    and_true] at e
  obtain ⟨e0, e1⟩ := e
  rw [UInt64.toNat_inj.mp e0, UInt64.toNat_inj.mp e1]

theorem pbsr_toValue_surjective' (v : Value) (h : Value.fits prysmBsrDesc v = true) : ∃ g : PBsr, g.toValue = v := by
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
      by simp [PBsr.toValue, Nat.mod_eq_of_lt ha0, Nat.mod_eq_of_lt ha1]⟩

theorem pbsr_serialize (g : PBsr) : serialize prysmBsrDesc g.toValue = .ok (pbsrEnc g) := by
  obtain ⟨a0, a1⟩ := g
  have := a0.toNat_lt; have := a1.toNat_lt
  simp only [prysmBsrDesc, PBsr.toValue, serialize, serializeStruct, serializeFields, Vector.toArray_mk]
  simp (config := {decide := true}) [*, bind, Except.bind, pure, Except.pure, assemble, headWidth, bodyWidth,
    headOf, bodiesOf, Desc.isFixed, Desc.fixedSize, Spec.uintBytes_size, bytesPerOffset, pbsrEnc,
    Desc.fieldsFixedSize, Array.append_assoc]

/-- **Spec roundtrip.** -/
theorem pbsr_roundtrip (g : PBsr) : deserialize prysmBsrDesc (pbsrEnc g) = .ok g.toValue :=
  deserialize_enc (G := PBsr) (toV := PBsr.toValue) (enc := pbsrEnc) prysmBsrDesc_wellFormed pbsr_serialize
    pbsr_toValue_fits g

theorem pbsr_accepted_is_enc {bs : Array UInt8} {v : Value} (h : deserialize prysmBsrDesc bs = .ok v) :
    ∃ g : PBsr, v = g.toValue ∧ bs = pbsrEnc g :=
  accepted_is_enc (G := PBsr) (toV := PBsr.toValue) (enc := pbsrEnc) prysmBsrDesc_wellFormed pbsr_serialize
    pbsr_toValue_surjective' h

/-- **EthLib accepts exactly the 16-byte inputs.** -/
theorem pbsr_spec_accepts_iff (bs : Array UInt8) : (∃ v, deserialize prysmBsrDesc bs = .ok v) ↔ bs.size = 16 := by
  constructor
  · rintro ⟨v, hd⟩
    obtain ⟨g, rfl, hb⟩ := pbsr_accepted_is_enc hd
    rw [hb]; exact pbsr_enc_size g
  · intro h
    have r0 := readUint_lt bs 0 8
    have r1 := readUint_lt bs 8 8
    simp only [Nat.reducePow, Nat.reduceMul] at r0 r1
    let g : PBsr := ⟨UInt64.ofNat (readUint bs 0 8), UInt64.ofNat (readUint bs 8 8)⟩
    have e : bs = pbsrEnc g := by
      simp only [g, pbsrEnc, UInt64.toNat_ofNat_of_lt' r0, UInt64.toNat_ofNat_of_lt' r1, uintBytes_readUint_slice bs 0 8 (by omega), uintBytes_readUint_slice bs 8 8 (by omega)]
      simp only [Nat.zero_add, Nat.reduceAdd]
      simp (config := {decide := true}) only [Array.extract_append_extract, Nat.min_def, Nat.max_def, ↓reduceIte]
      rw [← h]; simp
    rw [e]
    exact ⟨_, pbsr_roundtrip g⟩

/-- `len(buf) ≠ 16`: EthLib rejects. -/
theorem pbsr_spec_rejects (bs : Array UInt8) (h : bs.size ≠ 16) : ∃ e, deserialize prysmBsrDesc bs = .error e := by
  cases hd : deserialize prysmBsrDesc bs with
  | error e => exact ⟨e, rfl⟩
  | ok v => exact absurd ((pbsr_spec_accepts_iff bs).mp ⟨v, hd⟩) h

end E2e
