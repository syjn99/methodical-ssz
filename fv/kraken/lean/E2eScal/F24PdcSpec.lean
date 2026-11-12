import Prysm.Checkpoint.Spec
import Prysm.Checkpoint.SpecEquivalence
import E2eScal.F24Desc

/-!
# Spec bridge for the real Prysm `v1alpha1.PartialDataColumnGroupID` (FLAT24 / H7)

Written by the FLAT24 evaluator with its evidence script `f24spec.py` (the text of `SmSpec.lean` / `SaSpec.lean`
generalised to a field list). `prysmPdcDesc` (`F24Desc.lean`) is the independent hand `Desc` (Prysm proto).
No Desc-checker record exists for this type (`gen/desc/results/main.result.json`): no codec equality here.
`PPdc` is the SSZ content of a Go `v1alpha1.PartialDataColumnGroupID`.
-/

namespace E2e
open EthLib.Serialization.Ssz
open Spec hiding readUint_lt

theorem prysmPdcDesc_kinds : prysmPdcDesc = .container ["beacon_block_root", "slot"]
      [.byteVector 32, .uint 8] := rfl

theorem prysmPdcDesc_wellFormed : prysmPdcDesc.wellFormed = .ok () := by rfl
theorem prysmPdcDesc_fixedSize : prysmPdcDesc.fixedSize = some 40 := by rfl

/-- The SSZ content of a Go `v1alpha1.PartialDataColumnGroupID`. -/
structure PPdc where
  beaconBlockRoot : Vector UInt8 32
  slot : UInt64

def PPdc.toValue (g : PPdc) : Value :=
  .seq [.bytes g.beaconBlockRoot.toArray, .uint g.slot.toNat]

def ppdcEnc (g : PPdc) : Array UInt8 :=
  g.beaconBlockRoot.toArray ++ uintBytes 8 g.slot.toNat

theorem ppdc_enc_size (g : PPdc) : (ppdcEnc g).size = 40 := by
  simp [ppdcEnc, Spec.uintBytes_size]

theorem ppdc_toValue_fits (g : PPdc) : Value.fits prysmPdcDesc g.toValue = true := by
  have := g.slot.toNat_lt
  simp only [prysmPdcDesc, PPdc.toValue, Value.fits, Value.fieldsFit] at *
  simp; omega

theorem ppdc_toValue_injective (g h : PPdc) (e : g.toValue = h.toValue) : g = h := by
  obtain ⟨a0, a1⟩ := g; obtain ⟨b0, b1⟩ := h
  simp only [PPdc.toValue, Value.seq.injEq, List.cons.injEq, Value.uint.injEq, Value.bytes.injEq,
    and_true] at e
  obtain ⟨e0, e1⟩ := e
  rw [Vector.toArray_inj.mp e0, UInt64.toNat_inj.mp e1]

theorem ppdc_toValue_surjective' (v : Value) (h : Value.fits prysmPdcDesc v = true) : ∃ g : PPdc, g.toValue = v := by
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
      by simp [PPdc.toValue, Nat.mod_eq_of_lt ha1]⟩

theorem ppdc_serialize (g : PPdc) : serialize prysmPdcDesc g.toValue = .ok (ppdcEnc g) := by
  obtain ⟨⟨r0, hr0⟩, a1⟩ := g
  have := a1.toNat_lt
  simp only [prysmPdcDesc, PPdc.toValue, serialize, serializeStruct, serializeFields, Vector.toArray_mk, hr0]
  simp (config := {decide := true}) [*, bind, Except.bind, pure, Except.pure, assemble, headWidth, bodyWidth,
    headOf, bodiesOf, Desc.isFixed, Desc.fixedSize, Spec.uintBytes_size, bytesPerOffset, ppdcEnc,
    Desc.fieldsFixedSize, Array.append_assoc]

/-- **Spec roundtrip.** -/
theorem ppdc_roundtrip (g : PPdc) : deserialize prysmPdcDesc (ppdcEnc g) = .ok g.toValue :=
  deserialize_enc (G := PPdc) (toV := PPdc.toValue) (enc := ppdcEnc) prysmPdcDesc_wellFormed ppdc_serialize
    ppdc_toValue_fits g

theorem ppdc_accepted_is_enc {bs : Array UInt8} {v : Value} (h : deserialize prysmPdcDesc bs = .ok v) :
    ∃ g : PPdc, v = g.toValue ∧ bs = ppdcEnc g :=
  accepted_is_enc (G := PPdc) (toV := PPdc.toValue) (enc := ppdcEnc) prysmPdcDesc_wellFormed ppdc_serialize
    ppdc_toValue_surjective' h

/-- **EthLib accepts exactly the 40-byte inputs.** -/
theorem ppdc_spec_accepts_iff (bs : Array UInt8) : (∃ v, deserialize prysmPdcDesc bs = .ok v) ↔ bs.size = 40 := by
  constructor
  · rintro ⟨v, hd⟩
    obtain ⟨g, rfl, hb⟩ := ppdc_accepted_is_enc hd
    rw [hb]; exact ppdc_enc_size g
  · intro h
    have r1 := readUint_lt bs 32 8
    simp only [Nat.reducePow, Nat.reduceMul] at r1
    let g : PPdc := ⟨⟨bs.extract 0 32, by simp; omega⟩, UInt64.ofNat (readUint bs 32 8)⟩
    have e : bs = ppdcEnc g := by
      simp only [g, ppdcEnc, UInt64.toNat_ofNat_of_lt' r1, uintBytes_readUint_slice bs 32 8 (by omega)]
      simp only [Nat.zero_add, Nat.reduceAdd]
      simp (config := {decide := true}) only [Array.extract_append_extract, Nat.min_def, Nat.max_def, ↓reduceIte]
      rw [← h]; simp
    rw [e]
    exact ⟨_, ppdc_roundtrip g⟩

/-- `len(buf) ≠ 40`: EthLib rejects. -/
theorem ppdc_spec_rejects (bs : Array UInt8) (h : bs.size ≠ 40) : ∃ e, deserialize prysmPdcDesc bs = .error e := by
  cases hd : deserialize prysmPdcDesc bs with
  | error e => exact ⟨e, rfl⟩
  | ok v => exact absurd ((ppdc_spec_accepts_iff bs).mp ⟨v, hd⟩) h

end E2e
