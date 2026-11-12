import Prysm.Checkpoint.Spec
import Prysm.Checkpoint.SpecEquivalence
import E2eScal.F24Desc

/-!
# Spec bridge for the real Prysm `v1alpha1.BuilderPreferences` (FLAT24 / H7)

Written by the FLAT24 evaluator with its evidence script `f24spec.py` (the text of `SmSpec.lean` / `SaSpec.lean`
generalised to a field list). `prysmBpfDesc` (`F24Desc.lean`) is the independent hand `Desc` (Prysm proto).
No Desc-checker record exists for this type (`gen/desc/results/main.result.json`): no codec equality here.
`PBpf` is the SSZ content of a Go `v1alpha1.BuilderPreferences`.
-/

namespace E2e
open EthLib.Serialization.Ssz
open Spec hiding readUint_lt

theorem prysmBpfDesc_kinds : prysmBpfDesc = .container ["max_execution_payment"]
      [.uint 8] := rfl

theorem prysmBpfDesc_wellFormed : prysmBpfDesc.wellFormed = .ok () := by rfl
theorem prysmBpfDesc_fixedSize : prysmBpfDesc.fixedSize = some 8 := by rfl

/-- The SSZ content of a Go `v1alpha1.BuilderPreferences`. -/
structure PBpf where
  maxExecutionPayment : UInt64

def PBpf.toValue (g : PBpf) : Value :=
  .seq [.uint g.maxExecutionPayment.toNat]

def pbpfEnc (g : PBpf) : Array UInt8 :=
  uintBytes 8 g.maxExecutionPayment.toNat

theorem pbpf_enc_size (g : PBpf) : (pbpfEnc g).size = 8 := by
  simp [pbpfEnc, Spec.uintBytes_size]

theorem pbpf_toValue_fits (g : PBpf) : Value.fits prysmBpfDesc g.toValue = true := by
  have := g.maxExecutionPayment.toNat_lt
  simp only [prysmBpfDesc, PBpf.toValue, Value.fits, Value.fieldsFit] at *
  simp; omega

theorem pbpf_toValue_injective (g h : PBpf) (e : g.toValue = h.toValue) : g = h := by
  obtain ⟨a0⟩ := g; obtain ⟨b0⟩ := h
  simp only [PBpf.toValue, Value.seq.injEq, List.cons.injEq, Value.uint.injEq, Value.bytes.injEq,
    and_true] at e
  rw [UInt64.toNat_inj.mp e]

theorem pbpf_toValue_surjective' (v : Value) (h : Value.fits prysmBpfDesc v = true) : ∃ g : PBpf, g.toValue = v := by
  obtain ⟨vs, rfl, hf⟩ := fits_container h
  have hl := fieldsFit_length hf
  match vs, hl with
  | [v0], _ =>
    simp only [fieldsFit_cons] at hf
    obtain ⟨h0, -⟩ := hf
    obtain ⟨a0, rfl, ha0⟩ := fits_uint h0
    simp only [Nat.reduceMul, Nat.reducePow] at ha0
    exact ⟨⟨UInt64.ofNat a0⟩,
      by simp [PBpf.toValue, Nat.mod_eq_of_lt ha0]⟩

theorem pbpf_serialize (g : PBpf) : serialize prysmBpfDesc g.toValue = .ok (pbpfEnc g) := by
  obtain ⟨a0⟩ := g
  have := a0.toNat_lt
  simp only [prysmBpfDesc, PBpf.toValue, serialize, serializeStruct, serializeFields, Vector.toArray_mk]
  simp (config := {decide := true}) [*, bind, Except.bind, pure, Except.pure, assemble, headWidth, bodyWidth,
    headOf, bodiesOf, Desc.isFixed, Desc.fixedSize, Spec.uintBytes_size, bytesPerOffset, pbpfEnc,
    Desc.fieldsFixedSize, Array.append_assoc]

/-- **Spec roundtrip.** -/
theorem pbpf_roundtrip (g : PBpf) : deserialize prysmBpfDesc (pbpfEnc g) = .ok g.toValue :=
  deserialize_enc (G := PBpf) (toV := PBpf.toValue) (enc := pbpfEnc) prysmBpfDesc_wellFormed pbpf_serialize
    pbpf_toValue_fits g

theorem pbpf_accepted_is_enc {bs : Array UInt8} {v : Value} (h : deserialize prysmBpfDesc bs = .ok v) :
    ∃ g : PBpf, v = g.toValue ∧ bs = pbpfEnc g :=
  accepted_is_enc (G := PBpf) (toV := PBpf.toValue) (enc := pbpfEnc) prysmBpfDesc_wellFormed pbpf_serialize
    pbpf_toValue_surjective' h

/-- **EthLib accepts exactly the 8-byte inputs.** -/
theorem pbpf_spec_accepts_iff (bs : Array UInt8) : (∃ v, deserialize prysmBpfDesc bs = .ok v) ↔ bs.size = 8 := by
  constructor
  · rintro ⟨v, hd⟩
    obtain ⟨g, rfl, hb⟩ := pbpf_accepted_is_enc hd
    rw [hb]; exact pbpf_enc_size g
  · intro h
    have r0 := readUint_lt bs 0 8
    simp only [Nat.reducePow, Nat.reduceMul] at r0
    let g : PBpf := ⟨UInt64.ofNat (readUint bs 0 8)⟩
    have e : bs = pbpfEnc g := by
      simp only [g, pbpfEnc, UInt64.toNat_ofNat_of_lt' r0, uintBytes_readUint_slice bs 0 8 (by omega)]
      try simp only [Nat.zero_add, Nat.reduceAdd]
      try simp (config := {decide := true}) only [Array.extract_append_extract, Nat.min_def, Nat.max_def, ↓reduceIte]
      rw [← h]; simp
    rw [e]
    exact ⟨_, pbpf_roundtrip g⟩

/-- `len(buf) ≠ 8`: EthLib rejects. -/
theorem pbpf_spec_rejects (bs : Array UInt8) (h : bs.size ≠ 8) : ∃ e, deserialize prysmBpfDesc bs = .error e := by
  cases hd : deserialize prysmBpfDesc bs with
  | error e => exact ⟨e, rfl⟩
  | ok v => exact absurd ((pbpf_spec_accepts_iff bs).mp ⟨v, hd⟩) h

end E2e
