import E2e.Spec
import E2e.SpecEq
import E2eScal.F24Desc

/-!
# Spec bridge for the real Prysm `v1alpha1.ValidatorIdentity` (FLAT24 / H7)

Written by the FLAT24 evaluator with its evidence script `f24spec.py` (the text of `SmSpec.lean` / `SaSpec.lean`
generalised to a field list). `prysmVidDesc` (`F24Desc.lean`) is the independent hand `Desc` (Prysm proto).
No Desc-checker record exists for this type (`gen/desc/results/main.result.json`): no codec equality here.
`PVid` is the SSZ content of a Go `v1alpha1.ValidatorIdentity`.
-/

namespace E2e
open EthLib.Serialization.Ssz
open Spec hiding readUint_lt

theorem prysmVidDesc_kinds : prysmVidDesc = .container ["index", "pubkey", "activation_epoch"]
      [.uint 8, .byteVector 48, .uint 8] := rfl

theorem prysmVidDesc_wellFormed : prysmVidDesc.wellFormed = .ok () := by rfl
theorem prysmVidDesc_fixedSize : prysmVidDesc.fixedSize = some 64 := by rfl

/-- The SSZ content of a Go `v1alpha1.ValidatorIdentity`. -/
structure PVid where
  index : UInt64
  pubkey : Vector UInt8 48
  activationEpoch : UInt64

def PVid.toValue (g : PVid) : Value :=
  .seq [.uint g.index.toNat, .bytes g.pubkey.toArray, .uint g.activationEpoch.toNat]

def pvidEnc (g : PVid) : Array UInt8 :=
  uintBytes 8 g.index.toNat ++ g.pubkey.toArray ++ uintBytes 8 g.activationEpoch.toNat

theorem pvid_enc_size (g : PVid) : (pvidEnc g).size = 64 := by
  simp [pvidEnc, Spec.uintBytes_size]

theorem pvid_toValue_fits (g : PVid) : Value.fits prysmVidDesc g.toValue = true := by
  have := g.index.toNat_lt; have := g.activationEpoch.toNat_lt
  simp only [prysmVidDesc, PVid.toValue, Value.fits, Value.fieldsFit] at *
  simp; omega

theorem pvid_toValue_injective (g h : PVid) (e : g.toValue = h.toValue) : g = h := by
  obtain ⟨a0, a1, a2⟩ := g; obtain ⟨b0, b1, b2⟩ := h
  simp only [PVid.toValue, Value.seq.injEq, List.cons.injEq, Value.uint.injEq, Value.bytes.injEq,
    and_true] at e
  obtain ⟨e0, e1, e2⟩ := e
  rw [UInt64.toNat_inj.mp e0, Vector.toArray_inj.mp e1, UInt64.toNat_inj.mp e2]

theorem pvid_toValue_surjective' (v : Value) (h : Value.fits prysmVidDesc v = true) : ∃ g : PVid, g.toValue = v := by
  obtain ⟨vs, rfl, hf⟩ := fits_container h
  have hl := fieldsFit_length hf
  match vs, hl with
  | [v0, v1, v2], _ =>
    simp only [fieldsFit_cons] at hf
    obtain ⟨h0, h1, h2, -⟩ := hf
    obtain ⟨a0, rfl, ha0⟩ := fits_uint h0
    obtain ⟨a1, rfl, ha1⟩ : ∃ d, v1 = .bytes d ∧ d.size = 48 := by
      cases v1 <;> simp [Value.fits] at h1 ⊢; exact h1
    obtain ⟨a2, rfl, ha2⟩ := fits_uint h2
    simp only [Nat.reduceMul, Nat.reducePow] at ha0 ha2
    exact ⟨⟨UInt64.ofNat a0, ⟨a1, ha1⟩, UInt64.ofNat a2⟩,
      by simp [PVid.toValue, Nat.mod_eq_of_lt ha0, Nat.mod_eq_of_lt ha2]⟩

theorem pvid_serialize (g : PVid) : serialize prysmVidDesc g.toValue = .ok (pvidEnc g) := by
  obtain ⟨a0, ⟨r1, hr1⟩, a2⟩ := g
  have := a0.toNat_lt; have := a2.toNat_lt
  simp only [prysmVidDesc, PVid.toValue, serialize, serializeStruct, serializeFields, Vector.toArray_mk, hr1]
  simp (config := {decide := true}) [*, bind, Except.bind, pure, Except.pure, assemble, headWidth, bodyWidth,
    headOf, bodiesOf, Desc.isFixed, Desc.fixedSize, Spec.uintBytes_size, bytesPerOffset, pvidEnc,
    Desc.fieldsFixedSize, Array.append_assoc]

/-- **Spec roundtrip.** -/
theorem pvid_roundtrip (g : PVid) : deserialize prysmVidDesc (pvidEnc g) = .ok g.toValue :=
  deserialize_enc (G := PVid) (toV := PVid.toValue) (enc := pvidEnc) prysmVidDesc_wellFormed pvid_serialize
    pvid_toValue_fits g

theorem pvid_accepted_is_enc {bs : Array UInt8} {v : Value} (h : deserialize prysmVidDesc bs = .ok v) :
    ∃ g : PVid, v = g.toValue ∧ bs = pvidEnc g :=
  accepted_is_enc (G := PVid) (toV := PVid.toValue) (enc := pvidEnc) prysmVidDesc_wellFormed pvid_serialize
    pvid_toValue_surjective' h

/-- **EthLib accepts exactly the 64-byte inputs.** -/
theorem pvid_spec_accepts_iff (bs : Array UInt8) : (∃ v, deserialize prysmVidDesc bs = .ok v) ↔ bs.size = 64 := by
  constructor
  · rintro ⟨v, hd⟩
    obtain ⟨g, rfl, hb⟩ := pvid_accepted_is_enc hd
    rw [hb]; exact pvid_enc_size g
  · intro h
    have r0 := readUint_lt bs 0 8
    have r2 := readUint_lt bs 56 8
    simp only [Nat.reducePow, Nat.reduceMul] at r0 r2
    let g : PVid := ⟨UInt64.ofNat (readUint bs 0 8), ⟨bs.extract 8 56, by simp; omega⟩, UInt64.ofNat (readUint bs 56 8)⟩
    have e : bs = pvidEnc g := by
      simp only [g, pvidEnc, UInt64.toNat_ofNat_of_lt' r0, UInt64.toNat_ofNat_of_lt' r2, uintBytes_readUint_slice bs 0 8 (by omega), uintBytes_readUint_slice bs 56 8 (by omega)]
      simp only [Nat.zero_add, Nat.reduceAdd]
      simp (config := {decide := true}) only [Array.extract_append_extract, Nat.min_def, Nat.max_def, ↓reduceIte]
      rw [← h]; simp
    rw [e]
    exact ⟨_, pvid_roundtrip g⟩

/-- `len(buf) ≠ 64`: EthLib rejects. -/
theorem pvid_spec_rejects (bs : Array UInt8) (h : bs.size ≠ 64) : ∃ e, deserialize prysmVidDesc bs = .error e := by
  cases hd : deserialize prysmVidDesc bs with
  | error e => exact ⟨e, rfl⟩
  | ok v => exact absurd ((pvid_spec_accepts_iff bs).mp ⟨v, hd⟩) h

end E2e
