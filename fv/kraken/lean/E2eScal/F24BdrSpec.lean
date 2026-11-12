import Prysm.Checkpoint.Spec
import Prysm.Checkpoint.SpecEquivalence
import E2eScal.F24Desc

/-!
# Spec bridge for the real Prysm `v1.BuilderDepositRequest` (FLAT24 / H7)

Written by the FLAT24 evaluator with its evidence script `f24spec.py` (the text of `SmSpec.lean` / `SaSpec.lean`
generalised to a field list). `prysmBdrDesc` (`F24Desc.lean`) is the independent hand `Desc` (Prysm proto).
No Desc-checker record exists for this type (`gen/desc/results/main.result.json`): no codec equality here.
`PBdr` is the SSZ content of a Go `v1.BuilderDepositRequest`.
-/

namespace E2e
open EthLib.Serialization.Ssz
open Spec hiding readUint_lt

theorem prysmBdrDesc_kinds : prysmBdrDesc = .container ["pubkey", "withdrawal_credentials", "amount", "signature"]
      [.byteVector 48, .byteVector 32, .uint 8, .byteVector 96] := rfl

theorem prysmBdrDesc_wellFormed : prysmBdrDesc.wellFormed = .ok () := by rfl
theorem prysmBdrDesc_fixedSize : prysmBdrDesc.fixedSize = some 184 := by rfl

/-- The SSZ content of a Go `v1.BuilderDepositRequest`. -/
structure PBdr where
  pubkey : Vector UInt8 48
  withdrawalCredentials : Vector UInt8 32
  amount : UInt64
  signature : Vector UInt8 96

def PBdr.toValue (g : PBdr) : Value :=
  .seq [.bytes g.pubkey.toArray, .bytes g.withdrawalCredentials.toArray, .uint g.amount.toNat, .bytes g.signature.toArray]

def pbdrEnc (g : PBdr) : Array UInt8 :=
  g.pubkey.toArray ++ g.withdrawalCredentials.toArray ++ uintBytes 8 g.amount.toNat ++ g.signature.toArray

theorem pbdr_enc_size (g : PBdr) : (pbdrEnc g).size = 184 := by
  simp [pbdrEnc, Spec.uintBytes_size]

theorem pbdr_toValue_fits (g : PBdr) : Value.fits prysmBdrDesc g.toValue = true := by
  have := g.amount.toNat_lt
  simp only [prysmBdrDesc, PBdr.toValue, Value.fits, Value.fieldsFit] at *
  simp; omega

theorem pbdr_toValue_injective (g h : PBdr) (e : g.toValue = h.toValue) : g = h := by
  obtain ⟨a0, a1, a2, a3⟩ := g; obtain ⟨b0, b1, b2, b3⟩ := h
  simp only [PBdr.toValue, Value.seq.injEq, List.cons.injEq, Value.uint.injEq, Value.bytes.injEq,
    and_true] at e
  obtain ⟨e0, e1, e2, e3⟩ := e
  rw [Vector.toArray_inj.mp e0, Vector.toArray_inj.mp e1, UInt64.toNat_inj.mp e2, Vector.toArray_inj.mp e3]

theorem pbdr_toValue_surjective' (v : Value) (h : Value.fits prysmBdrDesc v = true) : ∃ g : PBdr, g.toValue = v := by
  obtain ⟨vs, rfl, hf⟩ := fits_container h
  have hl := fieldsFit_length hf
  match vs, hl with
  | [v0, v1, v2, v3], _ =>
    simp only [fieldsFit_cons] at hf
    obtain ⟨h0, h1, h2, h3, -⟩ := hf
    obtain ⟨a0, rfl, ha0⟩ : ∃ d, v0 = .bytes d ∧ d.size = 48 := by
      cases v0 <;> simp [Value.fits] at h0 ⊢; exact h0
    obtain ⟨a1, rfl, ha1⟩ : ∃ d, v1 = .bytes d ∧ d.size = 32 := by
      cases v1 <;> simp [Value.fits] at h1 ⊢; exact h1
    obtain ⟨a2, rfl, ha2⟩ := fits_uint h2
    obtain ⟨a3, rfl, ha3⟩ : ∃ d, v3 = .bytes d ∧ d.size = 96 := by
      cases v3 <;> simp [Value.fits] at h3 ⊢; exact h3
    simp only [Nat.reduceMul, Nat.reducePow] at ha2
    exact ⟨⟨⟨a0, ha0⟩, ⟨a1, ha1⟩, UInt64.ofNat a2, ⟨a3, ha3⟩⟩,
      by simp [PBdr.toValue, Nat.mod_eq_of_lt ha2]⟩

theorem pbdr_serialize (g : PBdr) : serialize prysmBdrDesc g.toValue = .ok (pbdrEnc g) := by
  obtain ⟨⟨r0, hr0⟩, ⟨r1, hr1⟩, a2, ⟨r3, hr3⟩⟩ := g
  have := a2.toNat_lt
  simp only [prysmBdrDesc, PBdr.toValue, serialize, serializeStruct, serializeFields, Vector.toArray_mk, hr0, hr1, hr3]
  simp (config := {decide := true}) [*, bind, Except.bind, pure, Except.pure, assemble, headWidth, bodyWidth,
    headOf, bodiesOf, Desc.isFixed, Desc.fixedSize, Spec.uintBytes_size, bytesPerOffset, pbdrEnc,
    Desc.fieldsFixedSize, Array.append_assoc]

/-- **Spec roundtrip.** -/
theorem pbdr_roundtrip (g : PBdr) : deserialize prysmBdrDesc (pbdrEnc g) = .ok g.toValue :=
  deserialize_enc (G := PBdr) (toV := PBdr.toValue) (enc := pbdrEnc) prysmBdrDesc_wellFormed pbdr_serialize
    pbdr_toValue_fits g

theorem pbdr_accepted_is_enc {bs : Array UInt8} {v : Value} (h : deserialize prysmBdrDesc bs = .ok v) :
    ∃ g : PBdr, v = g.toValue ∧ bs = pbdrEnc g :=
  accepted_is_enc (G := PBdr) (toV := PBdr.toValue) (enc := pbdrEnc) prysmBdrDesc_wellFormed pbdr_serialize
    pbdr_toValue_surjective' h

/-- **EthLib accepts exactly the 184-byte inputs.** -/
theorem pbdr_spec_accepts_iff (bs : Array UInt8) : (∃ v, deserialize prysmBdrDesc bs = .ok v) ↔ bs.size = 184 := by
  constructor
  · rintro ⟨v, hd⟩
    obtain ⟨g, rfl, hb⟩ := pbdr_accepted_is_enc hd
    rw [hb]; exact pbdr_enc_size g
  · intro h
    have r2 := readUint_lt bs 80 8
    simp only [Nat.reducePow, Nat.reduceMul] at r2
    let g : PBdr := ⟨⟨bs.extract 0 48, by simp; omega⟩, ⟨bs.extract 48 80, by simp; omega⟩, UInt64.ofNat (readUint bs 80 8), ⟨bs.extract 88 184, by simp; omega⟩⟩
    have e : bs = pbdrEnc g := by
      simp only [g, pbdrEnc, UInt64.toNat_ofNat_of_lt' r2, uintBytes_readUint_slice bs 80 8 (by omega)]
      simp only [Nat.zero_add, Nat.reduceAdd]
      simp (config := {decide := true}) only [Array.extract_append_extract, Nat.min_def, Nat.max_def, ↓reduceIte]
      rw [← h]; simp
    rw [e]
    exact ⟨_, pbdr_roundtrip g⟩

/-- `len(buf) ≠ 184`: EthLib rejects. -/
theorem pbdr_spec_rejects (bs : Array UInt8) (h : bs.size ≠ 184) : ∃ e, deserialize prysmBdrDesc bs = .error e := by
  cases hd : deserialize prysmBdrDesc bs with
  | error e => exact ⟨e, rfl⟩
  | ok v => exact absurd ((pbdr_spec_accepts_iff bs).mp ⟨v, hd⟩) h

end E2e
