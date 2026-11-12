import E2e.Spec
import E2e.SpecEq
import E2eScal.F24Desc
import E2eScal.F24DprSpecChecker

/-!
# Spec bridge for the real Prysm `v1.DepositRequest` (FLAT24 / H7)

Written by the FLAT24 evaluator with its evidence script `f24spec.py` (the text of `SmSpec.lean` / `SaSpec.lean`
generalised to a field list). `prysmDprDesc` (`F24Desc.lean`) is the independent hand `Desc` (Prysm proto).
`dprCheckerDesc` (`F24DprSpecChecker.lean`, rendered by `gen/e2e/descterm.py`) is the Desc checker's Desc of the type
(the producer output recorded in `gen/desc/results/main.result.json`, same sha256; copy in `prysm/go1.26.10/e2e/f24/`).
`PDpr` is the SSZ content of a Go `v1.DepositRequest`.
-/

namespace E2e
open EthLib.Serialization.Ssz
open Spec hiding readUint_lt

theorem prysmDprDesc_kinds : prysmDprDesc = .container ["pubkey", "withdrawal_credentials", "amount", "signature", "index"]
      [.byteVector 48, .byteVector 32, .uint 8, .byteVector 96, .uint 8] := rfl

theorem prysmDprDesc_wellFormed : prysmDprDesc.wellFormed = .ok () := by rfl
theorem prysmDprDesc_fixedSize : prysmDprDesc.fixedSize = some 192 := by rfl

/-- EthLib's `serialize` ignores container names. -/
theorem prysmDprDesc_serialize_checker (v : Value) : serialize prysmDprDesc v = serialize dprCheckerDesc v := by
  unfold prysmDprDesc dprCheckerDesc
  cases v <;> (try simp only [serialize, serializeStruct]) <;> rfl

/-- The SSZ content of a Go `v1.DepositRequest`. -/
structure PDpr where
  pubkey : Vector UInt8 48
  withdrawalCredentials : Vector UInt8 32
  amount : UInt64
  signature : Vector UInt8 96
  index : UInt64

def PDpr.toValue (g : PDpr) : Value :=
  .seq [.bytes g.pubkey.toArray, .bytes g.withdrawalCredentials.toArray, .uint g.amount.toNat, .bytes g.signature.toArray, .uint g.index.toNat]

def pdprEnc (g : PDpr) : Array UInt8 :=
  g.pubkey.toArray ++ g.withdrawalCredentials.toArray ++ uintBytes 8 g.amount.toNat ++ g.signature.toArray ++ uintBytes 8 g.index.toNat

theorem pdpr_enc_size (g : PDpr) : (pdprEnc g).size = 192 := by
  simp [pdprEnc, Spec.uintBytes_size]

theorem pdpr_toValue_fits (g : PDpr) : Value.fits prysmDprDesc g.toValue = true := by
  have := g.amount.toNat_lt; have := g.index.toNat_lt
  simp only [prysmDprDesc, PDpr.toValue, Value.fits, Value.fieldsFit] at *
  simp; omega

theorem pdpr_toValue_injective (g h : PDpr) (e : g.toValue = h.toValue) : g = h := by
  obtain ⟨a0, a1, a2, a3, a4⟩ := g; obtain ⟨b0, b1, b2, b3, b4⟩ := h
  simp only [PDpr.toValue, Value.seq.injEq, List.cons.injEq, Value.uint.injEq, Value.bytes.injEq,
    and_true] at e
  obtain ⟨e0, e1, e2, e3, e4⟩ := e
  rw [Vector.toArray_inj.mp e0, Vector.toArray_inj.mp e1, UInt64.toNat_inj.mp e2, Vector.toArray_inj.mp e3, UInt64.toNat_inj.mp e4]

theorem pdpr_toValue_surjective' (v : Value) (h : Value.fits prysmDprDesc v = true) : ∃ g : PDpr, g.toValue = v := by
  obtain ⟨vs, rfl, hf⟩ := fits_container h
  have hl := fieldsFit_length hf
  match vs, hl with
  | [v0, v1, v2, v3, v4], _ =>
    simp only [fieldsFit_cons] at hf
    obtain ⟨h0, h1, h2, h3, h4, -⟩ := hf
    obtain ⟨a0, rfl, ha0⟩ : ∃ d, v0 = .bytes d ∧ d.size = 48 := by
      cases v0 <;> simp [Value.fits] at h0 ⊢; exact h0
    obtain ⟨a1, rfl, ha1⟩ : ∃ d, v1 = .bytes d ∧ d.size = 32 := by
      cases v1 <;> simp [Value.fits] at h1 ⊢; exact h1
    obtain ⟨a2, rfl, ha2⟩ := fits_uint h2
    obtain ⟨a3, rfl, ha3⟩ : ∃ d, v3 = .bytes d ∧ d.size = 96 := by
      cases v3 <;> simp [Value.fits] at h3 ⊢; exact h3
    obtain ⟨a4, rfl, ha4⟩ := fits_uint h4
    simp only [Nat.reduceMul, Nat.reducePow] at ha2 ha4
    exact ⟨⟨⟨a0, ha0⟩, ⟨a1, ha1⟩, UInt64.ofNat a2, ⟨a3, ha3⟩, UInt64.ofNat a4⟩,
      by simp [PDpr.toValue, Nat.mod_eq_of_lt ha2, Nat.mod_eq_of_lt ha4]⟩

theorem pdpr_serialize (g : PDpr) : serialize prysmDprDesc g.toValue = .ok (pdprEnc g) := by
  obtain ⟨⟨r0, hr0⟩, ⟨r1, hr1⟩, a2, ⟨r3, hr3⟩, a4⟩ := g
  have := a2.toNat_lt; have := a4.toNat_lt
  simp only [prysmDprDesc, PDpr.toValue, serialize, serializeStruct, serializeFields, Vector.toArray_mk, hr0, hr1, hr3]
  simp (config := {decide := true}) [*, bind, Except.bind, pure, Except.pure, assemble, headWidth, bodyWidth,
    headOf, bodiesOf, Desc.isFixed, Desc.fixedSize, Spec.uintBytes_size, bytesPerOffset, pdprEnc,
    Desc.fieldsFixedSize, Array.append_assoc]

/-- **Spec roundtrip.** -/
theorem pdpr_roundtrip (g : PDpr) : deserialize prysmDprDesc (pdprEnc g) = .ok g.toValue :=
  deserialize_enc (G := PDpr) (toV := PDpr.toValue) (enc := pdprEnc) prysmDprDesc_wellFormed pdpr_serialize
    pdpr_toValue_fits g

theorem pdpr_accepted_is_enc {bs : Array UInt8} {v : Value} (h : deserialize prysmDprDesc bs = .ok v) :
    ∃ g : PDpr, v = g.toValue ∧ bs = pdprEnc g :=
  accepted_is_enc (G := PDpr) (toV := PDpr.toValue) (enc := pdprEnc) prysmDprDesc_wellFormed pdpr_serialize
    pdpr_toValue_surjective' h

/-- **EthLib accepts exactly the 192-byte inputs.** -/
theorem pdpr_spec_accepts_iff (bs : Array UInt8) : (∃ v, deserialize prysmDprDesc bs = .ok v) ↔ bs.size = 192 := by
  constructor
  · rintro ⟨v, hd⟩
    obtain ⟨g, rfl, hb⟩ := pdpr_accepted_is_enc hd
    rw [hb]; exact pdpr_enc_size g
  · intro h
    have r2 := readUint_lt bs 80 8
    have r4 := readUint_lt bs 184 8
    simp only [Nat.reducePow, Nat.reduceMul] at r2 r4
    let g : PDpr := ⟨⟨bs.extract 0 48, by simp; omega⟩, ⟨bs.extract 48 80, by simp; omega⟩, UInt64.ofNat (readUint bs 80 8), ⟨bs.extract 88 184, by simp; omega⟩, UInt64.ofNat (readUint bs 184 8)⟩
    have e : bs = pdprEnc g := by
      simp only [g, pdprEnc, UInt64.toNat_ofNat_of_lt' r2, UInt64.toNat_ofNat_of_lt' r4, uintBytes_readUint_slice bs 80 8 (by omega), uintBytes_readUint_slice bs 184 8 (by omega)]
      simp only [Nat.zero_add, Nat.reduceAdd]
      simp (config := {decide := true}) only [Array.extract_append_extract, Nat.min_def, Nat.max_def, ↓reduceIte]
      rw [← h]; simp
    rw [e]
    exact ⟨_, pdpr_roundtrip g⟩

/-- `len(buf) ≠ 192`: EthLib rejects. -/
theorem pdpr_spec_rejects (bs : Array UInt8) (h : bs.size ≠ 192) : ∃ e, deserialize prysmDprDesc bs = .error e := by
  cases hd : deserialize prysmDprDesc bs with
  | error e => exact ⟨e, rfl⟩
  | ok v => exact absurd ((pdpr_spec_accepts_iff bs).mp ⟨v, hd⟩) h

/-! ### The checker Desc decodes like the hand Desc (accepted inputs and values) -/

theorem dprChecker_wellFormed : dprCheckerDesc.wellFormed = .ok () := by rfl

theorem pdpr_serialize_checker (g : PDpr) : serialize dprCheckerDesc g.toValue = .ok (pdprEnc g) := by
  rw [← prysmDprDesc_serialize_checker]; exact pdpr_serialize g

theorem pdpr_toValue_fits_checker (g : PDpr) : Value.fits dprCheckerDesc g.toValue = true := by
  have := g.amount.toNat_lt; have := g.index.toNat_lt
  simp [dprCheckerDesc, PDpr.toValue, Value.fits, Value.fieldsFit]; omega

theorem pdpr_toValue_surjective_checker (v : Value) (h : Value.fits dprCheckerDesc v = true) :
    ∃ g : PDpr, g.toValue = v := by
  have h' : Value.fits prysmDprDesc v = true := by
    cases v <;> simp_all [prysmDprDesc, dprCheckerDesc, Value.fits]
  exact pdpr_toValue_surjective' v h'

/-- **Codec equality on the accepted inputs**. -/
theorem prysmDprDesc_deserialize_checker (bs : Array UInt8) (v : Value) :
    deserialize prysmDprDesc bs = .ok v ↔ deserialize dprCheckerDesc bs = .ok v := by
  constructor
  · intro h
    obtain ⟨g, rfl, hb⟩ := pdpr_accepted_is_enc h
    rw [hb]
    exact deserialize_enc (G := PDpr) (toV := PDpr.toValue) (enc := pdprEnc) dprChecker_wellFormed
      pdpr_serialize_checker pdpr_toValue_fits_checker g
  · intro h
    obtain ⟨g, rfl, hb⟩ := accepted_is_enc (G := PDpr) (toV := PDpr.toValue) (enc := pdprEnc)
      dprChecker_wellFormed pdpr_serialize_checker pdpr_toValue_surjective_checker h
    rw [hb]; exact pdpr_roundtrip g

end E2e
