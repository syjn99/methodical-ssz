import Prysm.Checkpoint.Spec
import Prysm.Checkpoint.SpecEquivalence
import Prysm.DepositRequest.SpecDescription
import Prysm.DepositRequest.SpecChecker

/-!
# Spec bridge for the real Prysm `v1.DepositRequest` (24 flat hold-out types)

Written by the evidence script `flat_types_spec.py` (the text of `Prysm/SyncCommitteeMessage/Spec.lean` / `Prysm/SyncAggregatorSelectionData/Spec.lean`
generalised to a field list). `desc` (`Prysm/DepositRequest/SpecDescription.lean`) is the independent hand `Desc` (Prysm proto).
`checkerDesc` (`Prysm/DepositRequest/SpecChecker.lean`, rendered by `gen/checks/desc_to_lean.py`) is the Desc checker's Desc of the type
(the producer output recorded in `gen/desc/results/main.result.json`, same sha256; copy in `prysm/go1.26.10/evidence/flat-types/`).
`SszValue` is the SSZ content of a Go `v1.DepositRequest`.
-/

namespace Prysm.DepositRequest
open EthLib.Serialization.Ssz
open Spec hiding readUint_lt

theorem desc_kinds : desc = .container ["pubkey", "withdrawal_credentials", "amount", "signature", "index"]
      [.byteVector 48, .byteVector 32, .uint 8, .byteVector 96, .uint 8] := rfl

theorem desc_wellFormed : desc.wellFormed = .ok () := by rfl
theorem desc_fixedSize : desc.fixedSize = some 192 := by rfl

/-- EthLib's `serialize` ignores container names. -/
theorem desc_serialize_checker (v : Value) : serialize desc v = serialize checkerDesc v := by
  unfold desc checkerDesc
  cases v <;> (try simp only [serialize, serializeStruct]) <;> rfl

/-- The SSZ content of a Go `v1.DepositRequest`. -/
structure SszValue where
  pubkey : Vector UInt8 48
  withdrawalCredentials : Vector UInt8 32
  amount : UInt64
  signature : Vector UInt8 96
  index : UInt64

def SszValue.toValue (g : SszValue) : Value :=
  .seq [.bytes g.pubkey.toArray, .bytes g.withdrawalCredentials.toArray, .uint g.amount.toNat, .bytes g.signature.toArray, .uint g.index.toNat]

def SszValue.encode (g : SszValue) : Array UInt8 :=
  g.pubkey.toArray ++ g.withdrawalCredentials.toArray ++ uintBytes 8 g.amount.toNat ++ g.signature.toArray ++ uintBytes 8 g.index.toNat

theorem SszValue.encode_size (g : SszValue) : (SszValue.encode g).size = 192 := by
  simp [SszValue.encode, Spec.uintBytes_size]

theorem SszValue.toValue_fits (g : SszValue) : Value.fits desc g.toValue = true := by
  have := g.amount.toNat_lt; have := g.index.toNat_lt
  simp only [desc, SszValue.toValue, Value.fits, Value.fieldsFit] at *
  simp; omega

theorem SszValue.toValue_injective (g h : SszValue) (e : g.toValue = h.toValue) : g = h := by
  obtain ⟨a0, a1, a2, a3, a4⟩ := g; obtain ⟨b0, b1, b2, b3, b4⟩ := h
  simp only [SszValue.toValue, Value.seq.injEq, List.cons.injEq, Value.uint.injEq, Value.bytes.injEq,
    and_true] at e
  obtain ⟨e0, e1, e2, e3, e4⟩ := e
  rw [Vector.toArray_inj.mp e0, Vector.toArray_inj.mp e1, UInt64.toNat_inj.mp e2, Vector.toArray_inj.mp e3, UInt64.toNat_inj.mp e4]

theorem SszValue.toValue_surjective' (v : Value) (h : Value.fits desc v = true) : ∃ g : SszValue, g.toValue = v := by
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
      by simp [SszValue.toValue, Nat.mod_eq_of_lt ha2, Nat.mod_eq_of_lt ha4]⟩

theorem SszValue.serialize_eq (g : SszValue) : serialize desc g.toValue = .ok (SszValue.encode g) := by
  obtain ⟨⟨r0, hr0⟩, ⟨r1, hr1⟩, a2, ⟨r3, hr3⟩, a4⟩ := g
  have := a2.toNat_lt; have := a4.toNat_lt
  simp only [desc, SszValue.toValue, serialize, serializeStruct, serializeFields, Vector.toArray_mk, hr0, hr1, hr3]
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

/-- **EthLib accepts exactly the 192-byte inputs.** -/
theorem SszValue.spec_accepts_iff (bs : Array UInt8) : (∃ v, deserialize desc bs = .ok v) ↔ bs.size = 192 := by
  constructor
  · rintro ⟨v, hd⟩
    obtain ⟨g, rfl, hb⟩ := SszValue.accepted_is_encoding hd
    rw [hb]; exact SszValue.encode_size g
  · intro h
    have r2 := readUint_lt bs 80 8
    have r4 := readUint_lt bs 184 8
    simp only [Nat.reducePow, Nat.reduceMul] at r2 r4
    let g : SszValue := ⟨⟨bs.extract 0 48, by simp; omega⟩, ⟨bs.extract 48 80, by simp; omega⟩, UInt64.ofNat (readUint bs 80 8), ⟨bs.extract 88 184, by simp; omega⟩, UInt64.ofNat (readUint bs 184 8)⟩
    have e : bs = SszValue.encode g := by
      simp only [g, SszValue.encode, UInt64.toNat_ofNat_of_lt' r2, UInt64.toNat_ofNat_of_lt' r4, uintBytes_readUint_slice bs 80 8 (by omega), uintBytes_readUint_slice bs 184 8 (by omega)]
      simp only [Nat.zero_add, Nat.reduceAdd]
      simp (config := {decide := true}) only [Array.extract_append_extract, Nat.min_def, Nat.max_def, ↓reduceIte]
      rw [← h]; simp
    rw [e]
    exact ⟨_, SszValue.roundtrip g⟩

/-- `len(buf) ≠ 192`: EthLib rejects. -/
theorem SszValue.spec_rejects (bs : Array UInt8) (h : bs.size ≠ 192) : ∃ e, deserialize desc bs = .error e := by
  cases hd : deserialize desc bs with
  | error e => exact ⟨e, rfl⟩
  | ok v => exact absurd ((SszValue.spec_accepts_iff bs).mp ⟨v, hd⟩) h

/-! ### The checker Desc decodes like the hand Desc (accepted inputs and values) -/

theorem checker_wellFormed : checkerDesc.wellFormed = .ok () := by rfl

theorem SszValue.serialize_eq_checker (g : SszValue) : serialize checkerDesc g.toValue = .ok (SszValue.encode g) := by
  rw [← desc_serialize_checker]; exact SszValue.serialize_eq g

theorem SszValue.toValue_fits_checker (g : SszValue) : Value.fits checkerDesc g.toValue = true := by
  have := g.amount.toNat_lt; have := g.index.toNat_lt
  simp [checkerDesc, SszValue.toValue, Value.fits, Value.fieldsFit]; omega

theorem SszValue.toValue_surjective_checker (v : Value) (h : Value.fits checkerDesc v = true) :
    ∃ g : SszValue, g.toValue = v := by
  have h' : Value.fits desc v = true := by
    cases v <;> simp_all [desc, checkerDesc, Value.fits]
  exact SszValue.toValue_surjective' v h'

/-- **Codec equality on the accepted inputs**. -/
theorem desc_deserialize_checker (bs : Array UInt8) (v : Value) :
    deserialize desc bs = .ok v ↔ deserialize checkerDesc bs = .ok v := by
  constructor
  · intro h
    obtain ⟨g, rfl, hb⟩ := SszValue.accepted_is_encoding h
    rw [hb]
    exact deserialize_encoding (G := SszValue) (toV := SszValue.toValue) (enc := SszValue.encode) checker_wellFormed
      SszValue.serialize_eq_checker SszValue.toValue_fits_checker g
  · intro h
    obtain ⟨g, rfl, hb⟩ := accepted_input_is_encoding (G := SszValue) (toV := SszValue.toValue) (enc := SszValue.encode)
      checker_wellFormed SszValue.serialize_eq_checker SszValue.toValue_surjective_checker h
    rw [hb]; exact SszValue.roundtrip g

end Prysm.DepositRequest
