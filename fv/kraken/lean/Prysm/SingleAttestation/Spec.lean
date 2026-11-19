module

public import Prysm.AttestationData.Spec
public import Prysm.SingleAttestation.SpecDescription

@[expose] public section

/-!
# Spec bridge for the Prysm `v1alpha1.SingleAttestation`

`desc` (`Prysm/SingleAttestation/SpecDescription.lean`) is the independent hand `Desc` from consensus-specs electra.
The Prysm Go fields (`attestation.pb.go` of the pinned Prysm commit, `go_fields` of `v1alpha1.SingleAttestation` in `prysm/ir/ir-mainnet.json`)
are `CommitteeId` (offset 8), `AttesterIndex` (16), `Data` (24, `*AttestationData`) and `Signature` (32, slice header).
`state` (0), `unknownFields` (56) and `sizeCache` (80) have no SSZ value (size 88).

`SszValue` is the SSZ content of a Go `v1alpha1.SingleAttestation` with a non-nil `Data` (as in `Prysm.AttestationData.SszValue`)
and `len(Signature) = 96`.
The proofs follow `Prysm/AttestationData/Spec.lean` and `Prysm/IndexedAttestation/Spec.lean`.
They read EthLib and `Prysm.AttestationData.Spec` only.
-/

namespace Prysm.SingleAttestation
open EthLib.Serialization.Ssz
open Spec hiding readUint_lt

theorem desc_wellFormed : desc.wellFormed = .ok () := by rfl
theorem desc_fixedSize : desc.fixedSize = some 240 := by rfl

/-- The SSZ content of a Go `v1alpha1.SingleAttestation` (non-nil Data, 96-byte Signature). -/
structure SszValue where
  committeeIndex : UInt64
  attesterIndex : UInt64
  data : Prysm.AttestationData.SszValue
  signature : Vector UInt8 96

def SszValue.toValue (g : SszValue) : Value :=
  .seq [.uint g.committeeIndex.toNat, .uint g.attesterIndex.toNat, g.data.toValue, .bytes g.signature.toArray]

/-- `uintBytes 8 committeeIndex ++ uintBytes 8 attesterIndex ++ enc data ++ signature`. -/
def SszValue.encode (g : SszValue) : Array UInt8 :=
  uintBytes 8 g.committeeIndex.toNat ++ uintBytes 8 g.attesterIndex.toNat ++ Prysm.AttestationData.SszValue.encode g.data
    ++ g.signature.toArray

theorem SszValue.encode_size (g : SszValue) : (SszValue.encode g).size = 240 := by
  simp [SszValue.encode, Spec.uintBytes_size, Prysm.AttestationData.SszValue.encode_size]

theorem SszValue.toValue_fits (g : SszValue) : Value.fits desc g.toValue = true := by
  have := g.committeeIndex.toNat_lt; have := g.attesterIndex.toNat_lt
  have h1 := Prysm.AttestationData.SszValue.toValue_fits g.data
  simp only [desc, SszValue.toValue, Value.fits, Value.fieldsFit] at *
  simp [h1]; omega

theorem SszValue.toValue_injective (g h : SszValue) (e : g.toValue = h.toValue) : g = h := by
  obtain ⟨a, b, d, s⟩ := g; obtain ⟨a', b', d', s'⟩ := h
  simp only [SszValue.toValue, Value.seq.injEq, List.cons.injEq, Value.uint.injEq, Value.bytes.injEq,
    and_true] at e
  obtain ⟨e1, e2, e3, e4⟩ := e
  rw [UInt64.toNat_inj.mp e1, UInt64.toNat_inj.mp e2, Prysm.AttestationData.SszValue.toValue_injective d d' e3,
    Vector.toArray_inj.mp e4]

theorem SszValue.toValue_surjective (v : Value) (h : Value.fits desc v = true) :
    ∃ g : SszValue, g.toValue = v := by
  obtain ⟨vs, rfl, hf⟩ := fits_container h
  have hl := fieldsFit_length hf
  match vs, hl with
  | [v1, v2, v3, v4], _ =>
    simp only [fieldsFit_cons] at hf
    obtain ⟨h1, h2, h3, h4, -⟩ := hf
    obtain ⟨a, rfl, ha⟩ := fits_uint h1
    obtain ⟨b, rfl, hb⟩ := fits_uint h2
    obtain ⟨d, rfl⟩ := Prysm.AttestationData.SszValue.toValue_surjective v3 h3
    obtain ⟨z, rfl, hz⟩ : ∃ z, v4 = .bytes z ∧ z.size = 96 := by
      cases v4 <;> simp [Value.fits] at h4 ⊢; exact h4
    simp only [Nat.reduceMul, Nat.reducePow] at ha hb
    exact ⟨⟨UInt64.ofNat a, UInt64.ofNat b, d, ⟨z, hz⟩⟩,
      by simp [SszValue.toValue, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]⟩

/-- **`serialize g = committeeIndex ‖ attesterIndex ‖ data ‖ signature`.** -/
theorem SszValue.serialize_eq (g : SszValue) : serialize desc g.toValue = .ok (SszValue.encode g) := by
  obtain ⟨a, b, d, ⟨z, hz⟩⟩ := g
  have := a.toNat_lt; have := b.toNat_lt
  have hd := Prysm.AttestationData.SszValue.serialize_eq d
  have hds := Prysm.AttestationData.SszValue.encode_size d
  have f4 : Prysm.AttestationData.desc.isFixed = true := rfl
  have f5 : Prysm.AttestationData.desc.fixedSize = some 128 := rfl
  simp only [desc, SszValue.toValue, serialize, serializeStruct, serializeFields, hz]
  rw [hd]
  simp (config := {decide := true}) [*, bind, Except.bind, pure, Except.pure, assemble, headWidth, bodyWidth,
    headOf, bodiesOf, Desc.isFixed, Desc.fixedSize, Spec.uintBytes_size, bytesPerOffset, SszValue.encode,
    Array.append_assoc]

/-- **Spec roundtrip.** -/
theorem SszValue.roundtrip (g : SszValue) : deserialize desc (SszValue.encode g) = .ok g.toValue :=
  deserialize_encoding (G := SszValue) (toV := SszValue.toValue) (enc := SszValue.encode) desc_wellFormed SszValue.serialize_eq
    SszValue.toValue_fits g

theorem SszValue.accepted_is_encoding {bs : Array UInt8} {v : Value} (h : deserialize desc bs = .ok v) :
    ∃ g : SszValue, v = g.toValue ∧ bs = SszValue.encode g :=
  accepted_input_is_encoding (G := SszValue) (toV := SszValue.toValue) (enc := SszValue.encode) desc_wellFormed SszValue.serialize_eq
    SszValue.toValue_surjective h

/-- **EthLib accepts exactly the 240-byte inputs.** -/
theorem SszValue.spec_accepts_iff (bs : Array UInt8) : (∃ v, deserialize desc bs = .ok v) ↔ bs.size = 240 := by
  constructor
  · rintro ⟨v, hd⟩
    obtain ⟨g, rfl, rfl⟩ := SszValue.accepted_is_encoding hd
    exact SszValue.encode_size g
  · intro h
    have r0 := readUint_lt bs 0 8; have r1 := readUint_lt bs 8 8
    simp only [Nat.reducePow, Nat.reduceMul] at r0 r1
    obtain ⟨vd, hvd⟩ := (Prysm.AttestationData.SszValue.spec_accepts_iff (bs.extract 16 144)).mpr (by simp; omega)
    obtain ⟨d, -, hd⟩ := Prysm.AttestationData.SszValue.accepted_is_encoding hvd
    let g : SszValue := ⟨UInt64.ofNat (readUint bs 0 8), UInt64.ofNat (readUint bs 8 8), d,
      ⟨bs.extract 144 240, by simp; omega⟩⟩
    have e : bs = SszValue.encode g := by
      simp only [g, SszValue.encode, UInt64.toNat_ofNat_of_lt' r0, UInt64.toNat_ofNat_of_lt' r1, ← hd,
        uintBytes_readUint_slice bs 0 8 (by omega), uintBytes_readUint_slice bs 8 8 (by omega)]
      simp only [Nat.zero_add, Nat.reduceAdd]
      simp (config := {decide := true}) only [Array.extract_append_extract, Nat.min_def, Nat.max_def, ↓reduceIte]
      rw [← h]; simp
    rw [e]
    exact ⟨_, SszValue.roundtrip g⟩

/-- `len(buf) ≠ 240`: EthLib rejects. -/
theorem SszValue.spec_rejects (bs : Array UInt8) (h : bs.size ≠ 240) : ∃ e, deserialize desc bs = .error e := by
  cases hd : deserialize desc bs with
  | error e => exact ⟨e, rfl⟩
  | ok v => exact absurd ((SszValue.spec_accepts_iff bs).mp ⟨v, hd⟩) h

end Prysm.SingleAttestation
