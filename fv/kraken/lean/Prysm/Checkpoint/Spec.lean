import Spec.TestCheckpointAndAttestationData
import Spec.DeserializeOfSerialize
import EthLib.Serialization.Proofs.Ssz.Codec.CanonicalTable
import Prysm.Checkpoint.SpecChecker

/-!
# Spec bridge for the real Prysm `v1alpha1.Checkpoint`

Independent hand `Desc`, written from consensus-specs phase0 (`specs/phase0/beacon-chain.md`):

    class Checkpoint(Container):
        epoch: Epoch      # Epoch = uint64
        root: Root        # Root = Bytes32

Field order epoch, root; SSZ kinds `uint64` (8-byte little endian) and `Bytes32`
(EthLib `byteVector 32`). The Prysm Go fields (`attestation.pb.go`, Prysm `ab15ff70`) are
`Epoch` at offset 8 and `Root` (`[]byte`, `ssz-size:"32"`) at offset 16, in this order; `state`, `unknownFields`
and `sizeCache` have no SSZ value (Go size 72; gc amd64 layout from `prysm/ir/ir-mainnet.json`). `checkerDesc` (generated) is the Desc
checker's Desc of `(v1alpha1, Checkpoint)`; `desc_checker` shows that the
two differ only in the field names (spec names vs Go names). The theorems of
this namespace use `desc`.

`SszValue` is the SSZ content of a Go `v1alpha1.Checkpoint` in the EthLib domain
(`len(Root) = 32`): the other Go fields (`state`, `unknownFields`, `sizeCache`)
carry no SSZ value. The proofs of the spec lemmas below follow
`Spec/TestCheckpointAndAttestationData.lean` and an earlier Checkpoint spec module that is no longer in the tree (their text, with the names of this
namespace); they read EthLib only.
-/

namespace Prysm.Checkpoint
open EthLib.Serialization.Ssz
open Spec hiding readUint_lt

/-- consensus-specs phase0 `Checkpoint`. -/
def desc : Desc := .container ["epoch", "root"] [.uint 8, .byteVector 32]

/-- The checker's Desc and the hand Desc have the same field list; only the names differ. -/
theorem desc_checker :
    ∃ fs, desc = .container ["epoch", "root"] fs ∧ checkerDesc = .container ["Epoch", "Root"] fs :=
  ⟨_, rfl, rfl⟩

/-- The reduced hand case `Spec.checkpointDesc` is structurally the same term (cited, not used). -/
theorem desc_eq_hand : desc = Spec.checkpointDesc := rfl

theorem desc_wellFormed : desc.wellFormed = .ok () := by rfl
theorem desc_fixedSize : desc.fixedSize = some 40 := by rfl

/-- The SSZ content of a Go `v1alpha1.Checkpoint` with `len(Root) = 32`. -/
structure SszValue where
  epoch : UInt64
  root : Vector UInt8 32

def SszValue.toValue (g : SszValue) : Value := .seq [.uint g.epoch.toNat, .bytes g.root.toArray]

/-- `uintBytes 8 epoch ++ root`. -/
def SszValue.encode (g : SszValue) : Array UInt8 := uintBytes 8 g.epoch.toNat ++ g.root.toArray

theorem SszValue.enc_size (g : SszValue) : (SszValue.encode g).size = 40 := by
  simp [SszValue.encode, Spec.uintBytes_size]

theorem SszValue.toValue_fits (g : SszValue) : Value.fits desc g.toValue = true := by
  have := g.epoch.toNat_lt
  simp [SszValue.toValue, desc, Value.fits, Value.fieldsFit]; omega

theorem SszValue.toValue_surjective (v : Value) (h : Value.fits desc v = true) :
    ∃ g : SszValue, g.toValue = v := by
  obtain ⟨vs, rfl, hf⟩ := fits_container h
  have hl := fieldsFit_length hf
  match vs, hl with
  | [v1, v2], _ =>
    simp only [fieldsFit_cons] at hf
    obtain ⟨h1, h2, -⟩ := hf
    obtain ⟨a, rfl, ha⟩ := fits_uint h1
    obtain ⟨d, rfl, hd⟩ : ∃ d, v2 = .bytes d ∧ d.size = 32 := by
      cases v2 <;> simp [Value.fits] at h2 ⊢; exact h2
    simp only [Nat.reduceMul, Nat.reducePow] at ha
    exact ⟨⟨UInt64.ofNat a, ⟨d, hd⟩⟩, by simp [SszValue.toValue, Nat.mod_eq_of_lt ha]⟩

/-- **`serialize g = uintBytes 8 epoch ++ root`.** -/
theorem SszValue.serialize_eq (g : SszValue) : serialize desc g.toValue = .ok (SszValue.encode g) := by
  obtain ⟨a, ⟨r, hr⟩⟩ := g
  have := a.toNat_lt
  simp only [desc, SszValue.toValue, serialize, serializeStruct, serializeFields, Vector.toArray_mk, hr]
  simp (config := {decide := true}) [*, bind, Except.bind, pure, Except.pure, assemble, headWidth, bodyWidth,
    headOf, bodiesOf, Desc.isFixed, Desc.fixedSize, Spec.uintBytes_size, bytesPerOffset, SszValue.encode]

/-- **Spec roundtrip**: EthLib decodes the encoding of `g` to `g`. -/
theorem SszValue.roundtrip (g : SszValue) : deserialize desc (SszValue.encode g) = .ok g.toValue :=
  deserialize_encoding (G := SszValue) (toV := SszValue.toValue) (enc := SszValue.encode) desc_wellFormed SszValue.serialize_eq
    SszValue.toValue_fits g

/-- Every input that EthLib accepts is the encoding of the value it returns. -/
theorem SszValue.accepted_is_encoding {bs : Array UInt8} {v : Value} (h : deserialize desc bs = .ok v) :
    ∃ g : SszValue, v = g.toValue ∧ bs = SszValue.encode g :=
  accepted_input_is_encoding (G := SszValue) (toV := SszValue.toValue) (enc := SszValue.encode) desc_wellFormed SszValue.serialize_eq
    SszValue.toValue_surjective h

/-- **EthLib accepts exactly the 40-byte inputs.** -/
theorem SszValue.spec_accepts_iff (bs : Array UInt8) : (∃ v, deserialize desc bs = .ok v) ↔ bs.size = 40 := by
  constructor
  · rintro ⟨v, hd⟩
    obtain ⟨g, rfl, rfl⟩ := SszValue.accepted_is_encoding hd
    exact SszValue.enc_size g
  · intro h
    have r8 := readUint_lt bs 0 8
    simp only [Nat.reducePow, Nat.reduceMul] at r8
    let g : SszValue := ⟨UInt64.ofNat (readUint bs 0 8), ⟨bs.extract 8 40, by simp; omega⟩⟩
    have e : bs = SszValue.encode g := by
      simp only [g, SszValue.encode, UInt64.toNat_ofNat_of_lt' r8, uintBytes_readUint_slice bs 0 8 (by omega)]
      rw [Array.extract_append_extract, show min 0 8 = 0 from rfl, show max 8 40 = bs.size by omega]; simp
    rw [e]
    exact ⟨_, SszValue.roundtrip g⟩

/-- `len(buf) ≠ 40`: EthLib rejects. -/
theorem SszValue.spec_rejects (bs : Array UInt8) (h : bs.size ≠ 40) : ∃ e, deserialize desc bs = .error e := by
  cases hd : deserialize desc bs with
  | error e => exact ⟨e, rfl⟩
  | ok v => exact absurd ((SszValue.spec_accepts_iff bs).mp ⟨v, hd⟩) h

end Prysm.Checkpoint
