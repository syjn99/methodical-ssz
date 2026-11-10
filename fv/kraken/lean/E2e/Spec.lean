import Fv1.SpecPrysm
import Fv1.Transfer
import EthLib.Serialization.Proofs.Ssz.Codec.CanonicalTable
import E2e.SpecChecker

/-!
# Spec bridge for the real Prysm `v1alpha1.Checkpoint` (prysm-e2e E1.3)

Independent hand `Desc`, written from consensus-specs phase0 (`specs/phase0/beacon-chain.md`):

    class Checkpoint(Container):
        epoch: Epoch      # Epoch = uint64
        root: Root        # Root = Bytes32

Field order epoch, root; SSZ kinds `uint64` (8-byte little endian) and `Bytes32`
(EthLib `byteVector 32`). The evidence table to the Prysm Go fields is in
`prysm/go1.26.10/e2e/SPEC-BRIDGE.md`. `cpCheckerDesc` (generated) is the Desc
checker's Desc of `(v1alpha1, Checkpoint)`; `prysmCpDesc_checker` shows that the
two differ only in the field names (spec names vs Go names). The theorems of
this namespace use `prysmCpDesc`.

`PCp` is the SSZ content of a Go `v1alpha1.Checkpoint` in the EthLib domain
(`len(Root) = 32`): the other Go fields (`state`, `unknownFields`, `sizeCache`)
carry no SSZ value. The proofs of the spec lemmas below follow
`Fv1/SpecPrysm.lean` and `Fk/CpSpec.lean` (their text, with the names of this
namespace); they read EthLib only.
-/

namespace E2e
open EthLib.Serialization.Ssz Fv1

/-- consensus-specs phase0 `Checkpoint`. -/
def prysmCpDesc : Desc := .container ["epoch", "root"] [.uint 8, .byteVector 32]

/-- The checker's Desc and the hand Desc have the same field list; only the names differ. -/
theorem prysmCpDesc_checker :
    ∃ fs, prysmCpDesc = .container ["epoch", "root"] fs ∧ cpCheckerDesc = .container ["Epoch", "Root"] fs :=
  ⟨_, rfl, rfl⟩

/-- The reduced hand case `Fv1.cpDesc` is structurally the same term (cited, not used). -/
theorem prysmCpDesc_eq_hand : prysmCpDesc = Fv1.cpDesc := rfl

theorem prysmCpDesc_wellFormed : prysmCpDesc.wellFormed = .ok () := by rfl
theorem prysmCpDesc_fixedSize : prysmCpDesc.fixedSize = some 40 := by rfl

/-- The SSZ content of a Go `v1alpha1.Checkpoint` with `len(Root) = 32`. -/
structure PCp where
  epoch : UInt64
  root : Vector UInt8 32

def PCp.toValue (g : PCp) : Value := .seq [.uint g.epoch.toNat, .bytes g.root.toArray]

/-- `uintBytes 8 epoch ++ root`. -/
def pcpEnc (g : PCp) : Array UInt8 := uintBytes 8 g.epoch.toNat ++ g.root.toArray

theorem pcp_enc_size (g : PCp) : (pcpEnc g).size = 40 := by
  simp [pcpEnc, Fv.uintBytes_size]

theorem pcp_toValue_fits (g : PCp) : Value.fits prysmCpDesc g.toValue = true := by
  have := g.epoch.toNat_lt
  simp [PCp.toValue, prysmCpDesc, Value.fits, Value.fieldsFit]; omega

theorem pcp_toValue_surjective (v : Value) (h : Value.fits prysmCpDesc v = true) :
    ∃ g : PCp, g.toValue = v := by
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
    exact ⟨⟨UInt64.ofNat a, ⟨d, hd⟩⟩, by simp [PCp.toValue, Nat.mod_eq_of_lt ha]⟩

/-- **`serialize g = uintBytes 8 epoch ++ root`.** -/
theorem pcp_serialize (g : PCp) : serialize prysmCpDesc g.toValue = .ok (pcpEnc g) := by
  obtain ⟨a, ⟨r, hr⟩⟩ := g
  have := a.toNat_lt
  simp only [prysmCpDesc, PCp.toValue, serialize, serializeStruct, serializeFields, Vector.toArray_mk, hr]
  simp (config := {decide := true}) [*, bind, Except.bind, pure, Except.pure, assemble, headWidth, bodyWidth,
    headOf, bodiesOf, Desc.isFixed, Desc.fixedSize, Fv.uintBytes_size, bytesPerOffset, pcpEnc]

theorem pcp_toValue_surjective' (v : Value) (h : Value.fits prysmCpDesc v = true) : ∃ g : PCp, g.toValue = v :=
  pcp_toValue_surjective v h

/-- **Spec roundtrip**: EthLib decodes the encoding of `g` to `g`. -/
theorem pcp_roundtrip (g : PCp) : deserialize prysmCpDesc (pcpEnc g) = .ok g.toValue :=
  deserialize_enc (G := PCp) (toV := PCp.toValue) (enc := pcpEnc) prysmCpDesc_wellFormed pcp_serialize
    pcp_toValue_fits g

/-- Every input that EthLib accepts is the encoding of the value it returns. -/
theorem pcp_accepted_is_enc {bs : Array UInt8} {v : Value} (h : deserialize prysmCpDesc bs = .ok v) :
    ∃ g : PCp, v = g.toValue ∧ bs = pcpEnc g :=
  accepted_is_enc (G := PCp) (toV := PCp.toValue) (enc := pcpEnc) prysmCpDesc_wellFormed pcp_serialize
    pcp_toValue_surjective' h

/-- **EthLib accepts exactly the 40-byte inputs.** -/
theorem pcp_spec_accepts_iff (bs : Array UInt8) : (∃ v, deserialize prysmCpDesc bs = .ok v) ↔ bs.size = 40 := by
  constructor
  · rintro ⟨v, hd⟩
    obtain ⟨g, rfl, rfl⟩ := pcp_accepted_is_enc hd
    exact pcp_enc_size g
  · intro h
    have r8 := readUint_lt bs 0 8
    simp only [Nat.reducePow, Nat.reduceMul] at r8
    let g : PCp := ⟨UInt64.ofNat (readUint bs 0 8), ⟨bs.extract 8 40, by simp; omega⟩⟩
    have e : bs = pcpEnc g := by
      simp only [g, pcpEnc, UInt64.toNat_ofNat_of_lt' r8, uintBytes_readUint_slice bs 0 8 (by omega)]
      rw [Array.extract_append_extract, show min 0 8 = 0 from rfl, show max 8 40 = bs.size by omega]; simp
    rw [e]
    exact ⟨_, pcp_roundtrip g⟩

/-- `len(buf) ≠ 40`: EthLib rejects. -/
theorem pcp_spec_rejects (bs : Array UInt8) (h : bs.size ≠ 40) : ∃ e, deserialize prysmCpDesc bs = .error e := by
  cases hd : deserialize prysmCpDesc bs with
  | error e => exact ⟨e, rfl⟩
  | ok v => exact absurd ((pcp_spec_accepts_iff bs).mp ⟨v, hd⟩) h

end E2e
