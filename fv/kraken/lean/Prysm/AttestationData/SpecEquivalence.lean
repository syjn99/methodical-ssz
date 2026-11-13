import Prysm.Checkpoint.Spec
import Prysm.Checkpoint.SpecEquivalence
import Prysm.AttestationData.SpecChecker
import Prysm.AttestationData.Spec
import Codec.SerializeFieldsCongruence

/-!
# The hand `Desc` of `v1alpha1.AttestationData` and the Desc checker's `Desc`

`checkerDesc` (generated, `Prysm/AttestationData/SpecChecker.lean`) has the same kinds in the same order as `desc`
(`Prysm/AttestationData/Spec.lean`); only the names differ. `desc_serialize_checker` gives the equality of `serialize`
for every value, and `desc_deserialize_checker` the same accepted inputs with the same values
(EthLib error values are not compared).
-/

namespace Prysm.AttestationData
open EthLib.Serialization.Ssz
open Spec hiding readUint_lt

/-- The checker's Desc has the same kinds in the same order; only the names differ. -/
theorem desc_checker :
    desc = .container ["slot", "index", "beacon_block_root", "source", "target"]
      [.uint 8, .uint 8, .byteVector 32, .container ["epoch", "root"] [.uint 8, .byteVector 32],
        .container ["epoch", "root"] [.uint 8, .byteVector 32]]
    ∧ checkerDesc = .container ["Slot", "CommitteeIndex", "BeaconBlockRoot", "Source", "Target"]
      [.uint 8, .uint 8, .byteVector 32, .container ["Epoch", "Root"] [.uint 8, .byteVector 32],
        .container ["Epoch", "Root"] [.uint 8, .byteVector 32]] :=
  ⟨rfl, rfl⟩

/-- EthLib's `serialize` ignores container names, also nested ones: the hand Desc and the
checker Desc encode every value the same way. -/
theorem desc_serialize_checker (v : Value) : serialize desc v = serialize checkerDesc v := by
  unfold desc checkerDesc
  cases v <;> simp only [serialize]
  rename_i vs
  have hc : ∀ w, serialize Prysm.Checkpoint.desc w = serialize (.container ["Epoch", "Root"] [.uint 8, .byteVector 32]) w :=
    Prysm.Checkpoint.desc_serialize_checker
  simp only [serializeStruct]
  rw [Codec.serializeFields_congr _ [.uint 8, .uint 8, .byteVector 32, .container ["Epoch", "Root"] [.uint 8, .byteVector 32],
      .container ["Epoch", "Root"] [.uint 8, .byteVector 32]] vs
    (.cons (fun _ => rfl) (.cons (fun _ => rfl) (.cons (fun _ => rfl) (.cons hc (.cons hc .nil)))))]
  rfl

/-! ### The checker Desc decodes like the hand Desc (accepted inputs and values)

EthLib's error values are not compared: the statement is that both Descs accept the same
byte arrays with the same value. -/

theorem checker_wellFormed : checkerDesc.wellFormed = .ok () := by rfl

theorem SszValue.serialize_eq_checker (g : SszValue) : serialize checkerDesc g.toValue = .ok (SszValue.encode g) := by
  rw [← desc_serialize_checker]; exact SszValue.serialize_eq g

theorem SszValue.toValue_fits_checker (g : SszValue) : Value.fits checkerDesc g.toValue = true := by
  have := g.slot.toNat_lt; have := g.index.toNat_lt
  have := g.source.epoch.toNat_lt; have := g.target.epoch.toNat_lt
  simp [checkerDesc, SszValue.toValue, Prysm.Checkpoint.SszValue.toValue, Value.fits, Value.fieldsFit]; omega

theorem checkpoint_toValue_surjective_checker (v : Value)
    (h : Value.fits (.container ["Epoch", "Root"] [.uint 8, .byteVector 32]) v = true) :
    ∃ g : Prysm.Checkpoint.SszValue, g.toValue = v := by
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
    exact ⟨⟨UInt64.ofNat a, ⟨d, hd⟩⟩, by simp [Prysm.Checkpoint.SszValue.toValue, Nat.mod_eq_of_lt ha]⟩

theorem SszValue.toValue_surjective_checker (v : Value) (h : Value.fits checkerDesc v = true) :
    ∃ g : SszValue, g.toValue = v := by
  obtain ⟨vs, rfl, hf⟩ := fits_container h
  have hl := fieldsFit_length hf
  match vs, hl with
  | [v1, v2, v3, v4, v5], _ =>
    simp only [fieldsFit_cons] at hf
    obtain ⟨h1, h2, h3, h4, h5, -⟩ := hf
    obtain ⟨a, rfl, ha⟩ := fits_uint h1
    obtain ⟨b, rfl, hb⟩ := fits_uint h2
    obtain ⟨d, rfl, hd⟩ : ∃ d, v3 = .bytes d ∧ d.size = 32 := by
      cases v3 <;> simp [Value.fits] at h3 ⊢; exact h3
    obtain ⟨s, rfl⟩ := checkpoint_toValue_surjective_checker v4 h4
    obtain ⟨t, rfl⟩ := checkpoint_toValue_surjective_checker v5 h5
    simp only [Nat.reduceMul, Nat.reducePow] at ha hb
    exact ⟨⟨UInt64.ofNat a, UInt64.ofNat b, ⟨d, hd⟩, s, t⟩,
      by simp [SszValue.toValue, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]⟩

/-- **Codec equality on the accepted inputs**: the checker Desc accepts `bs` with value `v`
exactly when the hand Desc does. -/
theorem desc_deserialize_checker (bs : Array UInt8) (v : Value) :
    deserialize desc bs = .ok v ↔ deserialize checkerDesc bs = .ok v := by
  constructor
  · intro h
    obtain ⟨g, rfl, rfl⟩ := SszValue.accepted_is_encoding h
    exact deserialize_encoding (G := SszValue) (toV := SszValue.toValue) (enc := SszValue.encode) checker_wellFormed
      SszValue.serialize_eq_checker SszValue.toValue_fits_checker g
  · intro h
    obtain ⟨g, rfl, rfl⟩ := accepted_input_is_encoding (G := SszValue) (toV := SszValue.toValue) (enc := SszValue.encode) checker_wellFormed
      SszValue.serialize_eq_checker SszValue.toValue_surjective_checker h
    exact SszValue.roundtrip g

end Prysm.AttestationData
