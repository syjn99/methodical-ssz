import Prysm.Checkpoint.Spec
import Prysm.Checkpoint.SpecEquivalence
import Prysm.AttestationData.SpecChecker

/-!
# Spec bridge for the real Prysm `v1alpha1.AttestationData`

Independent hand `Desc`, written from consensus-specs phase0 (`specs/phase0/beacon-chain.md`):

    class AttestationData(Container):
        slot: Slot                # uint64
        index: CommitteeIndex     # uint64
        beacon_block_root: Root   # Bytes32
        source: Checkpoint
        target: Checkpoint

with `Checkpoint` = `Prysm.Checkpoint.desc` (consensus-specs `Checkpoint(epoch: Epoch, root: Root)`).
The Prysm Go fields (`attestation.pb.go`, Prysm `ab15ff70`) are `Slot` (offset 8), `CommitteeIndex` (16),
`BeaconBlockRoot` (24, slice header), `Source` (48) and `Target` (56), both `*Checkpoint`; `state` (0), `unknownFields` (64)
and `sizeCache` (88) have no SSZ value (size 96; offsets from `prysm/ir/ir-mainnet.json`).
`checkerDesc` (generated) is the Desc checker's Desc of `(v1alpha1, AttestationData)`;
`desc_checker` shows the same kinds in the same order (only the names differ) and
`desc_serialize_checker` the equality of `serialize` (every value) and `desc_deserialize_checker`
the same accepted inputs with the same values (EthLib error values are not compared).

`SszValue` is the SSZ content of a Go `v1alpha1.AttestationData` with `len(BeaconBlockRoot) = 32`
and non-nil `Source`/`Target` whose `Root`s have length 32. The proofs of the spec lemmas follow
`Spec/ReducedPrysm.lean` (its text, with the names of this namespace); they
read EthLib and `Prysm.Checkpoint.Spec` only.
-/

namespace Prysm.AttestationData
open EthLib.Serialization.Ssz
open Spec hiding encode readUint_lt

/-- consensus-specs phase0 `AttestationData`. -/
def desc : Desc := .container ["slot", "index", "beacon_block_root", "source", "target"]
  [.uint 8, .uint 8, .byteVector 32, Prysm.Checkpoint.desc, Prysm.Checkpoint.desc]

/-- The checker's Desc has the same kinds in the same order; only the names differ. -/
theorem desc_checker :
    desc = .container ["slot", "index", "beacon_block_root", "source", "target"]
      [.uint 8, .uint 8, .byteVector 32, .container ["epoch", "root"] [.uint 8, .byteVector 32],
        .container ["epoch", "root"] [.uint 8, .byteVector 32]]
    ∧ checkerDesc = .container ["Slot", "CommitteeIndex", "BeaconBlockRoot", "Source", "Target"]
      [.uint 8, .uint 8, .byteVector 32, .container ["Epoch", "Root"] [.uint 8, .byteVector 32],
        .container ["Epoch", "Root"] [.uint 8, .byteVector 32]] :=
  ⟨rfl, rfl⟩

/-- The reduced hand case `Spec.adDesc` is the same term (cited, not used). -/
theorem desc_eq_hand : desc = Spec.adDesc := rfl

theorem desc_wellFormed : desc.wellFormed = .ok () := by rfl
theorem desc_fixedSize : desc.fixedSize = some 128 := by rfl

/-- Two field lists whose fields encode every value the same way. -/
inductive SameEnc : List Desc → List Desc → Prop
  | nil : SameEnc [] []
  | cons {a b : Desc} {as bs : List Desc} : (∀ v, serialize a v = serialize b v) → SameEnc as bs →
      SameEnc (a :: as) (b :: bs)

/-- `serializeFields` only reads `serialize` of each field: field lists with the same encoders agree. -/
theorem serializeFields_congr : ∀ (fs gs : List Desc) (vs : List Value),
    SameEnc fs gs → serializeFields fs vs = serializeFields gs vs
  | [], [], [], _ => rfl
  | [], [], _ :: _, _ => by simp [serializeFields]
  | _ :: _, _ :: _, [], _ => by simp [serializeFields]
  | f :: fs, g :: gs, v :: vs, .cons h hs => by
    simp only [serializeFields, h v, serializeFields_congr fs gs vs hs]

/-- EthLib's `serialize` ignores container names, also nested ones: the hand Desc and the
checker Desc encode every value the same way. -/
theorem desc_serialize_checker (v : Value) : serialize desc v = serialize checkerDesc v := by
  unfold desc checkerDesc
  cases v <;> simp only [serialize]
  rename_i vs
  have hc : ∀ w, serialize Prysm.Checkpoint.desc w = serialize (.container ["Epoch", "Root"] [.uint 8, .byteVector 32]) w :=
    Prysm.Checkpoint.desc_serialize_checker
  simp only [serializeStruct]
  rw [serializeFields_congr _ [.uint 8, .uint 8, .byteVector 32, .container ["Epoch", "Root"] [.uint 8, .byteVector 32],
      .container ["Epoch", "Root"] [.uint 8, .byteVector 32]] vs
    (.cons (fun _ => rfl) (.cons (fun _ => rfl) (.cons (fun _ => rfl) (.cons hc (.cons hc .nil)))))]
  rfl

/-- The SSZ content of a Go `v1alpha1.AttestationData` (non-nil Source/Target, all Roots of length 32). -/
structure SszValue where
  slot : UInt64
  index : UInt64
  root : Vector UInt8 32
  source : Prysm.Checkpoint.SszValue
  target : Prysm.Checkpoint.SszValue

def SszValue.toValue (g : SszValue) : Value :=
  .seq [.uint g.slot.toNat, .uint g.index.toNat, .bytes g.root.toArray, g.source.toValue, g.target.toValue]

/-- `uintBytes 8 slot ++ uintBytes 8 index ++ root ++ enc source ++ enc target`. -/
def SszValue.encode (g : SszValue) : Array UInt8 :=
  uintBytes 8 g.slot.toNat ++ uintBytes 8 g.index.toNat ++ g.root.toArray ++ Prysm.Checkpoint.SszValue.encode g.source ++ Prysm.Checkpoint.SszValue.encode g.target

theorem SszValue.enc_size (g : SszValue) : (SszValue.encode g).size = 128 := by
  simp [SszValue.encode, Spec.uintBytes_size, Prysm.Checkpoint.SszValue.enc_size]

theorem checkpoint_toValue_injective (g h : Prysm.Checkpoint.SszValue) (e : g.toValue = h.toValue) : g = h := by
  obtain ⟨a, r⟩ := g; obtain ⟨a', r'⟩ := h
  simp only [Prysm.Checkpoint.SszValue.toValue, Value.seq.injEq, List.cons.injEq, Value.uint.injEq, Value.bytes.injEq, and_true] at e
  rw [UInt64.toNat_inj.mp e.1, Vector.toArray_inj.mp e.2]

theorem SszValue.toValue_fits (g : SszValue) : Value.fits desc g.toValue = true := by
  have := g.slot.toNat_lt; have := g.index.toNat_lt
  have h1 := Prysm.Checkpoint.SszValue.toValue_fits g.source; have h2 := Prysm.Checkpoint.SszValue.toValue_fits g.target
  simp only [desc, SszValue.toValue, Value.fits, Value.fieldsFit] at *
  simp [h1, h2]; omega

theorem SszValue.toValue_injective (g h : SszValue) (e : g.toValue = h.toValue) : g = h := by
  obtain ⟨a, b, r, s, t⟩ := g; obtain ⟨a', b', r', s', t'⟩ := h
  simp only [SszValue.toValue, Value.seq.injEq, List.cons.injEq, Value.uint.injEq, Value.bytes.injEq,
    and_true] at e
  obtain ⟨e1, e2, e3, e4, e5⟩ := e
  rw [UInt64.toNat_inj.mp e1, UInt64.toNat_inj.mp e2, Vector.toArray_inj.mp e3, checkpoint_toValue_injective s s' e4,
    checkpoint_toValue_injective t t' e5]

theorem SszValue.toValue_surjective (v : Value) (h : Value.fits desc v = true) :
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
    obtain ⟨s, rfl⟩ := Prysm.Checkpoint.SszValue.toValue_surjective v4 h4
    obtain ⟨t, rfl⟩ := Prysm.Checkpoint.SszValue.toValue_surjective v5 h5
    simp only [Nat.reduceMul, Nat.reducePow] at ha hb
    exact ⟨⟨UInt64.ofNat a, UInt64.ofNat b, ⟨d, hd⟩, s, t⟩,
      by simp [SszValue.toValue, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]⟩

theorem SszValue.toValue_surjective' (v : Value) (h : Value.fits desc v = true) : ∃ g : SszValue, g.toValue = v :=
  SszValue.toValue_surjective v h

/-- **`serialize g = slot ‖ index ‖ root ‖ source ‖ target`.** -/
theorem SszValue.serialize_eq (g : SszValue) : serialize desc g.toValue = .ok (SszValue.encode g) := by
  obtain ⟨a, b, ⟨r, hr⟩, s, t⟩ := g
  have := a.toNat_lt; have := b.toNat_lt
  have hs := Prysm.Checkpoint.SszValue.serialize_eq s; have ht := Prysm.Checkpoint.SszValue.serialize_eq t
  simp only [desc, SszValue.toValue, serialize, serializeStruct, serializeFields, Vector.toArray_mk, hr]
  rw [hs, ht]
  simp (config := {decide := true}) [*, bind, Except.bind, pure, Except.pure, assemble, headWidth, bodyWidth,
    headOf, bodiesOf, Desc.isFixed, Desc.fixedSize, Spec.uintBytes_size, bytesPerOffset, SszValue.encode, Prysm.Checkpoint.desc,
    Prysm.Checkpoint.SszValue.enc_size, Desc.fieldsFixedSize, Array.append_assoc]

/-- **Spec roundtrip.** -/
theorem SszValue.roundtrip (g : SszValue) : deserialize desc (SszValue.encode g) = .ok g.toValue :=
  deserialize_enc (G := SszValue) (toV := SszValue.toValue) (enc := SszValue.encode) desc_wellFormed SszValue.serialize_eq
    SszValue.toValue_fits g

theorem SszValue.accepted_is_encoding {bs : Array UInt8} {v : Value} (h : deserialize desc bs = .ok v) :
    ∃ g : SszValue, v = g.toValue ∧ bs = SszValue.encode g :=
  accepted_is_enc (G := SszValue) (toV := SszValue.toValue) (enc := SszValue.encode) desc_wellFormed SszValue.serialize_eq
    SszValue.toValue_surjective' h

theorem checkpoint_of_bytes (bs : Array UInt8) (o : Nat) (h : o + 40 ≤ bs.size) :
    ∃ c : Prysm.Checkpoint.SszValue, Prysm.Checkpoint.SszValue.encode c = bs.extract o (o + 40) := by
  have r8 := readUint_lt bs o 8
  simp only [Nat.reducePow, Nat.reduceMul] at r8
  refine ⟨⟨UInt64.ofNat (readUint bs o 8), ⟨bs.extract (o + 8) (o + 40), by simp; omega⟩⟩, ?_⟩
  simp only [Prysm.Checkpoint.SszValue.encode, UInt64.toNat_ofNat_of_lt' r8, uintBytes_readUint_slice bs o 8 (by omega)]
  rw [Array.extract_append_extract, Nat.min_eq_left (by omega), Nat.max_eq_right (by omega)]

/-- **EthLib accepts exactly the 128-byte inputs.** -/
theorem SszValue.spec_accepts_iff (bs : Array UInt8) : (∃ v, deserialize desc bs = .ok v) ↔ bs.size = 128 := by
  constructor
  · rintro ⟨v, hd⟩
    obtain ⟨g, rfl, rfl⟩ := SszValue.accepted_is_encoding hd
    exact SszValue.enc_size g
  · intro h
    have r0 := readUint_lt bs 0 8; have r1 := readUint_lt bs 8 8
    simp only [Nat.reducePow, Nat.reduceMul] at r0 r1
    obtain ⟨s, hs⟩ := checkpoint_of_bytes bs 48 (by omega)
    obtain ⟨t, ht⟩ := checkpoint_of_bytes bs 88 (by omega)
    let g : SszValue := ⟨UInt64.ofNat (readUint bs 0 8), UInt64.ofNat (readUint bs 8 8),
      ⟨bs.extract 16 48, by simp; omega⟩, s, t⟩
    have e : bs = SszValue.encode g := by
      simp only [g, SszValue.encode, UInt64.toNat_ofNat_of_lt' r0, UInt64.toNat_ofNat_of_lt' r1, hs, ht,
        uintBytes_readUint_slice bs 0 8 (by omega), uintBytes_readUint_slice bs 8 8 (by omega)]
      simp only [Nat.zero_add, Nat.reduceAdd]
      simp (config := {decide := true}) only [Array.extract_append_extract, Nat.min_def, Nat.max_def, ↓reduceIte]
      rw [← h]; simp
    rw [e]
    exact ⟨_, SszValue.roundtrip g⟩

/-- `len(buf) ≠ 128`: EthLib rejects. -/
theorem SszValue.spec_rejects (bs : Array UInt8) (h : bs.size ≠ 128) : ∃ e, deserialize desc bs = .error e := by
  cases hd : deserialize desc bs with
  | error e => exact ⟨e, rfl⟩
  | ok v => exact absurd ((SszValue.spec_accepts_iff bs).mp ⟨v, hd⟩) h


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
    exact deserialize_enc (G := SszValue) (toV := SszValue.toValue) (enc := SszValue.encode) checker_wellFormed
      SszValue.serialize_eq_checker SszValue.toValue_fits_checker g
  · intro h
    obtain ⟨g, rfl, rfl⟩ := accepted_is_enc (G := SszValue) (toV := SszValue.toValue) (enc := SszValue.encode) checker_wellFormed
      SszValue.serialize_eq_checker SszValue.toValue_surjective_checker h
    exact SszValue.roundtrip g

end Prysm.AttestationData
