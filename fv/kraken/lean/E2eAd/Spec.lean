import E2e.Spec
import E2e.SpecEq
import E2eAd.SpecChecker

/-!
# Spec bridge for the real Prysm `v1alpha1.AttestationData`

Independent hand `Desc`, written from consensus-specs phase0 (`specs/phase0/beacon-chain.md`):

    class AttestationData(Container):
        slot: Slot                # uint64
        index: CommitteeIndex     # uint64
        beacon_block_root: Root   # Bytes32
        source: Checkpoint
        target: Checkpoint

with `Checkpoint` = `E2e.prysmCpDesc` (consensus-specs `Checkpoint(epoch: Epoch, root: Root)`).
The evidence table to the Prysm Go fields is in `prysm/go1.26.10/e2e/ad/SPEC-BRIDGE.md`.
`adCheckerDesc` (generated) is the Desc checker's Desc of `(v1alpha1, AttestationData)`;
`prysmAdDesc_checker` shows the same kinds in the same order (only the names differ) and
`prysmAdDesc_serialize_checker` the equality of `serialize` (every value) and `prysmAdDesc_deserialize_checker`
the same accepted inputs with the same values (EthLib error values are not compared).

`PAd` is the SSZ content of a Go `v1alpha1.AttestationData` with `len(BeaconBlockRoot) = 32`
and non-nil `Source`/`Target` whose `Root`s have length 32. The proofs of the spec lemmas follow
`Fv1/SpecPrysm.lean` and `Fk/AdSpec.lean` (their text, with the names of this namespace); they
read EthLib and `E2e.Spec` only.
-/

namespace E2e
open EthLib.Serialization.Ssz Fv1

/-- consensus-specs phase0 `AttestationData`. -/
def prysmAdDesc : Desc := .container ["slot", "index", "beacon_block_root", "source", "target"]
  [.uint 8, .uint 8, .byteVector 32, prysmCpDesc, prysmCpDesc]

/-- The checker's Desc has the same kinds in the same order; only the names differ. -/
theorem prysmAdDesc_checker :
    prysmAdDesc = .container ["slot", "index", "beacon_block_root", "source", "target"]
      [.uint 8, .uint 8, .byteVector 32, .container ["epoch", "root"] [.uint 8, .byteVector 32],
        .container ["epoch", "root"] [.uint 8, .byteVector 32]]
    ∧ adCheckerDesc = .container ["Slot", "CommitteeIndex", "BeaconBlockRoot", "Source", "Target"]
      [.uint 8, .uint 8, .byteVector 32, .container ["Epoch", "Root"] [.uint 8, .byteVector 32],
        .container ["Epoch", "Root"] [.uint 8, .byteVector 32]] :=
  ⟨rfl, rfl⟩

/-- The reduced hand case `Fv1.adDesc` is the same term (cited, not used). -/
theorem prysmAdDesc_eq_hand : prysmAdDesc = Fv1.adDesc := rfl

theorem prysmAdDesc_wellFormed : prysmAdDesc.wellFormed = .ok () := by rfl
theorem prysmAdDesc_fixedSize : prysmAdDesc.fixedSize = some 128 := by rfl

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
theorem prysmAdDesc_serialize_checker (v : Value) : serialize prysmAdDesc v = serialize adCheckerDesc v := by
  unfold prysmAdDesc adCheckerDesc
  cases v <;> simp only [serialize]
  rename_i vs
  have hc : ∀ w, serialize prysmCpDesc w = serialize (.container ["Epoch", "Root"] [.uint 8, .byteVector 32]) w :=
    prysmCpDesc_serialize_checker
  simp only [serializeStruct]
  rw [serializeFields_congr _ [.uint 8, .uint 8, .byteVector 32, .container ["Epoch", "Root"] [.uint 8, .byteVector 32],
      .container ["Epoch", "Root"] [.uint 8, .byteVector 32]] vs
    (.cons (fun _ => rfl) (.cons (fun _ => rfl) (.cons (fun _ => rfl) (.cons hc (.cons hc .nil)))))]
  rfl

/-- The SSZ content of a Go `v1alpha1.AttestationData` (non-nil Source/Target, all Roots of length 32). -/
structure PAd where
  slot : UInt64
  index : UInt64
  root : Vector UInt8 32
  source : PCp
  target : PCp

def PAd.toValue (g : PAd) : Value :=
  .seq [.uint g.slot.toNat, .uint g.index.toNat, .bytes g.root.toArray, g.source.toValue, g.target.toValue]

/-- `uintBytes 8 slot ++ uintBytes 8 index ++ root ++ enc source ++ enc target`. -/
def padEnc (g : PAd) : Array UInt8 :=
  uintBytes 8 g.slot.toNat ++ uintBytes 8 g.index.toNat ++ g.root.toArray ++ pcpEnc g.source ++ pcpEnc g.target

theorem pad_enc_size (g : PAd) : (padEnc g).size = 128 := by
  simp [padEnc, Fv.uintBytes_size, pcp_enc_size]

theorem pcp_toValue_injective (g h : PCp) (e : g.toValue = h.toValue) : g = h := by
  obtain ⟨a, r⟩ := g; obtain ⟨a', r'⟩ := h
  simp only [PCp.toValue, Value.seq.injEq, List.cons.injEq, Value.uint.injEq, Value.bytes.injEq, and_true] at e
  rw [UInt64.toNat_inj.mp e.1, Vector.toArray_inj.mp e.2]

theorem pad_toValue_fits (g : PAd) : Value.fits prysmAdDesc g.toValue = true := by
  have := g.slot.toNat_lt; have := g.index.toNat_lt
  have h1 := pcp_toValue_fits g.source; have h2 := pcp_toValue_fits g.target
  simp only [prysmAdDesc, PAd.toValue, Value.fits, Value.fieldsFit] at *
  simp [h1, h2]; omega

theorem pad_toValue_injective (g h : PAd) (e : g.toValue = h.toValue) : g = h := by
  obtain ⟨a, b, r, s, t⟩ := g; obtain ⟨a', b', r', s', t'⟩ := h
  simp only [PAd.toValue, Value.seq.injEq, List.cons.injEq, Value.uint.injEq, Value.bytes.injEq,
    and_true] at e
  obtain ⟨e1, e2, e3, e4, e5⟩ := e
  rw [UInt64.toNat_inj.mp e1, UInt64.toNat_inj.mp e2, Vector.toArray_inj.mp e3, pcp_toValue_injective s s' e4,
    pcp_toValue_injective t t' e5]

theorem pad_toValue_surjective (v : Value) (h : Value.fits prysmAdDesc v = true) :
    ∃ g : PAd, g.toValue = v := by
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
    obtain ⟨s, rfl⟩ := pcp_toValue_surjective v4 h4
    obtain ⟨t, rfl⟩ := pcp_toValue_surjective v5 h5
    simp only [Nat.reduceMul, Nat.reducePow] at ha hb
    exact ⟨⟨UInt64.ofNat a, UInt64.ofNat b, ⟨d, hd⟩, s, t⟩,
      by simp [PAd.toValue, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]⟩

theorem pad_toValue_surjective' (v : Value) (h : Value.fits prysmAdDesc v = true) : ∃ g : PAd, g.toValue = v :=
  pad_toValue_surjective v h

/-- **`serialize g = slot ‖ index ‖ root ‖ source ‖ target`.** -/
theorem pad_serialize (g : PAd) : serialize prysmAdDesc g.toValue = .ok (padEnc g) := by
  obtain ⟨a, b, ⟨r, hr⟩, s, t⟩ := g
  have := a.toNat_lt; have := b.toNat_lt
  have hs := pcp_serialize s; have ht := pcp_serialize t
  simp only [prysmAdDesc, PAd.toValue, serialize, serializeStruct, serializeFields, Vector.toArray_mk, hr]
  rw [hs, ht]
  simp (config := {decide := true}) [*, bind, Except.bind, pure, Except.pure, assemble, headWidth, bodyWidth,
    headOf, bodiesOf, Desc.isFixed, Desc.fixedSize, Fv.uintBytes_size, bytesPerOffset, padEnc, prysmCpDesc,
    pcp_enc_size, Desc.fieldsFixedSize, Array.append_assoc]

/-- **Spec roundtrip.** -/
theorem pad_roundtrip (g : PAd) : deserialize prysmAdDesc (padEnc g) = .ok g.toValue :=
  deserialize_enc (G := PAd) (toV := PAd.toValue) (enc := padEnc) prysmAdDesc_wellFormed pad_serialize
    pad_toValue_fits g

theorem pad_accepted_is_enc {bs : Array UInt8} {v : Value} (h : deserialize prysmAdDesc bs = .ok v) :
    ∃ g : PAd, v = g.toValue ∧ bs = padEnc g :=
  accepted_is_enc (G := PAd) (toV := PAd.toValue) (enc := padEnc) prysmAdDesc_wellFormed pad_serialize
    pad_toValue_surjective' h

theorem pcp_of_bytes (bs : Array UInt8) (o : Nat) (h : o + 40 ≤ bs.size) :
    ∃ c : PCp, pcpEnc c = bs.extract o (o + 40) := by
  have r8 := readUint_lt bs o 8
  simp only [Nat.reducePow, Nat.reduceMul] at r8
  refine ⟨⟨UInt64.ofNat (readUint bs o 8), ⟨bs.extract (o + 8) (o + 40), by simp; omega⟩⟩, ?_⟩
  simp only [pcpEnc, UInt64.toNat_ofNat_of_lt' r8, uintBytes_readUint_slice bs o 8 (by omega)]
  rw [Array.extract_append_extract, Nat.min_eq_left (by omega), Nat.max_eq_right (by omega)]

/-- **EthLib accepts exactly the 128-byte inputs.** -/
theorem pad_spec_accepts_iff (bs : Array UInt8) : (∃ v, deserialize prysmAdDesc bs = .ok v) ↔ bs.size = 128 := by
  constructor
  · rintro ⟨v, hd⟩
    obtain ⟨g, rfl, rfl⟩ := pad_accepted_is_enc hd
    exact pad_enc_size g
  · intro h
    have r0 := readUint_lt bs 0 8; have r1 := readUint_lt bs 8 8
    simp only [Nat.reducePow, Nat.reduceMul] at r0 r1
    obtain ⟨s, hs⟩ := pcp_of_bytes bs 48 (by omega)
    obtain ⟨t, ht⟩ := pcp_of_bytes bs 88 (by omega)
    let g : PAd := ⟨UInt64.ofNat (readUint bs 0 8), UInt64.ofNat (readUint bs 8 8),
      ⟨bs.extract 16 48, by simp; omega⟩, s, t⟩
    have e : bs = padEnc g := by
      simp only [g, padEnc, UInt64.toNat_ofNat_of_lt' r0, UInt64.toNat_ofNat_of_lt' r1, hs, ht,
        uintBytes_readUint_slice bs 0 8 (by omega), uintBytes_readUint_slice bs 8 8 (by omega)]
      simp only [Nat.zero_add, Nat.reduceAdd]
      simp (config := {decide := true}) only [Array.extract_append_extract, Nat.min_def, Nat.max_def, ↓reduceIte]
      rw [← h]; simp
    rw [e]
    exact ⟨_, pad_roundtrip g⟩

/-- `len(buf) ≠ 128`: EthLib rejects. -/
theorem pad_spec_rejects (bs : Array UInt8) (h : bs.size ≠ 128) : ∃ e, deserialize prysmAdDesc bs = .error e := by
  cases hd : deserialize prysmAdDesc bs with
  | error e => exact ⟨e, rfl⟩
  | ok v => exact absurd ((pad_spec_accepts_iff bs).mp ⟨v, hd⟩) h


/-! ### The checker Desc decodes like the hand Desc (accepted inputs and values)

EthLib's error values are not compared: the statement is that both Descs accept the same
byte arrays with the same value. -/

theorem adChecker_wellFormed : adCheckerDesc.wellFormed = .ok () := by rfl

theorem pad_serialize_checker (g : PAd) : serialize adCheckerDesc g.toValue = .ok (padEnc g) := by
  rw [← prysmAdDesc_serialize_checker]; exact pad_serialize g

theorem pad_toValue_fits_checker (g : PAd) : Value.fits adCheckerDesc g.toValue = true := by
  have := g.slot.toNat_lt; have := g.index.toNat_lt
  have := g.source.epoch.toNat_lt; have := g.target.epoch.toNat_lt
  simp [adCheckerDesc, PAd.toValue, PCp.toValue, Value.fits, Value.fieldsFit]; omega

theorem pcp_toValue_surjective_checker (v : Value)
    (h : Value.fits (.container ["Epoch", "Root"] [.uint 8, .byteVector 32]) v = true) :
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

theorem pad_toValue_surjective_checker (v : Value) (h : Value.fits adCheckerDesc v = true) :
    ∃ g : PAd, g.toValue = v := by
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
    obtain ⟨s, rfl⟩ := pcp_toValue_surjective_checker v4 h4
    obtain ⟨t, rfl⟩ := pcp_toValue_surjective_checker v5 h5
    simp only [Nat.reduceMul, Nat.reducePow] at ha hb
    exact ⟨⟨UInt64.ofNat a, UInt64.ofNat b, ⟨d, hd⟩, s, t⟩,
      by simp [PAd.toValue, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]⟩

/-- **Codec equality on the accepted inputs**: the checker Desc accepts `bs` with value `v`
exactly when the hand Desc does. -/
theorem prysmAdDesc_deserialize_checker (bs : Array UInt8) (v : Value) :
    deserialize prysmAdDesc bs = .ok v ↔ deserialize adCheckerDesc bs = .ok v := by
  constructor
  · intro h
    obtain ⟨g, rfl, rfl⟩ := pad_accepted_is_enc h
    exact deserialize_enc (G := PAd) (toV := PAd.toValue) (enc := padEnc) adChecker_wellFormed
      pad_serialize_checker pad_toValue_fits_checker g
  · intro h
    obtain ⟨g, rfl, rfl⟩ := accepted_is_enc (G := PAd) (toV := PAd.toValue) (enc := padEnc) adChecker_wellFormed
      pad_serialize_checker pad_toValue_surjective_checker h
    exact pad_roundtrip g

end E2e
