import Spec.TestListU64

/-!
# Spec: Prysm `Checkpoint` (v7.1.8, commit 51b5a75ebbadf05af22bd2601b5baf7a9e99b66d)

    type Checkpoint struct {
        Epoch Epoch                 // uint64
        Root  []byte `ssz-size:"32"`
    }

    class Checkpoint(Container):
        epoch: Epoch               # uint64
        root: Root                 # Bytes32

The Go values EthLib accepts have `len(Root) = 32` (`CheckpointG` fixes it;
the encoder returns `ssz.ErrBytesLength` otherwise).
-/

namespace Spec
open EthLib.Serialization.Ssz

def checkpointDesc : Desc := .container ["epoch", "root"] [.uint 8, .byteVector 32]

theorem cpDesc_wellFormed : checkpointDesc.wellFormed = .ok () := by rfl
theorem cpDesc_fixedSize : checkpointDesc.fixedSize = some 40 := by rfl

structure CheckpointG where
  epoch : UInt64
  root : Vector UInt8 32

def CheckpointG.toValue (g : CheckpointG) : Value := .seq [.uint g.epoch.toNat, .bytes g.root.toArray]

def cpEncode (g : CheckpointG) : Array UInt8 := uintBytes 8 g.epoch.toNat ++ g.root.toArray

theorem cp_encode_size (g : CheckpointG) : (cpEncode g).size = 40 := by
  simp [cpEncode, Spec.uintBytes_size]

theorem cp_toValue_fits (g : CheckpointG) : Value.fits checkpointDesc g.toValue = true := by
  have := g.epoch.toNat_lt
  simp [CheckpointG.toValue, checkpointDesc, Value.fits, Value.fieldsFit]; omega

theorem cp_toValue_injective (g h : CheckpointG) (e : g.toValue = h.toValue) : g = h := by
  obtain ⟨a, r⟩ := g; obtain ⟨a', r'⟩ := h
  simp only [CheckpointG.toValue, Value.seq.injEq, List.cons.injEq, Value.uint.injEq, Value.bytes.injEq,
    and_true] at e
  obtain ⟨e1, e2⟩ := e
  rw [UInt64.toNat_inj.mp e1, Vector.toArray_inj.mp e2]

theorem cp_toValue_surjective (v : Value) (h : Value.fits checkpointDesc v = true) :
    ∃ g : CheckpointG, g.toValue = v := by
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
    exact ⟨⟨UInt64.ofNat a, ⟨d, hd⟩⟩, by simp [CheckpointG.toValue, Nat.mod_eq_of_lt ha]⟩

theorem cp_serialize (g : CheckpointG) : serialize checkpointDesc g.toValue = .ok (cpEncode g) := by
  obtain ⟨a, ⟨r, hr⟩⟩ := g
  have := a.toNat_lt
  simp only [checkpointDesc, CheckpointG.toValue, serialize, serializeStruct, serializeFields, Vector.toArray_mk, hr]
  simp (config := {decide := true}) [*, bind, Except.bind, pure, Except.pure, assemble, headWidth, bodyWidth,
    headOf, bodiesOf, Desc.isFixed, Desc.fixedSize, Spec.uintBytes_size, bytesPerOffset, cpEncode]

/-! ## Prysm `AttestationData`

    type AttestationData struct {
        Slot            Slot           // uint64
        CommitteeIndex  CommitteeIndex // uint64
        BeaconBlockRoot []byte `ssz-size:"32"`
        Source          *Checkpoint
        Target          *Checkpoint
    }
-/

def attestationDataDesc : Desc := .container ["slot", "index", "beacon_block_root", "source", "target"]
  [.uint 8, .uint 8, .byteVector 32, checkpointDesc, checkpointDesc]

theorem adDesc_wellFormed : attestationDataDesc.wellFormed = .ok () := by rfl
theorem adDesc_fixedSize : attestationDataDesc.fixedSize = some 128 := by rfl

structure AttestationDataG where
  slot : UInt64
  index : UInt64
  root : Vector UInt8 32
  source : CheckpointG
  target : CheckpointG

def AttestationDataG.toValue (g : AttestationDataG) : Value :=
  .seq [.uint g.slot.toNat, .uint g.index.toNat, .bytes g.root.toArray, g.source.toValue, g.target.toValue]

def adEncode (g : AttestationDataG) : Array UInt8 :=
  uintBytes 8 g.slot.toNat ++ uintBytes 8 g.index.toNat ++ g.root.toArray ++ cpEncode g.source ++ cpEncode g.target

theorem ad_encode_size (g : AttestationDataG) : (adEncode g).size = 128 := by
  simp [adEncode, Spec.uintBytes_size, cp_encode_size]

theorem ad_toValue_fits (g : AttestationDataG) : Value.fits attestationDataDesc g.toValue = true := by
  have := g.slot.toNat_lt; have := g.index.toNat_lt
  have h1 := cp_toValue_fits g.source; have h2 := cp_toValue_fits g.target
  simp only [attestationDataDesc, AttestationDataG.toValue, Value.fits, Value.fieldsFit] at *
  simp [h1, h2]; omega

theorem ad_toValue_injective (g h : AttestationDataG) (e : g.toValue = h.toValue) : g = h := by
  obtain ⟨a, b, r, s, t⟩ := g; obtain ⟨a', b', r', s', t'⟩ := h
  simp only [AttestationDataG.toValue, Value.seq.injEq, List.cons.injEq, Value.uint.injEq, Value.bytes.injEq,
    and_true] at e
  obtain ⟨e1, e2, e3, e4, e5⟩ := e
  rw [UInt64.toNat_inj.mp e1, UInt64.toNat_inj.mp e2, Vector.toArray_inj.mp e3, cp_toValue_injective s s' e4,
    cp_toValue_injective t t' e5]

theorem ad_toValue_surjective (v : Value) (h : Value.fits attestationDataDesc v = true) :
    ∃ g : AttestationDataG, g.toValue = v := by
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
    obtain ⟨s, rfl⟩ := cp_toValue_surjective v4 h4
    obtain ⟨t, rfl⟩ := cp_toValue_surjective v5 h5
    simp only [Nat.reduceMul, Nat.reducePow] at ha hb
    exact ⟨⟨UInt64.ofNat a, UInt64.ofNat b, ⟨d, hd⟩, s, t⟩,
      by simp [AttestationDataG.toValue, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]⟩

theorem ad_serialize (g : AttestationDataG) : serialize attestationDataDesc g.toValue = .ok (adEncode g) := by
  obtain ⟨a, b, ⟨r, hr⟩, s, t⟩ := g
  have := a.toNat_lt; have := b.toNat_lt
  have hs := cp_serialize s; have ht := cp_serialize t
  simp only [attestationDataDesc, AttestationDataG.toValue, serialize, serializeStruct, serializeFields, Vector.toArray_mk, hr]
  rw [hs, ht]
  simp (config := {decide := true}) [*, bind, Except.bind, pure, Except.pure, assemble, headWidth, bodyWidth,
    headOf, bodiesOf, Desc.isFixed, Desc.fixedSize, Spec.uintBytes_size, bytesPerOffset, adEncode, checkpointDesc,
    cp_encode_size, Desc.fieldsFixedSize, Array.append_assoc]

end Spec
