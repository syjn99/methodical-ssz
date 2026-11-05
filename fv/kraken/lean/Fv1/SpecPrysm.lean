import Fv1.SpecList

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

namespace Fv1
open EthLib.Serialization.Ssz

def cpDesc : Desc := .container ["epoch", "root"] [.uint 8, .byteVector 32]

theorem cpDesc_wellFormed : cpDesc.wellFormed = .ok () := by rfl
theorem cpDesc_fixedSize : cpDesc.fixedSize = some 40 := by rfl

structure CheckpointG where
  epoch : UInt64
  root : Vector UInt8 32

def CheckpointG.toValue (g : CheckpointG) : Value := .seq [.uint g.epoch.toNat, .bytes g.root.toArray]

def cpEncode (g : CheckpointG) : Array UInt8 := uintBytes 8 g.epoch.toNat ++ g.root.toArray

theorem cp_encode_size (g : CheckpointG) : (cpEncode g).size = 40 := by
  simp [cpEncode, Fv.uintBytes_size]

theorem cp_toValue_fits (g : CheckpointG) : Value.fits cpDesc g.toValue = true := by
  have := g.epoch.toNat_lt
  simp [CheckpointG.toValue, cpDesc, Value.fits, Value.fieldsFit]; omega

theorem cp_toValue_injective (g h : CheckpointG) (e : g.toValue = h.toValue) : g = h := by
  obtain ⟨a, r⟩ := g; obtain ⟨a', r'⟩ := h
  simp only [CheckpointG.toValue, Value.seq.injEq, List.cons.injEq, Value.uint.injEq, Value.bytes.injEq,
    and_true] at e
  obtain ⟨e1, e2⟩ := e
  rw [UInt64.toNat_inj.mp e1, Vector.toArray_inj.mp e2]

theorem cp_toValue_surjective (v : Value) (h : Value.fits cpDesc v = true) :
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

theorem cp_serialize (g : CheckpointG) : serialize cpDesc g.toValue = .ok (cpEncode g) := by
  obtain ⟨a, ⟨r, hr⟩⟩ := g
  have := a.toNat_lt
  simp only [cpDesc, CheckpointG.toValue, serialize, serializeStruct, serializeFields, Vector.toArray_mk, hr]
  simp (config := {decide := true}) [*, bind, Except.bind, pure, Except.pure, assemble, headWidth, bodyWidth,
    headOf, bodiesOf, Desc.isFixed, Desc.fixedSize, Fv.uintBytes_size, bytesPerOffset, cpEncode]

end Fv1
