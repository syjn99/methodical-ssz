import Spec.TestListU64
import EthLib.Serialization.Proofs.Ssz.Codec.Table

/-!
# Spec: `target.ListC`

    type ListC struct { Items []*ListU64 `ssz-max:"4"` }

    class ListC(Container):
        items: List[ListU64, 4]     # ListU64 is variable size

Encoding: offset 4 (4) ‖ the list: one 4-byte offset per element (the first
is 4n), then the element encodings (`listU64Encode`) end to end.
-/

namespace Spec
open EthLib.Serialization.Ssz

def listOfContainersDesc : Desc := .container ["items"] [.list listU64Desc 4]

theorem listOfContainersDesc_wellFormed : listOfContainersDesc.wellFormed = .ok () := by rfl

/-- A Go value of type `target.ListC` (every element non-nil). -/
structure ListOfContainersValue where
  items : List ListU64

def ListOfContainersValue.toValue (g : ListOfContainersValue) : Value := .seq [.seq (g.items.map ListU64.toValue)]

def ListOfContainersValue.ok (g : ListOfContainersValue) : Prop := g.items.length ≤ 4 ∧ ∀ x ∈ g.items, x.ok

def listOfContainersParts (g : ListOfContainersValue) : List Bytes := g.items.map listU64Encode

/-- The list bytes (`buf[4:]`): offset table then bodies. -/
def listOfContainersBody (g : ListOfContainersValue) : Bytes :=
  headOf (4 * g.items.length) (offsetSlots (listOfContainersParts g)) ++ bodiesOf (offsetSlots (listOfContainersParts g))

def listOfContainersEncode (g : ListOfContainersValue) : Bytes := uintBytes 4 4 ++ listOfContainersBody g

theorem serializeEach_listU64 : ∀ (items : List ListU64), (∀ x ∈ items, x.ok) →
    serializeEach listU64Desc (items.map ListU64.toValue) = .ok (items.map listU64Encode)
  | [], _ => by simp [serializeEach]
  | x :: rest, h => by
    simp only [List.map_cons, serializeEach, listU64_serialize x (h x (by simp)),
      serializeEach_listU64 rest (fun y hy => h y (by simp [hy]))]
    rfl

theorem bodyWidth_offsetSlots : ∀ (parts : List Bytes),
    bodyWidth (offsetSlots parts) = (bodiesOf (offsetSlots parts)).size
  | [] => rfl
  | p :: rest => by simp [offsetSlots_cons, bodyWidth, bodiesOf, bodyWidth_offsetSlots rest]

theorem listU64_bodies_le : ∀ (items : List ListU64), (∀ x ∈ items, x.ok) →
    (bodiesOf (offsetSlots (items.map listU64Encode))).size ≤ 132 * items.length
  | [], _ => by simp [bodiesOf]
  | x :: rest, h => by
    have h1 := listU64_encode_size x
    have h2 : x.l.length ≤ 16 := h x (by simp)
    have := listU64_bodies_le rest (fun y hy => h y (by simp [hy]))
    simp only [List.map_cons, offsetSlots_cons, bodiesOf, Array.size_append, List.length_cons]
    omega

theorem headOf_offsetSlots_size : ∀ (parts : List Bytes) (start : Nat),
    (headOf start (offsetSlots parts)).size = 4 * parts.length
  | [], _ => rfl
  | p :: rest, start => by
    simp [offsetSlots_cons, headOf, headOf_offsetSlots_size rest, Spec.uintBytes_size, bytesPerOffset]; omega

theorem listOfContainersBody_size_le (g : ListOfContainersValue) (h : g.ok) : (listOfContainersBody g).size ≤ 4 * 4 + 132 * 4 := by
  have hb := listU64_bodies_le g.items h.2
  have := h.1
  simp only [listOfContainersBody, listOfContainersParts, Array.size_append, headOf_offsetSlots_size, List.length_map]
  have : 132 * g.items.length ≤ 132 * 4 := Nat.mul_le_mul_left _ this
  omega

theorem listOfContainers_serialize (g : ListOfContainersValue) (h : g.ok) : serialize listOfContainersDesc g.toValue = .ok (listOfContainersEncode g) := by
  obtain ⟨hn, hall⟩ := h
  have hb := listU64_bodies_le g.items hall
  have hw := headWidth_offset (listOfContainersParts g)
  simp only [listOfContainersParts, List.length_map] at hw
  simp only [listOfContainersDesc, Spec.ListOfContainersValue.toValue, serialize, serializeStruct, serializeFields, List.length_map,
    show (g.items.length ≤ 4) = True from propext ⟨fun _ => trivial, fun _ => hn⟩, ite_true]
  simp only [serializeSequence, serializeEach_listU64 g.items hall]
  have hfx : listU64Desc.isFixed = false := rfl
  have hinner : assemble (List.map (fun _ => listU64Desc.isFixed) (List.map listU64Encode g.items)) (List.map listU64Encode g.items)
      = .ok (listOfContainersBody g) := by
    simp only [hfx, assemble, listOfContainersBody, listOfContainersParts]
    rw [show (List.map (fun _ => false) (List.map listU64Encode g.items)).zip (List.map listU64Encode g.items)
      = offsetSlots (List.map listU64Encode g.items) from rfl, hw, bodyWidth_offsetSlots]
    simp only [bytesPerOffset] at hw ⊢
    rw [ite_eq_right_of_eq_false _ _ (by simp; omega), Nat.mul_comm]; rfl
  simp only [bind, Except.bind, pure, Except.pure, hinner]
  simp (config := {decide := true}) [assemble, headWidth, bodyWidth, headOf, bodiesOf, Desc.isFixed,
    Desc.fixedSize, bytesPerOffset, listOfContainersEncode, listU64Desc]
  have := listOfContainersBody_size_le g ⟨hn, hall⟩
  rw [ite_eq_right_of_eq_false _ _ (by simp; omega)]; rfl

theorem allFit_listU64_inv : ∀ (vs : List Value), Value.allFit listU64Desc vs = true →
    ∃ items : List ListU64, (∀ x ∈ items, x.ok) ∧ items.map ListU64.toValue = vs
  | [], _ => ⟨[], by simp, rfl⟩
  | v :: vs, h => by
    simp only [Value.allFit, Bool.and_eq_true] at h
    obtain ⟨x, hx, rfl⟩ := listU64_toValue_surjective v h.1
    obtain ⟨items, hi, he⟩ := allFit_listU64_inv vs h.2
    refine ⟨x :: items, ?_, by simp [he]⟩
    intro y hy; simp at hy; rcases hy with rfl | hy
    · exact hx
    · exact hi y hy

theorem listOfContainers_toValue_surjective (v : Value) (h : Value.fits listOfContainersDesc v = true) :
    ∃ g : ListOfContainersValue, g.ok ∧ g.toValue = v := by
  obtain ⟨vs, rfl, hf⟩ := fits_container h
  have hl := fieldsFit_length hf
  match vs, hl with
  | [v1], _ =>
    simp only [fieldsFit_cons] at hf
    obtain ⟨h1, -⟩ := hf
    obtain ⟨es, rfl, hlen, hall⟩ : ∃ es, v1 = .seq es ∧ es.length ≤ 4 ∧ Value.allFit listU64Desc es = true := by
      cases v1 <;> simp [Value.fits] at h1 ⊢; exact h1
    obtain ⟨items, hi, rfl⟩ := allFit_listU64_inv es hall
    exact ⟨⟨items⟩, ⟨by simpa using hlen, hi⟩, rfl⟩

end Spec
