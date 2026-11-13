import Spec.TestListU64

/-!
# Spec: `target.Nested`

    type Nested struct { A uint64; S *Scalars; L *ListU64 }

    class Nested(Container):
        a: uint64
        s: Scalars          # fixed size 16, inline
        l: ListU64          # variable size, behind an offset

Encoding: A (8) ‖ S (16) ‖ offset 28 (4) ‖ L's encoding.
-/

namespace Spec
open EthLib.Serialization.Ssz

def nestedDesc : Desc := .container ["a", "s", "l"] [.uint 8, scalarsDesc, listU64Desc]

theorem nestedDesc_wellFormed : nestedDesc.wellFormed = .ok () := by rfl

/-- A Go value of type `target.Nested` (S and L non-nil after decoding). -/
structure NestedValue where
  a : UInt64
  s : Scalars
  l : ListU64

def NestedValue.toValue (g : NestedValue) : Value := .seq [.uint g.a.toNat, g.s.toValue, g.l.toValue]

def NestedValue.ok (g : NestedValue) : Prop := g.l.ok

def nestedEncode (g : NestedValue) : Array UInt8 :=
  uintBytes 8 g.a.toNat ++ scalarsEncode g.s ++ uintBytes 4 28 ++ listU64Encode g.l

theorem nested_encode_size (g : NestedValue) : (nestedEncode g).size = 32 + 8 * g.l.l.length := by
  simp [nestedEncode, Spec.uintBytes_size, scalars_encode_size, listU64_encode_size]; omega

theorem nested_toValue_fits (g : NestedValue) (h : g.ok) : Value.fits nestedDesc g.toValue = true := by
  have := g.a.toNat_lt
  have h1 := scalars_toValue_fits g.s
  have h2 := listU64_toValue_fits g.l h
  simp only [nestedDesc, Spec.NestedValue.toValue, Value.fits, Value.fieldsFit] at *
  simp [h1, h2]; omega

theorem nested_toValue_injective (g h : NestedValue) (e : g.toValue = h.toValue) : g = h := by
  obtain ⟨a, s, l⟩ := g; obtain ⟨a', s', l'⟩ := h
  simp only [Spec.NestedValue.toValue, Value.seq.injEq, List.cons.injEq, Value.uint.injEq, and_true] at e
  obtain ⟨e1, e2, e3⟩ := e
  rw [UInt64.toNat_inj.mp e1, scalars_toValue_injective s s' e2, listU64_toValue_injective l l' e3]

theorem nested_toValue_surjective (v : Value) (h : Value.fits nestedDesc v = true) :
    ∃ g : NestedValue, g.ok ∧ g.toValue = v := by
  obtain ⟨vs, rfl, hf⟩ := fits_container h
  have hl := fieldsFit_length hf
  match vs, hl with
  | [v1, v2, v3], _ =>
    simp only [fieldsFit_cons] at hf
    obtain ⟨h1, h2, h3, -⟩ := hf
    obtain ⟨a, rfl, ha⟩ := fits_uint h1
    obtain ⟨s, rfl⟩ := scalars_toValue_surjective v2 h2
    obtain ⟨l, hl, rfl⟩ := listU64_toValue_surjective v3 h3
    refine ⟨⟨UInt64.ofNat a, s, l⟩, hl, ?_⟩
    simp only [Nat.reduceMul, Nat.reducePow] at ha
    simp [Spec.NestedValue.toValue, Nat.mod_eq_of_lt ha]

theorem nested_serialize (g : NestedValue) (h : g.ok) : serialize nestedDesc g.toValue = .ok (nestedEncode g) := by
  have := g.a.toNat_lt
  have hs := scalars_serialize g.s
  have hl := listU64_serialize g.l h
  have hls := listU64_encode_size g.l
  have hok : g.l.l.length ≤ 16 := h
  simp only [nestedDesc, Spec.NestedValue.toValue, serialize, serializeStruct, serializeFields]
  rw [hs, hl]
  simp (config := {decide := true}) [*, bind, Except.bind, pure, Except.pure, assemble, headWidth, bodyWidth,
    headOf, bodiesOf, Desc.isFixed, Desc.fixedSize, Spec.uintBytes_size, bytesPerOffset, nestedEncode, scalarsDesc, listU64Desc,
    scalars_encode_size, Desc.fieldsFixedSize, hls]
  omega

end Spec
