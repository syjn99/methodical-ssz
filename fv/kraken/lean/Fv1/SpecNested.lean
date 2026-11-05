import Fv1.SpecList

/-!
# Spec: `target.Nested`

    type Nested struct { A uint64; S *Scalars; L *ListU64 }

    class Nested(Container):
        a: uint64
        s: Scalars          # fixed size 16, inline
        l: ListU64          # variable size, behind an offset

Encoding: A (8) ‖ S (16) ‖ offset 28 (4) ‖ L's encoding.
-/

namespace Fv1
open EthLib.Serialization.Ssz

def neDesc : Desc := .container ["a", "s", "l"] [.uint 8, scDesc, luDesc]

theorem neDesc_wellFormed : neDesc.wellFormed = .ok () := by rfl

/-- A Go value of type `target.Nested` (S and L non-nil after decoding). -/
structure NestedG where
  a : UInt64
  s : Scalars
  l : ListU64

def NestedG.toValue (g : NestedG) : Value := .seq [.uint g.a.toNat, g.s.toValue, g.l.toValue]

def NestedG.ok (g : NestedG) : Prop := g.l.ok

def neEncode (g : NestedG) : Array UInt8 :=
  uintBytes 8 g.a.toNat ++ scEncode g.s ++ uintBytes 4 28 ++ luEncode g.l

theorem ne_encode_size (g : NestedG) : (neEncode g).size = 32 + 8 * g.l.l.length := by
  simp [neEncode, Fv.uintBytes_size, sc_encode_size, lu_encode_size]; omega

theorem ne_toValue_fits (g : NestedG) (h : g.ok) : Value.fits neDesc g.toValue = true := by
  have := g.a.toNat_lt
  have h1 := sc_toValue_fits g.s
  have h2 := lu_toValue_fits g.l h
  simp only [neDesc, NestedG.toValue, Value.fits, Value.fieldsFit] at *
  simp [h1, h2]; omega

theorem ne_toValue_injective (g h : NestedG) (e : g.toValue = h.toValue) : g = h := by
  obtain ⟨a, s, l⟩ := g; obtain ⟨a', s', l'⟩ := h
  simp only [NestedG.toValue, Value.seq.injEq, List.cons.injEq, Value.uint.injEq, and_true] at e
  obtain ⟨e1, e2, e3⟩ := e
  rw [UInt64.toNat_inj.mp e1, sc_toValue_injective s s' e2, lu_toValue_injective l l' e3]

theorem ne_toValue_surjective (v : Value) (h : Value.fits neDesc v = true) :
    ∃ g : NestedG, g.ok ∧ g.toValue = v := by
  obtain ⟨vs, rfl, hf⟩ := fits_container h
  have hl := fieldsFit_length hf
  match vs, hl with
  | [v1, v2, v3], _ =>
    simp only [fieldsFit_cons] at hf
    obtain ⟨h1, h2, h3, -⟩ := hf
    obtain ⟨a, rfl, ha⟩ := fits_uint h1
    obtain ⟨s, rfl⟩ := sc_toValue_surjective v2 h2
    obtain ⟨l, hl, rfl⟩ := lu_toValue_surjective v3 h3
    refine ⟨⟨UInt64.ofNat a, s, l⟩, hl, ?_⟩
    simp only [Nat.reduceMul, Nat.reducePow] at ha
    simp [NestedG.toValue, Nat.mod_eq_of_lt ha]

theorem ne_serialize (g : NestedG) (h : g.ok) : serialize neDesc g.toValue = .ok (neEncode g) := by
  have := g.a.toNat_lt
  have hs := sc_serialize g.s
  have hl := lu_serialize g.l h
  have hls := lu_encode_size g.l
  have hok : g.l.l.length ≤ 16 := h
  simp only [neDesc, NestedG.toValue, serialize, serializeStruct, serializeFields]
  rw [hs, hl]
  simp (config := {decide := true}) [*, bind, Except.bind, pure, Except.pure, assemble, headWidth, bodyWidth,
    headOf, bodiesOf, Desc.isFixed, Desc.fixedSize, Fv.uintBytes_size, bytesPerOffset, neEncode, scDesc, luDesc,
    sc_encode_size, Desc.fieldsFixedSize, hls]
  omega

end Fv1
