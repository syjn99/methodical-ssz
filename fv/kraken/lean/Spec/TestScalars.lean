import EthLib.Serialization.Ssz
import Spec.TestFixed

/-!
# Spec: `target.Scalars`

    type Scalars struct { A uint8; B uint16; C uint32; D uint64; E bool }

    class Scalars(Container):
        a: uint8
        b: uint16
        c: uint32
        d: uint64
        e: boolean

EthLib `Desc.uint` takes a byte width, so uint64 is `.uint 8`.
-/

namespace Spec
open EthLib.Serialization.Ssz

def scalarsDesc : Desc := .container ["a", "b", "c", "d", "e"] [.uint 1, .uint 2, .uint 4, .uint 8, .bool]

theorem scalarsDesc_wellFormed : scalarsDesc.wellFormed = .ok () := by rfl
theorem scalarsDesc_fixedSize : scalarsDesc.fixedSize = some 16 := by rfl

/-- A Go value of type `target.Scalars`. -/
structure Scalars where
  a : UInt8
  b : UInt16
  c : UInt32
  d : UInt64
  e : Bool

def Scalars.toValue (v : Scalars) : Value :=
  .seq [.uint v.a.toNat, .uint v.b.toNat, .uint v.c.toNat, .uint v.d.toNat, .bool v.e]

theorem scalars_toValue_fits (v : Scalars) : Value.fits scalarsDesc v.toValue = true := by
  have := v.a.toNat_lt; have := v.b.toNat_lt; have := v.c.toNat_lt; have := v.d.toNat_lt
  simp [Scalars.toValue, scalarsDesc, Value.fits, Value.fieldsFit]; omega

theorem scalars_toValue_injective (v w : Scalars) (h : v.toValue = w.toValue) : v = w := by
  obtain ⟨a, b, c, d, e⟩ := v; obtain ⟨a', b', c', d', e'⟩ := w
  simp only [Scalars.toValue, Value.seq.injEq, List.cons.injEq, Value.uint.injEq, Value.bool.injEq,
    and_true] at h
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  have := UInt8.toNat_inj.mp h1; have := UInt16.toNat_inj.mp h2; have := UInt32.toNat_inj.mp h3
  have := UInt64.toNat_inj.mp h4
  subst_vars; rfl

theorem fits_uint {w : Nat} {v : Value} (h : Value.fits (.uint w) v = true) :
    ∃ n, v = .uint n ∧ n < 2 ^ (8 * w) := by
  cases v <;> simp [Value.fits] at h ⊢; exact h

theorem fits_bool {v : Value} (h : Value.fits .bool v = true) : ∃ b, v = .bool b := by
  cases v <;> simp [Value.fits] at h ⊢

theorem fieldsFit_cons {f : Desc} {fs : List Desc} {v : Value} {vs : List Value} :
    Value.fieldsFit (f :: fs) (v :: vs) = true ↔ Value.fits f v = true ∧ Value.fieldsFit fs vs = true := by
  simp [Value.fieldsFit]

theorem fieldsFit_length : ∀ {fs : List Desc} {vs : List Value}, Value.fieldsFit fs vs = true → vs.length = fs.length
  | [], [], _ => rfl
  | _ :: _, _ :: _, h => by rw [fieldsFit_cons] at h; simp [fieldsFit_length h.2]
  | [], _ :: _, h | _ :: _, [], h => by simp [Value.fieldsFit] at h

theorem fits_container {names : List String} {fs : List Desc} {v : Value}
    (h : Value.fits (.container names fs) v = true) : ∃ vs, v = .seq vs ∧ Value.fieldsFit fs vs = true := by
  cases v <;> simp [Value.fits] at h ⊢; exact h

theorem scalars_toValue_surjective (v : Value) (h : Value.fits scalarsDesc v = true) :
    ∃ g : Scalars, g.toValue = v := by
  obtain ⟨vs, rfl, hf⟩ := fits_container h
  have hl := fieldsFit_length hf
  match vs, hl with
  | [v1, v2, v3, v4, v5], _ =>
    simp only [fieldsFit_cons] at hf
    obtain ⟨h1, h2, h3, h4, h5, -⟩ := hf
    obtain ⟨a, rfl, ha⟩ := fits_uint h1; obtain ⟨b, rfl, hb⟩ := fits_uint h2
    obtain ⟨c, rfl, hc⟩ := fits_uint h3; obtain ⟨d, rfl, hd⟩ := fits_uint h4
    obtain ⟨e, rfl⟩ := fits_bool h5
    refine ⟨⟨UInt8.ofNat a, UInt16.ofNat b, UInt32.ofNat c, UInt64.ofNat d, e⟩, ?_⟩
    simp only [Nat.reduceMul, Nat.reducePow] at ha hb hc hd
    simp [Scalars.toValue, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt hc,
      Nat.mod_eq_of_lt hd]

/-! ## Encoding -/

/-- The 16 bytes of an encoding, as a function of the Go value. -/
def scalarsEncode (g : Scalars) : Array UInt8 :=
  uintBytes 1 g.a.toNat ++ uintBytes 2 g.b.toNat ++ uintBytes 4 g.c.toNat ++ uintBytes 8 g.d.toNat ++
    #[if g.e then 1 else 0]

theorem scalars_serialize (g : Scalars) : serialize scalarsDesc g.toValue = .ok (scalarsEncode g) := by
  have := g.a.toNat_lt; have := g.b.toNat_lt; have := g.c.toNat_lt; have := g.d.toNat_lt
  simp only [scalarsDesc, Scalars.toValue, serialize, serializeStruct, serializeFields]
  simp (config := {decide := true}) [*, bind, Except.bind, pure, Except.pure, assemble, headWidth, bodyWidth,
    headOf, bodiesOf, Desc.isFixed, Desc.fixedSize, Spec.uintBytes_size, bytesPerOffset, scalarsEncode]

theorem scalars_encode_size (g : Scalars) : (scalarsEncode g).size = 16 := by
  simp [scalarsEncode, Spec.uintBytes_size]

end Spec
