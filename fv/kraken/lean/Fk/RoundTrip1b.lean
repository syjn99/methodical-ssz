import Fk.RoundTrip
import Fk.NeSpec
import Fk.LcSpec
import Fk.BlSpec
import Fk.BvSpec

/-!
# 1b round trips at the EthLib level (BitVec, Nested, ListC, BitL) and the
# Nested encoder bytes

As in `Fk/RoundTrip.lean`: EthLib decodes `enc g` to `g.toValue`, and the
abstraction is injective, so with the marshal theorem (bytes = `enc g`) and the
unmarshal accept theorem (receiver holds a `g'` with `g'.toValue = v`) the
decoded Go value is `g`. ListC has no machine encoder or decoder-accept
theorem (REPORT-1b); its line here is the EthLib part only.
-/

open Fv1 EthLib.Serialization.Ssz

theorem bv_roundtrip (g : BitVecG) :
    deserialize bvDesc (bvEncode g) = .ok g.toValue ∧ ∀ g', g'.toValue = g.toValue → g' = g :=
  ⟨deserialize_enc bvDesc_wellFormed bv_serialize bv_toValue_fits g,
   fun g' h => bv_toValue_injective g' g h⟩

theorem ne_roundtrip (g : NestedG) (hg : g.ok) :
    deserialize neDesc (neEncode g) = .ok g.toValue ∧ ∀ g', g'.toValue = g.toValue → g' = g :=
  ⟨ne_deserialize_enc g hg, fun g' h => ne_toValue_injective g' g h⟩

theorem lc_items_injective : ∀ (a b : List ListU64), a.map ListU64.toValue = b.map ListU64.toValue → a = b
  | [], [], _ => rfl
  | x :: xs, y :: ys, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [lu_toValue_injective x y h.1, lc_items_injective xs ys h.2]
  | [], _ :: _, h | _ :: _, [], h => by simp at h

theorem lc_toValue_injective (g h : ListCG) (e : g.toValue = h.toValue) : g = h := by
  obtain ⟨a⟩ := g; obtain ⟨b⟩ := h
  simp only [ListCG.toValue, Value.seq.injEq, List.cons.injEq, and_true] at e
  rw [lc_items_injective a b e]

theorem allFit_lu : ∀ (items : List ListU64), (∀ x ∈ items, x.ok) →
    Value.allFit luDesc (items.map ListU64.toValue) = true
  | [], _ => by simp [Value.allFit]
  | x :: rest, h => by
    simp only [List.map_cons, Value.allFit, Bool.and_eq_true]
    exact ⟨lu_toValue_fits x (h x (by simp)), allFit_lu rest (fun y hy => h y (by simp [hy]))⟩

theorem lc_toValue_fits (g : ListCG) (hg : g.ok) : Value.fits lcDesc g.toValue = true := by
  have h1 := allFit_lu g.items hg.2
  have h2 := hg.1
  simp only [lcDesc, ListCG.toValue, Value.fits, Value.fieldsFit] at *
  simp [h1, h2]

theorem lc_roundtrip (g : ListCG) (hg : g.ok) :
    deserialize lcDesc (lcEncode g) = .ok g.toValue ∧ ∀ g', g'.toValue = g.toValue → g' = g :=
  ⟨deserialize_enc (G := LcG) (toV := fun g => g.1.toValue) (enc := fun g => lcEncode g.1)
     lcDesc_wellFormed (fun g => lc_serialize g.1 g.2) (fun g => lc_toValue_fits g.1 g.2) ⟨g, hg⟩,
   fun g' h => lc_toValue_injective g' g h⟩

theorem bl_roundtrip (g : BitLG) :
    deserialize blDesc (blEncode g) = .ok (blToValue g) ∧ ∀ g', blToValue g' = blToValue g → g' = g :=
  ⟨deserialize_enc blDesc_wellFormed bl_serialize bl_toValue_fits g,
   fun g' h => by
     obtain ⟨a, _⟩ := g'; obtain ⟨b, _⟩ := g
     simp only [blToValue, Value.seq.injEq, List.cons.injEq, Value.bits.injEq, and_true] at h
     subst h; rfl⟩

/-- The bytes `ne_marshal_main` writes at `dst[len:]` are `neEncode g`. -/
theorem ne_marshal_bytes (g : NestedG) :
    (neEncode g).toList = (uintBytes 8 g.a.toNat).toList ++ (scField g.s 0 ++ scField g.s 1
      ++ scField g.s 2 ++ scField g.s 3 ++ scField g.s 4) ++ [28, 0, 0, 0] ++ [4, 0, 0, 0]
      ++ (u64Bytes g.l.l).toList := by
  simp only [neEncode, Array.toList_append, scEncode_toList, luEncode_toList]
  simp [List.append_assoc]; rfl
