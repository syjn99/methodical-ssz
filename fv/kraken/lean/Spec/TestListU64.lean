import Spec.TestScalars

/-!
# Spec: `target.ListU64`

    type ListU64 struct { L []uint64 `ssz-max:"16"` }

    class ListU64(Container):
        l: List[uint64, 16]

The brief writes the Desc as `.list (.uint 64) 16`. EthLib's `Desc.uint`
takes a byte width (`[1, 2, 4, 8, 16, 32]`), so uint64 is `.uint 8` and
`.uint 64` is not well formed (a disagreement with the brief).
-/

namespace Spec
open EthLib.Serialization.Ssz

def luDesc : Desc := .container ["l"] [.list (.uint 8) 16]

theorem luDesc_wellFormed : luDesc.wellFormed = .ok () := by rfl
theorem luDesc_fixedSize : luDesc.fixedSize = none := by rfl

/-- A Go value of type `target.ListU64`: the elements of `L`. -/
structure ListU64 where
  l : List UInt64

def ListU64.toValue (v : ListU64) : Value := .seq [.seq (v.l.map fun x => .uint x.toNat)]

/-- The values a Go `ListU64` can hold that EthLib accepts: at most 16 elements. -/
def ListU64.ok (v : ListU64) : Prop := v.l.length ≤ 16

theorem allFit_u64 (l : List UInt64) : Value.allFit (.uint 8) (l.map fun x => .uint x.toNat) = true := by
  induction l with
  | nil => simp [Value.allFit]
  | cons x xs ih => have := x.toNat_lt; simp [Value.allFit, Value.fits, ih]; omega

theorem lu_toValue_fits (v : ListU64) (h : v.ok) : Value.fits luDesc v.toValue = true := by
  simp [ListU64.toValue, luDesc, Value.fits, Value.fieldsFit, allFit_u64, ListU64.ok] at h ⊢; exact h

theorem lu_toValue_injective (v w : ListU64) (h : v.toValue = w.toValue) : v = w := by
  obtain ⟨l⟩ := v; obtain ⟨l'⟩ := w
  simp only [ListU64.toValue, Value.seq.injEq, List.cons.injEq, and_true] at h
  congr
  induction l generalizing l' with
  | nil => cases l' <;> simp_all
  | cons x xs ih =>
    cases l' with
    | nil => simp at h
    | cons y ys =>
      simp only [List.map_cons, List.cons.injEq, Value.uint.injEq] at h
      rw [UInt64.toNat_inj.mp h.1, ih ys h.2]

theorem allFit_u64_inv : ∀ (vs : List Value), Value.allFit (.uint 8) vs = true →
    ∃ l : List UInt64, l.map (fun x => Value.uint x.toNat) = vs
  | [], _ => ⟨[], rfl⟩
  | v :: vs, h => by
    simp only [Value.allFit, Bool.and_eq_true] at h
    obtain ⟨n, rfl, hn⟩ := fits_uint h.1
    obtain ⟨l, hl⟩ := allFit_u64_inv vs h.2
    exact ⟨UInt64.ofNat n :: l, by simp [hl, Nat.mod_eq_of_lt (by simpa using hn)]⟩

theorem lu_toValue_surjective (v : Value) (h : Value.fits luDesc v = true) :
    ∃ g : ListU64, g.ok ∧ g.toValue = v := by
  obtain ⟨vs, rfl, hf⟩ := fits_container h
  have hl := fieldsFit_length hf
  match vs, hl with
  | [v1], _ =>
    simp only [fieldsFit_cons] at hf
    obtain ⟨h1, -⟩ := hf
    obtain ⟨es, rfl, hlen, hall⟩ : ∃ es, v1 = .seq es ∧ es.length ≤ 16 ∧ Value.allFit (.uint 8) es = true := by
      cases v1 <;> simp [Value.fits] at h1 ⊢; exact h1
    obtain ⟨l, rfl⟩ := allFit_u64_inv es hall
    exact ⟨⟨l⟩, by simpa [ListU64.ok] using hlen, rfl⟩

/-! ## Encoding -/

/-- The element bytes: each element as 8 little-endian bytes. -/
def u64Bytes : List UInt64 → Array UInt8
  | [] => #[]
  | x :: xs => uintBytes 8 x.toNat ++ u64Bytes xs

theorem u64Bytes_size (l : List UInt64) : (u64Bytes l).size = 8 * l.length := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp [u64Bytes, Spec.uintBytes_size, ih]; omega

/-- The encoding: the offset 4, then the elements. -/
def luEncode (g : ListU64) : Array UInt8 := uintBytes 4 4 ++ u64Bytes g.l

theorem serializeEach_u64 (l : List UInt64) :
    serializeEach (.uint 8) (l.map fun x => .uint x.toNat) = .ok (l.map fun x => uintBytes 8 x.toNat) := by
  induction l with
  | nil => simp [serializeEach]
  | cons x xs ih =>
    have := x.toNat_lt
    simp only [List.map_cons, serializeEach, serialize, ih]
    simp [bind, Except.bind, pure, Except.pure, show x.toNat < 2 ^ (8 * 8) by simpa using this]

abbrev inl (l : List UInt64) : List (Bool × Array UInt8) :=
  ((l.map fun x => uintBytes 8 x.toNat).map fun _ => true).zip (l.map fun x => uintBytes 8 x.toNat)

theorem inl_cons (x : UInt64) (l : List UInt64) : inl (x :: l) = (true, uintBytes 8 x.toNat) :: inl l := rfl

theorem inl_headWidth (l : List UInt64) : headWidth (((l.map fun x => uintBytes 8 x.toNat).map fun _ => true).zip (l.map fun x => uintBytes 8 x.toNat)) = 8 * l.length := by
  induction l with
  | nil => rfl
  | cons x xs ih => rw [show ((((x :: xs).map fun x => uintBytes 8 x.toNat).map fun _ => true).zip ((x :: xs).map fun x => uintBytes 8 x.toNat)) = (true, uintBytes 8 x.toNat) :: (((xs.map fun x => uintBytes 8 x.toNat).map fun _ => true).zip (xs.map fun x => uintBytes 8 x.toNat)) from rfl]; simp only [headWidth, if_pos, Spec.uintBytes_size, ih, List.length_cons]; omega
theorem inl_bodyWidth (l : List UInt64) : bodyWidth (((l.map fun x => uintBytes 8 x.toNat).map fun _ => true).zip (l.map fun x => uintBytes 8 x.toNat)) = 0 := by
  induction l with
  | nil => rfl
  | cons x xs ih => rw [show ((((x :: xs).map fun x => uintBytes 8 x.toNat).map fun _ => true).zip ((x :: xs).map fun x => uintBytes 8 x.toNat)) = (true, uintBytes 8 x.toNat) :: (((xs.map fun x => uintBytes 8 x.toNat).map fun _ => true).zip (xs.map fun x => uintBytes 8 x.toNat)) from rfl]; simp only [bodyWidth, ih]
theorem inl_headOf (l : List UInt64) (s : Nat) : headOf s (((l.map fun x => uintBytes 8 x.toNat).map fun _ => true).zip (l.map fun x => uintBytes 8 x.toNat)) = u64Bytes l := by
  induction l with
  | nil => rfl
  | cons x xs ih => rw [show ((((x :: xs).map fun x => uintBytes 8 x.toNat).map fun _ => true).zip ((x :: xs).map fun x => uintBytes 8 x.toNat)) = (true, uintBytes 8 x.toNat) :: (((xs.map fun x => uintBytes 8 x.toNat).map fun _ => true).zip (xs.map fun x => uintBytes 8 x.toNat)) from rfl]; simp only [headOf, ih, u64Bytes]
theorem inl_bodiesOf (l : List UInt64) : bodiesOf (((l.map fun x => uintBytes 8 x.toNat).map fun _ => true).zip (l.map fun x => uintBytes 8 x.toNat)) = #[] := by
  induction l with
  | nil => rfl
  | cons x xs ih => rw [show ((((x :: xs).map fun x => uintBytes 8 x.toNat).map fun _ => true).zip ((x :: xs).map fun x => uintBytes 8 x.toNat)) = (true, uintBytes 8 x.toNat) :: (((xs.map fun x => uintBytes 8 x.toNat).map fun _ => true).zip (xs.map fun x => uintBytes 8 x.toNat)) from rfl]; simp only [bodiesOf, ih]

theorem lu_serialize (g : ListU64) (h : g.ok) : serialize luDesc g.toValue = .ok (luEncode g) := by
  obtain ⟨l⟩ := g
  simp only [ListU64.ok] at h
  have h32 : 8 * l.length < 2 ^ (8 * bytesPerOffset) := by simp [bytesPerOffset]; omega
  have h32' : 4 + 8 * l.length < 2 ^ (8 * bytesPerOffset) := by simp [bytesPerOffset]; omega
  simp only [luDesc, ListU64.toValue, serialize, serializeStruct, serializeFields, serializeSequence,
    List.length_map, h, decide_true, if_true, serializeEach_u64]
  simp only [bind, Except.bind, pure, Except.pure, assemble, Desc.isFixed, Desc.fixedSize, Option.isSome_some]
  simp only [inl_headWidth, inl_bodyWidth, inl_headOf, inl_bodiesOf]
  simp only [Nat.add_zero,
    show ¬ (8 * l.length ≥ 2 ^ (8 * bytesPerOffset)) from Nat.not_le.mpr h32, if_false,
    Array.append_empty, Desc.isFixed, Desc.fixedSize, List.map_cons, List.map_nil, List.zip_cons_cons,
    List.zip_nil_right, headWidth, bodyWidth, headOf, bodiesOf, Bool.false_eq_true, u64Bytes_size,
    Array.size_append, Spec.uintBytes_size]
  have h4 : ¬ (4294967296 ≤ 4 + 8 * l.length) := by omega
  simp [bodyWidth, headOf, bodiesOf, u64Bytes_size, h4, bytesPerOffset, luEncode]

theorem lu_encode_size (g : ListU64) : (luEncode g).size = 4 + 8 * g.l.length := by
  simp [luEncode, Spec.uintBytes_size, u64Bytes_size]

end Spec
