import EthLib.Serialization.Ssz

/-!
# Hand-written statements for `target.Fixed`

External schema (Go source of the type `Fixed`; this file is kept in fv/kraken
because `Spec.TestScalars` uses its byte lemmas, e.g. `uintBytes_size`):

    type Fixed struct {
        A uint64
        B [32]byte `ssz-size:"32"`
    }

Consensus-specs spelling of the same schema:

    class Fixed(Container):
        a: uint64
        b: Bytes32        # Bytes32 = ByteVector[32]
-/

namespace Spec
open EthLib.Serialization.Ssz

/-! ## Desc and field order -/

/-- The EthLib declaration. Field order is the Go declaration order. -/
def fixedDesc : Desc := .container ["a", "b"] [.uint 8, .byteVector 32]

/-- Field order and layout, one row per field: name, Go struct offset,
SSZ encoding offset, width. The Go offsets are what the code uses
(`ld x5, 0(x10)` for A, `addi x11, x10, 8` for B in MarshalSSZTo). -/
def fieldLayout : List (String × Nat × Nat × Nat) := [("a", 0, 0, 8), ("b", 8, 8, 32)]

theorem fixedDesc_wellFormed : fixedDesc.wellFormed = .ok () := by rfl

theorem fixedDesc_fixedSize : fixedDesc.fixedSize = some 40 := by rfl

/-! ## Go values and the abstraction to EthLib values -/

/-- A Go value of type `target.Fixed`. -/
structure Fixed where
  a : UInt64
  b : Vector UInt8 32

/-- The abstraction function from Go values to EthLib values. -/
def Fixed.toValue (f : Fixed) : Value := .seq [.uint f.a.toNat, .bytes f.b.toArray]

/-- Every Go value maps to a value that fits the declaration. -/
theorem fixed_toValue_fits (f : Fixed) : Value.fits fixedDesc f.toValue = true := by
  have := f.a.toNat_lt
  simp [Fixed.toValue, fixedDesc, Value.fits, Value.fieldsFit]; omega

/-- The abstraction covers every intended value: each EthLib value that fits
the declaration is the image of exactly one Go value. -/
theorem fixed_toValue_surjective (v : Value) (h : Value.fits fixedDesc v = true) :
    ∃ f : Fixed, f.toValue = v := by
  match v, h with
  | .seq [.uint n, .bytes d], h =>
    simp [fixedDesc, Value.fits, Value.fieldsFit] at h
    obtain ⟨hn, hd⟩ := h
    exact ⟨⟨UInt64.ofNat n, ⟨d, hd⟩⟩, by simp [Fixed.toValue, Nat.mod_eq_of_lt hn]⟩
  | .seq [], h | .seq [_], h | .seq (_ :: _ :: _ :: _), h => simp [fixedDesc, Value.fits, Value.fieldsFit] at h
  | .seq (.bool _ :: _ :: []), h | .seq (.bytes _ :: _ :: []), h | .seq (.bits _ :: _ :: []), h
  | .seq (.seq _ :: _ :: []), h | .seq (.union _ _ :: _ :: []), h => simp [fixedDesc, Value.fits, Value.fieldsFit] at h
  | .seq (.uint _ :: .bool _ :: []), h | .seq (.uint _ :: .uint _ :: []), h | .seq (.uint _ :: .bits _ :: []), h
  | .seq (.uint _ :: .seq _ :: []), h | .seq (.uint _ :: .union _ _ :: []), h => simp [fixedDesc, Value.fits, Value.fieldsFit] at h
  | .bool _, h | .uint _, h | .bytes _, h | .bits _, h | .union _ _, h => simp [fixedDesc, Value.fits] at h

theorem fixed_toValue_injective (f g : Fixed) (h : f.toValue = g.toValue) : f = g := by
  obtain ⟨a, b⟩ := f; obtain ⟨a', b'⟩ := g
  simp only [Fixed.toValue, Value.seq.injEq, List.cons.injEq, Value.uint.injEq, Value.bytes.injEq, and_true] at h
  obtain ⟨h1, h2⟩ := h
  have : a = a' := UInt64.toNat_inj.mp h1
  have : b = b' := Vector.toArray_inj.mp h2
  subst_vars; rfl

/-! ## Encoding -/

/-- The 40 bytes of an encoding, as a function of the Go value. -/
def fixedEncode (f : Fixed) : Array UInt8 := uintBytes 8 f.a.toNat ++ f.b.toArray

theorem uintBytes_size (w n : Nat) : (uintBytes w n).size = w := by
  induction w generalizing n with
  | zero => rfl
  | succ w ih => simp [uintBytes, ih]; omega

theorem fixed_encode_size (f : Fixed) : (fixedEncode f).size = 40 := by
  simp [fixedEncode, uintBytes_size]

theorem serialize_fixed (f : Fixed) : serialize fixedDesc f.toValue = .ok (fixedEncode f) := by
  unfold fixedEncode
  have ha := f.a.toNat_lt
  simp only [fixedDesc, Fixed.toValue, serialize, serializeStruct, serializeFields, ha, ite_true,
    bind, Except.bind, pure, Except.pure]
  simp only [bytesPerOffset, Nat.reduceMul, Nat.reducePow, Nat.reduceLeDiff, ite_false, ite_true,
    throw, throwThe, MonadExceptOf.throw, List.zip_cons_cons, List.zip_nil_right, headWidth, bodyWidth,
    headOf, bodiesOf, Vector.size_toArray, uintBytes_size]
  simp only [bne_self_eq_false, Bool.false_eq_true, ite_false, ge_iff_le, Nat.reduceLeDiff]
  have hfx : List.map Desc.isFixed [Desc.uint 8, Desc.byteVector 32] = [true, true] := rfl
  simp only [hfx, assemble, List.zip_cons_cons, List.zip_nil_right, headWidth, bodyWidth, headOf, bodiesOf,
    ite_true, uintBytes_size, Vector.size_toArray, bytesPerOffset, Nat.reduceMul, Nat.reducePow, Nat.reduceAdd,
    Nat.reduceLeDiff, ite_false, bind, Except.bind, pure, Except.pure]
  simp only [ge_iff_le, Nat.reduceLeDiff, ite_false, Array.append_empty]

/-! ## Decoding -/

/-- The Go value an accepted 40-byte input decodes to. -/
def fixedDecode (bs : Array UInt8) : Fixed where
  a := UInt64.ofNat (readUint bs 0 8)
  b := Vector.ofFn fun i => bs[8 + i.val]!

theorem readUint_lt (d : Array UInt8) (s w : Nat) : readUint d s w < 256 ^ w := by
  induction w generalizing s with
  | zero => simp [readUint]
  | succ w ih =>
    have := ih (s + 1); have : (d[s]?.getD 0).toNat < 256 := UInt8.toNat_lt _
    simp only [readUint, Nat.pow_succ]; omega
theorem readUint_congr (d d' : Array UInt8) (k w : Nat)
    (h : ∀ i, k ≤ i → i < k + w → d[i]? = d'[i]?) : readUint d k w = readUint d' k w := by
  induction w generalizing k with
  | zero => rfl
  | succ w ih =>
    simp only [readUint]
    rw [h k (by omega) (by omega), ih (k + 1) (fun i h1 h2 => h i (by omega) (by omega))]
theorem deserialize_fixed_ok (bs : Array UInt8) (h : bs.size = 40) :
    deserialize fixedDesc bs = .ok (fixedDecode bs).toValue := by
  rw [deserialize.eq_def]
  simp only [fixedDesc, deserializeStruct, structSlots, structBudget, structBodies, bodyStarts, readSlots,
    Desc.fieldsFixedSize, Desc.fixedSize, h]
  simp [bind, Except.bind, throw, throwThe, MonadExceptOf.throw, bytesPerOffset, readSlots, Desc.fixedSize, h,
    bodyStarts, Slot.held, deserializeFields, pure, Except.pure]
  rw [deserialize.eq_def, deserialize.eq_def]
  simp [h, bind, Except.bind, throw, throwThe, MonadExceptOf.throw, bytesPerOffset, pure, Except.pure,
    fixedDecode, Fixed.toValue]
  constructor
  · rw [Nat.mod_eq_of_lt (by simpa using readUint_lt bs 0 8)]
    apply readUint_congr; intro i _ hi; simp [Array.getElem?_extract, h]; omega
  · apply Array.ext
    · simp [h]
    · intro i h1 h2; simp at h1; simp [Array.getElem_extract, h]
      rw [getElem!_pos bs (8 + i) (by omega)]

theorem deserialize_fixed_err (bs : Array UInt8) (h : bs.size ≠ 40) :
    ∃ e, deserialize fixedDesc bs = .error e := by
  rw [deserialize.eq_def]
  simp only [fixedDesc, deserializeStruct, structSlots, structBudget]
  by_cases hb : bs.size ≥ 2 ^ (8 * bytesPerOffset)
  · simp [hb, bind, Except.bind, throw, throwThe, MonadExceptOf.throw]
  · simp [hb, h, Desc.fieldsFixedSize, Desc.fixedSize, bind, Except.bind, throw, throwThe, MonadExceptOf.throw]

/-! ## Error correspondence

The goal: success and rejection agree. The kind table below is the
intended mapping; only the `errSize` row occurs in the three functions. -/

inductive GoErr where
  /-- `ssz.ErrSize`, from UnmarshalSSZ on `len(buf) != 40`. -/
  | errSize
  /-- `ssz.ErrBytesLength`, from MarshalSSZTo when `len(c.B) != 32`. The
  check is on an array, so the compiler removed it (DISASM.md). -/
  | errBytesLength
  deriving DecidableEq, Repr

/-- Which EthLib refusals a Go error stands for. -/
def GoErr.matches : GoErr → Err → Prop
  | .errSize, .scope 40 _ => True
  -- EthLib checks the 4-byte offset bound before the size, so an input of
  -- 4 GiB or more is refused as an overflow, where Go says ErrSize.
  | .errSize, .offsetOverflow _ => True
  | .errBytesLength, .scope 32 _ => True
  | _, _ => False

/-- The refusal for a wrong length, and that `ssz.ErrSize` stands for it. -/
theorem deserialize_fixed_err_kind (bs : Array UInt8) (h : bs.size ≠ 40) :
    deserialize fixedDesc bs =
      .error (if bs.size ≥ 2 ^ 32 then .offsetOverflow bs.size else .scope 40 bs.size) := by
  rw [deserialize.eq_def]
  simp only [fixedDesc, deserializeStruct, structSlots, structBudget]
  by_cases hb : bs.size ≥ 2 ^ (8 * bytesPerOffset)
  · have : bs.size ≥ 2 ^ 32 := by simpa [bytesPerOffset] using hb
    simp [hb, this, bind, Except.bind, throw, throwThe, MonadExceptOf.throw]
  · have : ¬ bs.size ≥ 2 ^ 32 := by simpa [bytesPerOffset] using hb
    simp [hb, h, this, Desc.fieldsFixedSize, Desc.fixedSize, bind, Except.bind, throw, throwThe, MonadExceptOf.throw]
theorem deserialize_fixed_err_matches (bs : Array UInt8) (h : bs.size ≠ 40) :
    ∃ e, deserialize fixedDesc bs = .error e ∧ GoErr.errSize.matches e := by
  refine ⟨_, deserialize_fixed_err_kind bs h, ?_⟩
  split <;> simp [GoErr.matches]

/-! ## Nil-pointer rules

The machine-level nil rules are not stated in this file. In fv/kraken each
theorem names the memory chunks it reads and writes (separation logic over
Kraken's partial data memory), so a receiver without a chunk is outside its
precondition. -/

end Spec
