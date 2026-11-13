import Machine.Frame
import Machine.Block
import Prysm.SyncCommittee.SpecDefinitions

/-!
# List and memory-chunk lemmas of a `[][]byte` decoder loop

- `elementBlocks_snoc`, `sliceHeaders_length`, `sliceHeaders_snoc`: the two loop objects grow by one element.
- `flatten_length_of_length_48`, `flatten_split`: a flattened list of 48-byte blocks around block i.
- `zeroBytes`: `n` zero bytes.
- `jge_false_of_lt`: `cmp b, a; jge` is not taken when `a < b < 2^62`.
-/

open Machine Runtime

namespace Codec

abbrev zeroBytes (n : Nat) : List UInt8 := List.replicate n 0

theorem elementBlocks_snoc (ps : List (BitVec 64)) (es : List (List UInt8)) (p : BitVec 64) (e : List UInt8)
    (h : ps.length = es.length) :
    Codec.elementBlocks (ps ++ [p]) (es ++ [e]) = Codec.elementBlocks ps es ⋆ Eq (e.At p) := by
  induction ps generalizing es with
  | nil =>
    cases es with
    | nil => simp only [List.nil_append, Codec.elementBlocks, Std.ExtHashMap.emp_sep, Std.ExtHashMap.sep_emp]
    | cons _ _ => simp at h
  | cons q qs ih =>
    cases es with
    | nil => simp at h
    | cons f fs =>
      simp only [List.cons_append, Codec.elementBlocks]
      rw [ih fs (by simpa using h), Std.ExtHashMap.sep_assoc]

theorem sliceHeaders_length (w : Int) (ps : List (BitVec 64)) : (Codec.sliceHeaders w ps).length = 24 * ps.length := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp [Codec.sliceHeaders, Int.toBytes_length] at ih ⊢; omega

theorem sliceHeaders_snoc (w : Int) (ps : List (BitVec 64)) (p : BitVec 64) :
    Codec.sliceHeaders w (ps ++ [p]) = Codec.sliceHeaders w ps ++ (Int.toBytes 8 p.toInt ++ (Int.toBytes 8 w ++ Int.toBytes 8 w)) := by
  simp [Codec.sliceHeaders, List.append_assoc]

theorem flatten_length_of_length_48 (qs : List (List UInt8)) (h : ∀ e ∈ qs, e.length = 48) :
    qs.flatten.length = 48 * qs.length := by
  induction qs with
  | nil => rfl
  | cons q qs ih =>
    simp only [List.flatten_cons, List.length_append, List.length_cons]
    rw [h q (List.mem_cons_self), ih (fun e he => h e (List.mem_cons_of_mem _ he))]; omega

theorem flatten_split (pks : List (List UInt8)) (i : Nat) (hi : i < pks.length) :
    pks.flatten = (pks.take i).flatten ++ (pks[i] ++ (pks.drop (i + 1)).flatten) := by
  have e : pks = pks.take i ++ (pks[i] :: pks.drop (i + 1)) := by
    rw [← List.drop_eq_getElem_cons hi, List.take_append_drop]
  calc pks.flatten = (pks.take i ++ (pks[i] :: pks.drop (i + 1))).flatten := congrArg List.flatten e
    _ = _ := by rw [List.flatten_append, List.flatten_cons]

/-- `cmp b, a; jge` is not taken when `a < b < 2^62` (the text of `Machine.jge_false`, bound 2^62 instead of 16). -/
theorem jge_false_of_lt (a b : BitVec 64) (hb : b.toNat < 2 ^ 62) (hab : a.toNat < b.toNat)
    (h : (a - b).msb = ((a.toInt - b.toInt).bmod 18446744073709551616 != a.toInt - b.toInt)) : False := by
  have ta : a.toInt = a.toNat := BitVec.toInt_eq_toNat_of_lt (by omega)
  have tb : b.toInt = b.toNat := BitVec.toInt_eq_toNat_of_lt (by omega)
  rw [ta, tb] at h
  have hm : (((a.toNat : Int) - b.toNat).bmod 18446744073709551616) = (a.toNat : Int) - b.toNat := by
    apply Int.bmod_eq_of_le <;> omega
  rw [hm] at h
  simp only [bne_self_eq_false] at h
  have hs : (a - b).msb = true := by
    rw [BitVec.msb_eq_decide]; simp [BitVec.toNat_sub]; omega
  rw [hs] at h; exact Bool.noConfusion h

end Codec
