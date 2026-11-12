import E2eHb.HbSpec

/-!
# Spec lemmas of a `Vector[Bytes32, n]` field, for ANY count `n` (generalized once)

`E2eHb.HbSpec` states `v32_flatten_length`, `v32_serialize`, `v32_of_bytes` for n = 8192. Here n is a variable;
the side condition is that the field fits an SSZ offset (`32 * n < 2^32`). Proof text: `HbSpec` with 8192 → n.
The element lemmas (`toV32`, `allFit_bv32`, `serializeEach_bv32`, `concatParts_v32`) are imported.
-/

namespace Codec.Segment
open EthLib.Serialization.Ssz Spec TestTarget E2eList E2eHb

theorem vN_flatten_length (n : Nat) (v : Vector (Vector UInt8 32) n) :
    (v.toList.map (·.toList)).flatten.length = 32 * n := by
  have h := concatParts_v32_size v.toList
  rw [concatParts_v32] at h
  simpa using h

/-- One `Vector[Bytes32, n]` field serializes to its elements laid end to end. -/
theorem vN_serialize (n : Nat) (hn : 32 * n < 2 ^ 32) (v : Vector (Vector UInt8 32) n) :
    serialize (.vector (.byteVector 32) n) (.seq (v.toList.map fun p => .bytes p.toArray))
      = .ok (v.toList.map (·.toList)).flatten.toArray := by
  have hs := concatParts_v32_size v.toList
  simp only [serialize, List.length_map, Vector.length_toList, beq_self_eq_true, ↓reduceIte, serializeSequence,
    serializeEach_bv32, bind, Except.bind]
  rw [show (v.toList.map (·.toArray)).map (fun _ => Desc.isFixed (.byteVector 32))
      = (v.toList.map (·.toArray)).map (fun _ => true) from rfl,
    assemble_inline_ok _ (by rw [hs]; simp; omega), concatParts_v32]

/-- Every `32 n`-byte array is the end-to-end layout of some `Vector[Bytes32, n]`. -/
theorem vN_of_bytes (n : Nat) (d : Array UInt8) (hd : d.size = 32 * n) :
    ∃ v : Vector (Vector UInt8 32) n, (v.toList.map (·.toList)).flatten.toArray = d := by
  let chunks : List (Vector UInt8 32) := (List.range n).map fun i =>
    toV32 (.bytes (d.extract (i * 32) ((i + 1) * 32)))
  refine ⟨⟨chunks.toArray, by simp [chunks]⟩, ?_⟩
  have hm : chunks.map (·.toArray) = (List.range n).map (fun i => d.extract (i * 32) ((i + 1) * 32)) := by
    simp only [chunks, List.map_map]
    apply List.map_congr_left
    intro i hi
    simp only [List.mem_range] at hi
    have hsz : (d.extract (i * 32) ((i + 1) * 32)).size = 32 := by
      simp; rw [Nat.min_eq_left (by rw [hd]; have := Nat.mul_le_mul_left 32 (show i + 1 ≤ n by omega); omega)]; omega
    show (toV32 (.bytes (d.extract (i * 32) ((i + 1) * 32)))).toArray = _
    simp only [toV32]
    rw [dif_pos hsz]
  rw [← concatParts_v32]
  have := concat_fixed_slices d 32 n (by omega)
  simp only [Vector.toList_mk, List.toList_toArray]
  rw [hm, this, show n * 32 = d.size by omega]
  simp

/-- The 8192 instances of `HbSpec` follow by `exact`. -/
example : type_of% @E2eHb.v32_serialize := vN_serialize 8192 (by decide)
example : type_of% @E2eHb.v32_flatten_length := vN_flatten_length 8192
example : type_of% @E2eHb.v32_of_bytes := vN_of_bytes 8192

end Codec.Segment
