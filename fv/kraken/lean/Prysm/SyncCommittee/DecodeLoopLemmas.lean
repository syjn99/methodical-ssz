import Machine.Frame
import Machine.Block
import Prysm.SyncCommittee.SpecDefinitions
import Codec.ByteSliceListLemmas

/-!
# List and memory-chunk lemmas for the SyncCommittee element loop

- `Decode.input_split`: the input chunk as (blocks < i) ⋆ block i ⋆ (blocks > i).
- `Decode.array_split`, `Decode.array_join`: the backing array (headers of the first i elements, then zeros) around element i,
  before (three zero words) and after (the header `(p, 48, 48)`) the three stores of iteration i.

The lemmas of these proofs that do not depend on the type are in `Codec/ByteSliceListLemmas.lean`:
`Codec.elementBlocks_snoc`, `Codec.sliceHeaders_length`, `Codec.sliceHeaders_snoc`, `Codec.flatten_length_of_length_48`,
`Codec.flatten_split`, `Codec.zeroBytes` and `Codec.jge_false_of_lt`.
-/

open Machine Runtime

namespace Prysm.SyncCommittee

theorem Decode.input_split (bf : BitVec 64) (pks : List (List UInt8)) (hpks : pks.length = 512)
    (hpk : ∀ e ∈ pks, e.length = 48) (i : Nat) (hi : i < 512) :
    Eq (pks.flatten.At bf) = Eq ((pks.take i).flatten.At bf) ⋆ Eq (pks[i].At (bf + BitVec.ofNat 64 (48 * i)))
      ⋆ Eq ((pks.drop (i + 1)).flatten.At (bf + BitVec.ofNat 64 (48 * i) + 48)) := by
  have hlt : i < pks.length := by omega
  have ht : (pks.take i).flatten.length = 48 * i := by
    rw [Codec.flatten_length_of_length_48 _ (fun e he => hpk e (List.mem_of_mem_take he))]; simp; omega
  have hp : pks[i].length = 48 := hpk _ (List.getElem_mem hlt)
  have hd : (pks.drop (i + 1)).flatten.length = 48 * (511 - i) := by
    rw [Codec.flatten_length_of_length_48 _ (fun e he => hpk e (List.mem_of_mem_drop he))]; simp; omega
  rw [Codec.flatten_split pks i hlt,
    at_app _ _ (b := bf + BitVec.ofNat 64 (48 * i)) (by rw [ht]) (by simp only [List.length_append, ht, hp, hd]; omega),
    at_app _ _ (b := bf + BitVec.ofNat 64 (48 * i) + 48) (by rw [hp]; rfl) (by rw [hp, hd]; omega)]
  simp only [Std.ExtHashMap.sep_assoc]

theorem Decode.array_split (A : BitVec 64) (ps : List (BitVec 64)) (i : Nat) (hi : i < 512) (hps : ps.length = i) :
    Eq ((Codec.sliceHeaders 48 ps ++ Codec.zeroBytes (24 * (512 - i))).At A) = Eq ((Codec.sliceHeaders 48 ps).At A)
      ⋆ Eq ((Codec.zeroBytes 8).At (A + BitVec.ofNat 64 (24 * i))) ⋆ Eq ((Codec.zeroBytes 8).At (A + BitVec.ofNat 64 (24 * i) + 8))
      ⋆ Eq ((Codec.zeroBytes 8).At (A + BitVec.ofNat 64 (24 * i) + 16))
      ⋆ Eq ((Codec.zeroBytes (24 * (512 - (i + 1)))).At (A + BitVec.ofNat 64 (24 * i) + 24)) := by
  have hl := Codec.sliceHeaders_length 48 ps
  rw [show Codec.zeroBytes (24 * (512 - i)) = Codec.zeroBytes 8 ++ (Codec.zeroBytes 8 ++ (Codec.zeroBytes 8 ++ Codec.zeroBytes (24 * (512 - (i + 1))))) by
      simp only [Codec.zeroBytes, List.replicate_append_replicate]; congr 1; omega,
    at_app _ _ (b := A + BitVec.ofNat 64 (24 * i)) (by rw [hl, hps]) (by simp [hl, hps]; omega),
    at_app _ _ (b := A + BitVec.ofNat 64 (24 * i) + 8) (by simp) (by simp; omega),
    at_app _ _ (b := A + BitVec.ofNat 64 (24 * i) + 16) (by simp; bv_omega) (by simp; omega),
    at_app _ _ (b := A + BitVec.ofNat 64 (24 * i) + 24) (by simp; bv_omega) (by simp; omega)]
  simp only [Std.ExtHashMap.sep_assoc]

theorem Decode.array_join (A p : BitVec 64) (ps : List (BitVec 64)) (i : Nat) (hi : i < 512) (hps : ps.length = i) :
    Eq ((Codec.sliceHeaders 48 (ps ++ [p]) ++ Codec.zeroBytes (24 * (512 - (i + 1)))).At A) = Eq ((Codec.sliceHeaders 48 ps).At A)
      ⋆ Eq ((Int.toBytes 8 p.toInt).At (A + BitVec.ofNat 64 (24 * i)))
      ⋆ Eq ((Int.toBytes 8 48).At (A + BitVec.ofNat 64 (24 * i) + 8))
      ⋆ Eq ((Int.toBytes 8 48).At (A + BitVec.ofNat 64 (24 * i) + 16))
      ⋆ Eq ((Codec.zeroBytes (24 * (512 - (i + 1)))).At (A + BitVec.ofNat 64 (24 * i) + 24)) := by
  have hl := Codec.sliceHeaders_length 48 ps
  rw [Codec.sliceHeaders_snoc, List.append_assoc, List.append_assoc, List.append_assoc,
    at_app _ _ (b := A + BitVec.ofNat 64 (24 * i)) (by rw [hl, hps])
      (by simp [hl, hps, Int.toBytes_length]; omega),
    at_app _ _ (b := A + BitVec.ofNat 64 (24 * i) + 8) (by simp [Int.toBytes_length])
      (by simp [Int.toBytes_length]; omega),
    at_app _ _ (b := A + BitVec.ofNat 64 (24 * i) + 16) (by simp [Int.toBytes_length]; bv_omega)
      (by simp [Int.toBytes_length]; omega),
    at_app _ _ (b := A + BitVec.ofNat 64 (24 * i) + 24) (by simp [Int.toBytes_length]; bv_omega)
      (by simp [Int.toBytes_length]; omega)]
  simp only [Std.ExtHashMap.sep_assoc]

end Prysm.SyncCommittee
