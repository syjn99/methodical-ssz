import Fk.Frame
import Fk.Block
import E2eList.ScLemmas

/-!
# List and memory-chunk lemmas for the HistoricalBatch element loops

Imported from the SyncCommittee proof as is (`E2eList.ScLemmas`): `lvElems_snoc`, `lvHdrs_length`, `lvHdrs_snoc`, `lv_flatten_split`,
`jge_false512` (its bound is 2^62, so it covers `cmp $0x2000`), `zz`.
New here: the SyncCommittee lemmas whose statements fix 48-byte blocks and 512 elements, with 32 and 8192.
Proof text: `E2eList.ScLemmas` with the two constants changed.
-/

open Fk E2eList

namespace E2eHb

theorem hb_flatten_length (qs : List (List UInt8)) (h : ∀ e ∈ qs, e.length = 32) :
    qs.flatten.length = 32 * qs.length := by
  induction qs with
  | nil => rfl
  | cons q qs ih =>
    simp only [List.flatten_cons, List.length_append, List.length_cons]
    rw [h q (List.mem_cons_self), ih (fun e he => h e (List.mem_cons_of_mem _ he))]; omega

theorem hbIn_split (bf : BitVec 64) (pks : List (List UInt8)) (hpks : pks.length = 8192)
    (hpk : ∀ e ∈ pks, e.length = 32) (i : Nat) (hi : i < 8192) :
    Eq (pks.flatten.At bf) = Eq ((pks.take i).flatten.At bf) ⋆ Eq (pks[i].At (bf + BitVec.ofNat 64 (32 * i)))
      ⋆ Eq ((pks.drop (i + 1)).flatten.At (bf + BitVec.ofNat 64 (32 * i) + 32)) := by
  have hlt : i < pks.length := by omega
  have ht : (pks.take i).flatten.length = 32 * i := by
    rw [hb_flatten_length _ (fun e he => hpk e (List.mem_of_mem_take he))]; simp; omega
  have hp : pks[i].length = 32 := hpk _ (List.getElem_mem hlt)
  have hd : (pks.drop (i + 1)).flatten.length = 32 * (8191 - i) := by
    rw [hb_flatten_length _ (fun e he => hpk e (List.mem_of_mem_drop he))]; simp; omega
  rw [lv_flatten_split pks i hlt,
    at_app _ _ (b := bf + BitVec.ofNat 64 (32 * i)) (by rw [ht]) (by simp only [List.length_append, ht, hp, hd]; omega),
    at_app _ _ (b := bf + BitVec.ofNat 64 (32 * i) + 32) (by rw [hp]; rfl) (by rw [hp, hd]; omega)]
  simp only [Std.ExtHashMap.sep_assoc]

theorem hbA_split (A : BitVec 64) (ps : List (BitVec 64)) (i : Nat) (hi : i < 8192) (hps : ps.length = i) :
    Eq ((lvHdrs 32 ps ++ zz (24 * (8192 - i))).At A) = Eq ((lvHdrs 32 ps).At A)
      ⋆ Eq ((zz 8).At (A + BitVec.ofNat 64 (24 * i))) ⋆ Eq ((zz 8).At (A + BitVec.ofNat 64 (24 * i) + 8))
      ⋆ Eq ((zz 8).At (A + BitVec.ofNat 64 (24 * i) + 16))
      ⋆ Eq ((zz (24 * (8192 - (i + 1)))).At (A + BitVec.ofNat 64 (24 * i) + 24)) := by
  have hl := lvHdrs_length 32 ps
  rw [show zz (24 * (8192 - i)) = zz 8 ++ (zz 8 ++ (zz 8 ++ zz (24 * (8192 - (i + 1))))) by
      simp only [zz, List.replicate_append_replicate]; congr 1; omega,
    at_app _ _ (b := A + BitVec.ofNat 64 (24 * i)) (by rw [hl, hps]) (by simp [hl, hps]; omega),
    at_app _ _ (b := A + BitVec.ofNat 64 (24 * i) + 8) (by simp) (by simp; omega),
    at_app _ _ (b := A + BitVec.ofNat 64 (24 * i) + 16) (by simp; bv_omega) (by simp; omega),
    at_app _ _ (b := A + BitVec.ofNat 64 (24 * i) + 24) (by simp; bv_omega) (by simp; omega)]
  simp only [Std.ExtHashMap.sep_assoc]

theorem hbA_join (A p : BitVec 64) (ps : List (BitVec 64)) (i : Nat) (hi : i < 8192) (hps : ps.length = i) :
    Eq ((lvHdrs 32 (ps ++ [p]) ++ zz (24 * (8192 - (i + 1)))).At A) = Eq ((lvHdrs 32 ps).At A)
      ⋆ Eq ((Int.toBytes 8 p.toInt).At (A + BitVec.ofNat 64 (24 * i)))
      ⋆ Eq ((Int.toBytes 8 32).At (A + BitVec.ofNat 64 (24 * i) + 8))
      ⋆ Eq ((Int.toBytes 8 32).At (A + BitVec.ofNat 64 (24 * i) + 16))
      ⋆ Eq ((zz (24 * (8192 - (i + 1)))).At (A + BitVec.ofNat 64 (24 * i) + 24)) := by
  have hl := lvHdrs_length 32 ps
  rw [lvHdrs_snoc, List.append_assoc, List.append_assoc, List.append_assoc,
    at_app _ _ (b := A + BitVec.ofNat 64 (24 * i)) (by rw [hl, hps])
      (by simp [hl, hps, Int.toBytes_length]; omega),
    at_app _ _ (b := A + BitVec.ofNat 64 (24 * i) + 8) (by simp [Int.toBytes_length])
      (by simp [Int.toBytes_length]; omega),
    at_app _ _ (b := A + BitVec.ofNat 64 (24 * i) + 16) (by simp [Int.toBytes_length]; bv_omega)
      (by simp [Int.toBytes_length]; omega),
    at_app _ _ (b := A + BitVec.ofNat 64 (24 * i) + 24) (by simp [Int.toBytes_length]; bv_omega)
      (by simp [Int.toBytes_length]; omega)]
  simp only [Std.ExtHashMap.sep_assoc]

end E2eHb
