import Fk.Bump
import Fk.BumpMore
import Fk.FunSpecs
import E2eList.DataIa
import E2eAd.Data

/-!
# Type-dispatching bump models of `runtime.makeslice` and `runtime.newobject` for the IndexedAttestation witness host

The IndexedAttestation accept path needs four `MakesliceC` instances (esz 8 for `lvU64Type_addr`, esz 1 for the uint8 type word, at
three stack sizes) and two `NewobjectC` instances (96 bytes for `lvAdType_addr`, 72 for `adCpType_addr`). A Host has
one `runtime.makeslice` and one `runtime.newobject`, so each model dispatches on the type word in rax:
`E2eList/BumpAllocT3.S` bumps by 8·cnt for `type__+387456` and by cnt otherwise; `E2eList/BumpNewT3.S` bumps by 96
for `type__+1464512` and by 72 otherwise. The offsets are those of `lv/link-t3/data/lvU64Type.data` and
`lvAdType.data`. The proof texts are `E2eList.bump_makeslice_t1` / `t24` (`BumpT.lean`) and `E2eAd.bump_newobject72`
with the dispatch steps. Abstract models for non-vacuity only, not a Go refinement. Both `.S`
files are in the Lake `input_dir` `lv_lean_S` (all `.S` files of `E2eList/`).
-/

open Fk

namespace E2eList

def BumpAllocT3 : Program := include_x64_rt "E2eList/BumpAllocT3.S"
def BumpNewT3 : Program := include_x64_rt "E2eList/BumpNewT3.S"

variable [Host]

/-- The esz-1 branch: any type word other than `lvU64Type_addr`. -/
theorem bump_makeslice_t3_1 (j : Nat) (hj : BumpAllocT3.IsInfixAt Host.prog j)
    (hf : ∀ i < j, Host.prog[i]? ≠ some (.label "runtime.makeslice")) (ty : BitVec 64)
    (hne : ty ≠ E2eList.Data.lvU64Type_addr) {S : Nat} :
    MakesliceC bumpHeap ty 1 S := by
  intro st ret cnt avail stk spill F _hty _hrbx hrcx hav _hmax _hcnt hstk hsp hm
  have hL := label_in_fragment hj (j := 0) (by decide) (by decide) hf
  rw [hL]
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := st
  simp only at hrcx hm ⊢
  have hm' : (bumpHeap avail ⋆ (Eq ((Int.toBytes 8 ret.toBitVec.toInt).At rsp.toBitVec)
      ⋆ Eq (stk.At (rsp.toBitVec - BitVec.ofNat 64 S)) ⋆ Eq (spill.At (rsp.toBitVec + 8)) ⋆ F)) mem := by ecancel
  obtain ⟨p, hp⟩ := sep_exists_left (Q := fun (p : BitVec 64) (m : DataMem) => p.toNat + avail < 2 ^ 64 ∧
    (Eq ((Int.toBytes 8 p.toInt).At (label "runtime.fvBump").toBitVec) ⋆ Eq ((List.replicate avail 0).At p)) m) hm'
  obtain ⟨hpa, hp⟩ := sep_pure_left hp
  kat hj BumpAllocT3 0
  kat hj BumpAllocT3 1
  kat hj BumpAllocT3 2
  kat hj BumpAllocT3 3
  split
  case isTrue h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
    simp only at _hty
    apply hne; rw [← _hty]
    simp only [E2eList.Data.lvU64Type_addr, Int64.toBitVec_add, Int64.toBitVec_ofNat]
    have h2 := congrArg (· + ((label "type__").toBitVec + 387456#64)) h
    simp only [BitVec.sub_add_cancel, BitVec.zero_add] at h2
    exact h2
  simp only [Effects.All]
  kat hj BumpAllocT3 4
  apply load_step _ _ _ _ (Int.toBytes 8 p.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hj BumpAllocT3 5
  kat hj BumpAllocT3 6
  apply store_step _ _ _ _ _ (Int.toBytes 8 p.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  intro m1 H1
  simp only [Width.bytes, Width.bits] at H1
  kunfold
  kat hj BumpAllocT3 7
  kat hj BumpAllocT3 8
  apply load_step _ _ _ _ (Int.toBytes 8 ret.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  apply Eventually.done
  have hq : (p + rcx.toBitVec * 1#64).toNat = p.toNat + 1 * cnt := by
    simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, UInt64.toNat_toBitVec]; omega
  have hq' : p + BitVec.ofNat 64 (1 * cnt) = p + rcx.toBitVec * 1#64 := by
    apply BitVec.eq_of_toNat_eq; rw [hq]; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hsplit : List.replicate avail (0 : UInt8) = List.replicate (1 * cnt) 0 ++ List.replicate (avail - 1 * cnt) 0 := by
    rw [List.replicate_append_replicate]; congr 1; omega
  rw [hsplit, Mem.At_append_sep _ _ _ (by simp; omega)] at H1
  simp only [List.length_replicate, hq'] at H1
  have H2 : ((Eq ((Int.toBytes 8 (p + rcx.toBitVec * 1#64).toInt).At (label "runtime.fvBump").toBitVec)
      ⋆ Eq ((List.replicate (avail - 1 * cnt) 0).At (p + rcx.toBitVec * 1#64)))
      ⋆ (Eq ((Int.toBytes 8 ret.toBitVec.toInt).At rsp.toBitVec) ⋆ Eq (stk.At (rsp.toBitVec - BitVec.ofNat 64 S))
        ⋆ Eq (spill.At (rsp.toBitVec + 8)) ⋆ Eq ((List.replicate (1 * cnt) 0).At p) ⋆ F)) m1 := by ecancel
  have H3 := sep_mono_left (P' := bumpHeap (avail - 1 * cnt))
    (fun m hm => ⟨p + rcx.toBitVec * 1#64, by omega, hm⟩) H2
  refine ⟨by simp, ?_, rfl, rfl, stk, spill, hstk, hsp, ?_⟩
  · apply UInt64.toBitVec_inj.mp; simp
  · dsimp only; ecancel

/-- The esz-8 branch: the type word `lvU64Type_addr`. -/
theorem bump_makeslice_t3_8 (j : Nat) (hj : BumpAllocT3.IsInfixAt Host.prog j)
    (hf : ∀ i < j, Host.prog[i]? ≠ some (.label "runtime.makeslice")) (hfl : LabelsFresh BumpAllocT3 j) {S : Nat} :
    MakesliceC bumpHeap E2eList.Data.lvU64Type_addr 8 S := by
  intro st ret cnt avail stk spill F _hty _hrbx hrcx hav _hmax _hcnt hstk hsp hm
  have hL := label_in_fragment hj (j := 0) (by decide) (by decide) hf
  rw [hL]
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := st
  simp only at hrcx hm ⊢
  have hm' : (bumpHeap avail ⋆ (Eq ((Int.toBytes 8 ret.toBitVec.toInt).At rsp.toBitVec)
      ⋆ Eq (stk.At (rsp.toBitVec - BitVec.ofNat 64 S)) ⋆ Eq (spill.At (rsp.toBitVec + 8)) ⋆ F)) mem := by ecancel
  obtain ⟨p, hp⟩ := sep_exists_left (Q := fun (p : BitVec 64) (m : DataMem) => p.toNat + avail < 2 ^ 64 ∧
    (Eq ((Int.toBytes 8 p.toInt).At (label "runtime.fvBump").toBitVec) ⋆ Eq ((List.replicate avail 0).At p)) m) hm'
  obtain ⟨hpa, hp⟩ := sep_pure_left hp
  kat hj BumpAllocT3 0
  kat hj BumpAllocT3 1
  kat hj BumpAllocT3 2
  kat hj BumpAllocT3 3
  split
  case isFalse h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
    simp only at _hty
    apply h; rw [_hty]
    simp only [E2eList.Data.lvU64Type_addr, Int64.toBitVec_add, Int64.toBitVec_ofNat]
    exact BitVec.sub_self _
  simp only [Effects.All]
  klabel hj hfl BumpAllocT3 9
  kat hj BumpAllocT3 9
  kat hj BumpAllocT3 10
  apply load_step _ _ _ _ (Int.toBytes 8 p.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hj BumpAllocT3 11
  kat hj BumpAllocT3 12
  apply store_step _ _ _ _ _ (Int.toBytes 8 p.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  intro m1 H1
  simp only [Width.bytes, Width.bits] at H1
  kunfold
  kat hj BumpAllocT3 13
  kat hj BumpAllocT3 14
  apply load_step _ _ _ _ (Int.toBytes 8 ret.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  apply Eventually.done
  have hq : (p + rcx.toBitVec * 8#64).toNat = p.toNat + 8 * cnt := by
    simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, UInt64.toNat_toBitVec]; omega
  have hq' : p + BitVec.ofNat 64 (8 * cnt) = p + rcx.toBitVec * 8#64 := by
    apply BitVec.eq_of_toNat_eq; rw [hq]; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hsplit : List.replicate avail (0 : UInt8) = List.replicate (8 * cnt) 0 ++ List.replicate (avail - 8 * cnt) 0 := by
    rw [List.replicate_append_replicate]; congr 1; omega
  rw [hsplit, Mem.At_append_sep _ _ _ (by simp; omega)] at H1
  simp only [List.length_replicate, hq'] at H1
  have H2 : ((Eq ((Int.toBytes 8 (p + rcx.toBitVec * 8#64).toInt).At (label "runtime.fvBump").toBitVec)
      ⋆ Eq ((List.replicate (avail - 8 * cnt) 0).At (p + rcx.toBitVec * 8#64)))
      ⋆ (Eq ((Int.toBytes 8 ret.toBitVec.toInt).At rsp.toBitVec) ⋆ Eq (stk.At (rsp.toBitVec - BitVec.ofNat 64 S))
        ⋆ Eq (spill.At (rsp.toBitVec + 8)) ⋆ Eq ((List.replicate (8 * cnt) 0).At p) ⋆ F)) m1 := by ecancel
  have H3 := sep_mono_left (P' := bumpHeap (avail - 8 * cnt))
    (fun m hm => ⟨p + rcx.toBitVec * 8#64, by omega, hm⟩) H2
  refine ⟨by simp, ?_, rfl, rfl, stk, spill, hstk, hsp, ?_⟩
  · apply UInt64.toBitVec_inj.mp; simp
  · dsimp only; ecancel

/-- The 72-byte branch: any type word other than `lvAdType_addr`. -/
theorem bump_newobject_t3_72 (j : Nat) (hj : BumpNewT3.IsInfixAt Host.prog j)
    (hf : ∀ i < j, Host.prog[i]? ≠ some (.label "runtime.newobject")) (ty : BitVec 64)
    (hne : ty ≠ E2eList.Data.lvAdType_addr) {S : Nat} :
    NewobjectC bumpHeap ty 72 S := by
  intro st ret avail stk spill F _hty hav hstk hsp hm
  have hL := label_in_fragment hj (j := 0) (by decide) (by decide) hf
  rw [hL]
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := st
  simp only at hm ⊢
  have hm' : (bumpHeap avail ⋆ (Eq ((Int.toBytes 8 ret.toBitVec.toInt).At rsp.toBitVec)
      ⋆ Eq (stk.At (rsp.toBitVec - BitVec.ofNat 64 S)) ⋆ Eq (spill.At (rsp.toBitVec + 8)) ⋆ F)) mem := by ecancel
  obtain ⟨p, hp⟩ := sep_exists_left (Q := fun (p : BitVec 64) (m : DataMem) => p.toNat + avail < 2 ^ 64 ∧
    (Eq ((Int.toBytes 8 p.toInt).At (label "runtime.fvBump").toBitVec) ⋆ Eq ((List.replicate avail 0).At p)) m) hm'
  obtain ⟨hpa, hp⟩ := sep_pure_left hp
  have hk := hj
  simp only [BumpNewT3] at hk
  kat hj BumpNewT3 0
  kat hj BumpNewT3 1
  kat hj BumpNewT3 2
  kat hj BumpNewT3 3
  split
  case isTrue h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
    simp only at _hty
    apply hne; rw [← _hty]
    simp only [E2eList.Data.lvAdType_addr, Int64.toBitVec_add, Int64.toBitVec_ofNat]
    have h2 := congrArg (· + ((label "type__").toBitVec + 1464512#64)) h
    simp only [BitVec.sub_add_cancel, BitVec.zero_add] at h2
    exact h2
  simp only [Effects.All]
  kat hj BumpNewT3 4
  apply load_step _ _ _ _ (Int.toBytes 8 p.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hj BumpNewT3 5
  kat hj BumpNewT3 6
  apply store_step _ _ _ _ _ (Int.toBytes 8 p.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  intro m1 H1
  simp only [Width.bytes, Width.bits] at H1
  kunfold
  kat hj BumpNewT3 7
  kat hj BumpNewT3 8
  apply load_step _ _ _ _ (Int.toBytes 8 ret.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  apply Eventually.done
  have h72 : (72 : BitVec 64).toNat = 72 := rfl
  have hq : (p + (72 : BitVec 64)).toNat = p.toNat + 72 := by
    simp only [BitVec.toNat_add, h72]; omega
  have hq' : p + BitVec.ofNat 64 (72) = p + (72 : BitVec 64) := rfl
  have hsplit : List.replicate avail (0 : UInt8) = List.replicate (72) 0 ++ List.replicate (avail - 72) 0 := by
    rw [List.replicate_append_replicate]; congr 1; omega
  rw [hsplit, Mem.At_append_sep _ _ _ (by simp; omega)] at H1
  simp only [List.length_replicate, hq'] at H1
  have H2 : ((Eq ((Int.toBytes 8 (p + (72 : BitVec 64)).toInt).At (label "runtime.fvBump").toBitVec)
      ⋆ Eq ((List.replicate (avail - 72) 0).At (p + (72 : BitVec 64))))
      ⋆ (Eq ((Int.toBytes 8 ret.toBitVec.toInt).At rsp.toBitVec) ⋆ Eq (stk.At (rsp.toBitVec - BitVec.ofNat 64 S))
        ⋆ Eq (spill.At (rsp.toBitVec + 8)) ⋆ Eq ((List.replicate (72) 0).At p) ⋆ F)) m1 := by ecancel
  have H3 := sep_mono_left (P' := bumpHeap (avail - 72))
    (fun m hm => ⟨p + (72 : BitVec 64), by omega, hm⟩) H2
  refine ⟨by simp, ?_, rfl, rfl, stk, spill, hstk, hsp, ?_⟩
  · apply UInt64.toBitVec_inj.mp; simp
  · dsimp only; ecancel
/-- The 96-byte branch: the type word `lvAdType_addr`. -/
theorem bump_newobject_t3_96 (j : Nat) (hj : BumpNewT3.IsInfixAt Host.prog j)
    (hf : ∀ i < j, Host.prog[i]? ≠ some (.label "runtime.newobject")) (hfl : LabelsFresh BumpNewT3 j) {S : Nat} :
    NewobjectC bumpHeap E2eList.Data.lvAdType_addr 96 S := by
  intro st ret avail stk spill F _hty hav hstk hsp hm
  have hL := label_in_fragment hj (j := 0) (by decide) (by decide) hf
  rw [hL]
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := st
  simp only at hm ⊢
  have hm' : (bumpHeap avail ⋆ (Eq ((Int.toBytes 8 ret.toBitVec.toInt).At rsp.toBitVec)
      ⋆ Eq (stk.At (rsp.toBitVec - BitVec.ofNat 64 S)) ⋆ Eq (spill.At (rsp.toBitVec + 8)) ⋆ F)) mem := by ecancel
  obtain ⟨p, hp⟩ := sep_exists_left (Q := fun (p : BitVec 64) (m : DataMem) => p.toNat + avail < 2 ^ 64 ∧
    (Eq ((Int.toBytes 8 p.toInt).At (label "runtime.fvBump").toBitVec) ⋆ Eq ((List.replicate avail 0).At p)) m) hm'
  obtain ⟨hpa, hp⟩ := sep_pure_left hp
  have hk := hj
  simp only [BumpNewT3] at hk
  kat hj BumpNewT3 0
  kat hj BumpNewT3 1
  kat hj BumpNewT3 2
  kat hj BumpNewT3 3
  split
  case isFalse h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
    simp only at _hty
    apply h; rw [_hty]
    simp only [E2eList.Data.lvAdType_addr, Int64.toBitVec_add, Int64.toBitVec_ofNat]
    exact BitVec.sub_self _
  simp only [Effects.All]
  klabel hj hfl BumpNewT3 9
  kat hj BumpNewT3 9
  kat hj BumpNewT3 10
  apply load_step _ _ _ _ (Int.toBytes 8 p.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hj BumpNewT3 11
  kat hj BumpNewT3 12
  apply store_step _ _ _ _ _ (Int.toBytes 8 p.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  intro m1 H1
  simp only [Width.bytes, Width.bits] at H1
  kunfold
  kat hj BumpNewT3 13
  kat hj BumpNewT3 14
  apply load_step _ _ _ _ (Int.toBytes 8 ret.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  apply Eventually.done
  have h96 : (96 : BitVec 64).toNat = 96 := rfl
  have hq : (p + (96 : BitVec 64)).toNat = p.toNat + 96 := by
    simp only [BitVec.toNat_add, h96]; omega
  have hq' : p + BitVec.ofNat 64 (96) = p + (96 : BitVec 64) := rfl
  have hsplit : List.replicate avail (0 : UInt8) = List.replicate (96) 0 ++ List.replicate (avail - 96) 0 := by
    rw [List.replicate_append_replicate]; congr 1; omega
  rw [hsplit, Mem.At_append_sep _ _ _ (by simp; omega)] at H1
  simp only [List.length_replicate, hq'] at H1
  have H2 : ((Eq ((Int.toBytes 8 (p + (96 : BitVec 64)).toInt).At (label "runtime.fvBump").toBitVec)
      ⋆ Eq ((List.replicate (avail - 96) 0).At (p + (96 : BitVec 64))))
      ⋆ (Eq ((Int.toBytes 8 ret.toBitVec.toInt).At rsp.toBitVec) ⋆ Eq (stk.At (rsp.toBitVec - BitVec.ofNat 64 S))
        ⋆ Eq (spill.At (rsp.toBitVec + 8)) ⋆ Eq ((List.replicate (96) 0).At p) ⋆ F)) m1 := by ecancel
  have H3 := sep_mono_left (P' := bumpHeap (avail - 96))
    (fun m hm => ⟨p + (96 : BitVec 64), by omega, hm⟩) H2
  refine ⟨by simp, ?_, rfl, rfl, stk, spill, hstk, hsp, ?_⟩
  · apply UInt64.toBitVec_inj.mp; simp
  · dsimp only; ecancel
end E2eList
