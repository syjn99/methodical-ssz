import Fk.Bump
import Fk.FunSpecs

/-!
# More bump-allocator models

`bump_makeslice1`: `runtime.makeslice` for 1-byte elements (`BumpAlloc1`).
`bump_newobject24`, `bump_newobject32`: `runtime.newobject` for one object of
24 or 32 bytes (`BumpNew24`, `BumpNew32`). All on `bumpHeap` (Fk/Bump.lean).
-/

open Fk

namespace Fk
def BumpAlloc1 : Program := include_x64_rt "Fk/BumpAlloc1.S"
def BumpNew24 : Program := include_x64_rt "Fk/BumpNew24.S"
def BumpNew16 : Program := include_x64_rt "Fk/BumpNew16.S"
def BumpNew32 : Program := include_x64_rt "Fk/BumpNew32.S"

variable [Host]

set_option maxHeartbeats 4000000 in
theorem bump_makeslice1 (j : Nat) (hj : BumpAlloc1.IsInfixAt Host.prog j)
    (hf : ∀ i < j, Host.prog[i]? ≠ some (.label "runtime.makeslice")) (ty : BitVec 64) {S : Nat} :
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
  have hk := hj
  simp only [BumpAlloc1] at hk
  kat hj BumpAlloc1 0
  kat hj BumpAlloc1 1
  apply load_step _ _ _ _ (Int.toBytes 8 p.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hj BumpAlloc1 2
  kat hj BumpAlloc1 3
  apply store_step _ _ _ _ _ (Int.toBytes 8 p.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  intro m1 H1
  simp only [Width.bytes, Width.bits] at H1
  kunfold
  kat hj BumpAlloc1 4
  kat hj BumpAlloc1 5
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
set_option maxHeartbeats 4000000 in
theorem bump_newobject24 (j : Nat) (hj : BumpNew24.IsInfixAt Host.prog j)
    (hf : ∀ i < j, Host.prog[i]? ≠ some (.label "runtime.newobject")) (ty : BitVec 64) {S : Nat} :
    NewobjectC bumpHeap ty 24 S := by
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
  simp only [BumpNew24] at hk
  kat hj BumpNew24 0
  kat hj BumpNew24 1
  apply load_step _ _ _ _ (Int.toBytes 8 p.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hj BumpNew24 2
  kat hj BumpNew24 3
  apply store_step _ _ _ _ _ (Int.toBytes 8 p.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  intro m1 H1
  simp only [Width.bytes, Width.bits] at H1
  kunfold
  kat hj BumpNew24 4
  kat hj BumpNew24 5
  apply load_step _ _ _ _ (Int.toBytes 8 ret.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  apply Eventually.done
  have h24 : (24 : BitVec 64).toNat = 24 := rfl
  have hq : (p + (24 : BitVec 64)).toNat = p.toNat + 24 := by
    simp only [BitVec.toNat_add, h24]; omega
  have hq' : p + BitVec.ofNat 64 (24) = p + (24 : BitVec 64) := rfl
  have hsplit : List.replicate avail (0 : UInt8) = List.replicate (24) 0 ++ List.replicate (avail - 24) 0 := by
    rw [List.replicate_append_replicate]; congr 1; omega
  rw [hsplit, Mem.At_append_sep _ _ _ (by simp; omega)] at H1
  simp only [List.length_replicate, hq'] at H1
  have H2 : ((Eq ((Int.toBytes 8 (p + (24 : BitVec 64)).toInt).At (label "runtime.fvBump").toBitVec)
      ⋆ Eq ((List.replicate (avail - 24) 0).At (p + (24 : BitVec 64))))
      ⋆ (Eq ((Int.toBytes 8 ret.toBitVec.toInt).At rsp.toBitVec) ⋆ Eq (stk.At (rsp.toBitVec - BitVec.ofNat 64 S))
        ⋆ Eq (spill.At (rsp.toBitVec + 8)) ⋆ Eq ((List.replicate (24) 0).At p) ⋆ F)) m1 := by ecancel
  have H3 := sep_mono_left (P' := bumpHeap (avail - 24))
    (fun m hm => ⟨p + (24 : BitVec 64), by omega, hm⟩) H2
  refine ⟨by simp, ?_, rfl, rfl, stk, spill, hstk, hsp, ?_⟩
  · apply UInt64.toBitVec_inj.mp; simp
  · dsimp only; ecancel
set_option maxHeartbeats 4000000 in
/-- The 16-byte bump `runtime.newobject`. -/
theorem bump_newobject16 (j : Nat) (hj : BumpNew16.IsInfixAt Host.prog j)
    (hf : ∀ i < j, Host.prog[i]? ≠ some (.label "runtime.newobject")) (ty : BitVec 64) {S : Nat} :
    NewobjectC bumpHeap ty 16 S := by
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
  simp only [BumpNew16] at hk
  kat hj BumpNew16 0
  kat hj BumpNew16 1
  apply load_step _ _ _ _ (Int.toBytes 8 p.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hj BumpNew16 2
  kat hj BumpNew16 3
  apply store_step _ _ _ _ _ (Int.toBytes 8 p.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  intro m1 H1
  simp only [Width.bytes, Width.bits] at H1
  kunfold
  kat hj BumpNew16 4
  kat hj BumpNew16 5
  apply load_step _ _ _ _ (Int.toBytes 8 ret.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  apply Eventually.done
  have h16 : (16 : BitVec 64).toNat = 16 := rfl
  have hq : (p + (16 : BitVec 64)).toNat = p.toNat + 16 := by
    simp only [BitVec.toNat_add, h16]; omega
  have hq' : p + BitVec.ofNat 64 (16) = p + (16 : BitVec 64) := rfl
  have hsplit : List.replicate avail (0 : UInt8) = List.replicate (16) 0 ++ List.replicate (avail - 16) 0 := by
    rw [List.replicate_append_replicate]; congr 1; omega
  rw [hsplit, Mem.At_append_sep _ _ _ (by simp; omega)] at H1
  simp only [List.length_replicate, hq'] at H1
  have H2 : ((Eq ((Int.toBytes 8 (p + (16 : BitVec 64)).toInt).At (label "runtime.fvBump").toBitVec)
      ⋆ Eq ((List.replicate (avail - 16) 0).At (p + (16 : BitVec 64))))
      ⋆ (Eq ((Int.toBytes 8 ret.toBitVec.toInt).At rsp.toBitVec) ⋆ Eq (stk.At (rsp.toBitVec - BitVec.ofNat 64 S))
        ⋆ Eq (spill.At (rsp.toBitVec + 8)) ⋆ Eq ((List.replicate (16) 0).At p) ⋆ F)) m1 := by ecancel
  have H3 := sep_mono_left (P' := bumpHeap (avail - 16))
    (fun m hm => ⟨p + (16 : BitVec 64), by omega, hm⟩) H2
  refine ⟨by simp, ?_, rfl, rfl, stk, spill, hstk, hsp, ?_⟩
  · apply UInt64.toBitVec_inj.mp; simp
  · dsimp only; ecancel
set_option maxHeartbeats 4000000 in
theorem bump_newobject32 (j : Nat) (hj : BumpNew32.IsInfixAt Host.prog j)
    (hf : ∀ i < j, Host.prog[i]? ≠ some (.label "runtime.newobject")) (ty : BitVec 64) {S : Nat} :
    NewobjectC bumpHeap ty 32 S := by
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
  simp only [BumpNew32] at hk
  kat hj BumpNew32 0
  kat hj BumpNew32 1
  apply load_step _ _ _ _ (Int.toBytes 8 p.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hj BumpNew32 2
  kat hj BumpNew32 3
  apply store_step _ _ _ _ _ (Int.toBytes 8 p.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  intro m1 H1
  simp only [Width.bytes, Width.bits] at H1
  kunfold
  kat hj BumpNew32 4
  kat hj BumpNew32 5
  apply load_step _ _ _ _ (Int.toBytes 8 ret.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  apply Eventually.done
  have h32 : (32 : BitVec 64).toNat = 32 := rfl
  have hq : (p + (32 : BitVec 64)).toNat = p.toNat + 32 := by
    simp only [BitVec.toNat_add, h32]; omega
  have hq' : p + BitVec.ofNat 64 (32) = p + (32 : BitVec 64) := rfl
  have hsplit : List.replicate avail (0 : UInt8) = List.replicate (32) 0 ++ List.replicate (avail - 32) 0 := by
    rw [List.replicate_append_replicate]; congr 1; omega
  rw [hsplit, Mem.At_append_sep _ _ _ (by simp; omega)] at H1
  simp only [List.length_replicate, hq'] at H1
  have H2 : ((Eq ((Int.toBytes 8 (p + (32 : BitVec 64)).toInt).At (label "runtime.fvBump").toBitVec)
      ⋆ Eq ((List.replicate (avail - 32) 0).At (p + (32 : BitVec 64))))
      ⋆ (Eq ((Int.toBytes 8 ret.toBitVec.toInt).At rsp.toBitVec) ⋆ Eq (stk.At (rsp.toBitVec - BitVec.ofNat 64 S))
        ⋆ Eq (spill.At (rsp.toBitVec + 8)) ⋆ Eq ((List.replicate (32) 0).At p) ⋆ F)) m1 := by ecancel
  have H3 := sep_mono_left (P' := bumpHeap (avail - 32))
    (fun m hm => ⟨p + (32 : BitVec 64), by omega, hm⟩) H2
  refine ⟨by simp, ?_, rfl, rfl, stk, spill, hstk, hsp, ?_⟩
  · apply UInt64.toBitVec_inj.mp; simp
  · dsimp only; ecancel
end Fk
