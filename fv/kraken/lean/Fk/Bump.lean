import Fk.Contracts
import Fk.Labels
import Fk.Include

/-!
# A `runtime.makeslice` that satisfies `MakesliceC` (non-vacuity of the contract)

`BumpAlloc` (Fk/BumpAlloc.S) is a bump allocator over a zeroed region. Its heap
predicate `bumpHeap avail`: the 8-byte pointer at label `runtime.fvBump` holds
`p`, and the `avail` bytes at `p` are 0. `bump_makeslice` proves, on Kraken's
semantics, that this code satisfies `MakesliceC bumpHeap ty 8 0` for every
`ty`. It is a model of the contract, not Go's allocator.
-/

open Fk

namespace Fk
def BumpAlloc : Program := include_x64_rt "Fk/BumpAlloc.S"

variable [Host]

def bumpHeap (avail : Nat) (m : DataMem) : Prop :=
  ∃ p : BitVec 64, p.toNat + avail < 2 ^ 64 ∧
    (Eq ((Int.toBytes 8 p.toInt).At (label "runtime.fvBump").toBitVec) ⋆ Eq ((List.replicate avail 0).At p)) m

theorem sep_exists_left {α : Type} {Q : α → DataMem → Prop} {R : DataMem → Prop} {m : DataMem}
    (h : ((fun m => ∃ x, Q x m) ⋆ R) m) : ∃ x, (Q x ⋆ R) m := by
  obtain ⟨a, b, hu, hi, ⟨x, hq⟩, hr⟩ := h
  exact ⟨x, a, b, hu, hi, hq, hr⟩

theorem sep_pure_left {φ : Prop} {P R : DataMem → Prop} {m : DataMem}
    (h : ((fun m => φ ∧ P m) ⋆ R) m) : φ ∧ (P ⋆ R) m := by
  obtain ⟨a, b, hu, hi, ⟨hφ, hp⟩, hr⟩ := h
  exact ⟨hφ, a, b, hu, hi, hp, hr⟩

theorem sep_mono_left {P P' R : DataMem → Prop} {m : DataMem} (hP : ∀ m, P m → P' m)
    (h : (P ⋆ R) m) : (P' ⋆ R) m := by
  obtain ⟨a, b, hu, hi, hp, hr⟩ := h
  exact ⟨a, b, hu, hi, hP a hp, hr⟩

set_option maxHeartbeats 4000000 in
theorem bump_makeslice (j : Nat) (hj : BumpAlloc.IsInfixAt Host.prog j)
    (hf : ∀ i < j, Host.prog[i]? ≠ some (.label "runtime.makeslice")) (ty : BitVec 64) :
    MakesliceC bumpHeap ty 8 0 := by
  intro st ret cnt avail stk F _hty _hrbx hrcx hav hstk hm
  have hL := label_in_fragment hj (j := 0) (by decide) (by decide) hf
  rw [hL]
  have hstk0 : stk = [] := List.length_eq_zero_iff.mp hstk
  subst hstk0
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := st
  simp only at hrcx hm ⊢
  have hm' : (bumpHeap avail ⋆ (Eq ((Int.toBytes 8 ret.toBitVec.toInt).At rsp.toBitVec)
      ⋆ Eq (([] : List UInt8).At (rsp.toBitVec - BitVec.ofNat 64 0)) ⋆ F)) mem := by ecancel
  obtain ⟨p, hp⟩ := sep_exists_left (Q := fun (p : BitVec 64) (m : DataMem) => p.toNat + avail < 2 ^ 64 ∧
    (Eq ((Int.toBytes 8 p.toInt).At (label "runtime.fvBump").toBitVec) ⋆ Eq ((List.replicate avail 0).At p)) m) hm'
  obtain ⟨hpa, hp⟩ := sep_pure_left hp
  have hk := hj
  simp only [BumpAlloc] at hk
  kat hj BumpAlloc 0
  kat hj BumpAlloc 1
  apply load_step _ _ _ _ (Int.toBytes 8 p.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hj BumpAlloc 2
  kat hj BumpAlloc 3
  apply store_step _ _ _ _ _ (Int.toBytes 8 p.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  intro m1 H1
  simp only [Width.bytes, Width.bits] at H1
  kunfold
  kat hj BumpAlloc 4
  kat hj BumpAlloc 5
  apply load_step _ _ _ _ (Int.toBytes 8 ret.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  apply Eventually.done
  have hq : (p + rcx.toBitVec * 8#64).toNat = p.toNat + 8 * cnt := by
    simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, UInt64.toNat_toBitVec, hrcx]; omega
  have hq' : p + BitVec.ofNat 64 (8 * cnt) = p + rcx.toBitVec * 8#64 := by
    apply BitVec.eq_of_toNat_eq; rw [hq]; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hsplit : List.replicate avail (0 : UInt8) = List.replicate (8 * cnt) 0 ++ List.replicate (avail - 8 * cnt) 0 := by
    rw [List.replicate_append_replicate]; congr 1; omega
  rw [hsplit, Mem.At_append_sep _ _ _ (by simp; omega)] at H1
  simp only [List.length_replicate, hq'] at H1
  have H2 : ((Eq ((Int.toBytes 8 (p + rcx.toBitVec * 8#64).toInt).At (label "runtime.fvBump").toBitVec)
      ⋆ Eq ((List.replicate (avail - 8 * cnt) 0).At (p + rcx.toBitVec * 8#64)))
      ⋆ (Eq ((Int.toBytes 8 ret.toBitVec.toInt).At rsp.toBitVec) ⋆ Eq (([] : List UInt8).At (rsp.toBitVec - 0#64))
        ⋆ Eq ((List.replicate (8 * cnt) 0).At p) ⋆ F)) m1 := by ecancel
  have H3 := sep_mono_left (P' := bumpHeap (avail - 8 * cnt))
    (fun m hm => ⟨p + rcx.toBitVec * 8#64, by omega, hm⟩) H2
  refine ⟨by simp, ?_, rfl, [], rfl, ?_⟩
  · apply UInt64.toBitVec_inj.mp; simp
  · dsimp only; ecancel
end Fk
