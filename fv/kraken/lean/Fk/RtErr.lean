import Fk.RtCopy

/-!
# Models of the `fmt.errorf` and `runtime.convT64` contracts (1b-fix X2)

`RtErr` (Fk/RtErr.S): `fmt.errorf` returns rax = 0 when `len(a)` (rdi) is 0
and rax = 1 otherwise; `runtime.convT64` returns rax = 1. They allocate
nothing. `rt_errorf_nil`, `rt_errorf`, `rt_convT64` prove that this code
satisfies `FmtErrorfNilC S`, `FmtErrorfC Heap S` and `ConvT64C Heap S` for
every `S` and every heap predicate. They show that the three contracts are
satisfiable together (one `fmt.errorf` meets both of its contracts); they are
not models of Go's formatting.
-/

open Fk

namespace Fk
def RtErr : Program := include_x64_rt "Fk/RtErr.S"

variable [Host]

set_option maxHeartbeats 4000000 in
theorem rt_errorf_nil (j : Nat) (hj : RtErr.IsInfixAt Host.prog j) (hf : LabelsFresh RtErr j) (S : Nat) :
    FmtErrorfNilC S := by
  intro st ret fs stk spill F _hrbx hrdi _hpct hstk hsp hm
  rw [label_at' hj hf (j := 0) (by rfl) (by rfl)]
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := st
  simp only at hrdi hm ⊢
  subst hrdi
  kat hj RtErr 0
  kat hj RtErr 1
  intro _
  kat hj RtErr 2
  split
  case isTrue h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
  simp only [Effects.All]
  kat hj RtErr 3
  intro _
  kat hj RtErr 4
  apply load_step _ _ _ _ (Int.toBytes 8 ret.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  apply Eventually.done
  refine ⟨by simp, ?_, rfl, ?_, stk, spill, hstk, hsp, by ecancel⟩
  · apply UInt64.toBitVec_inj.mp; simp
  · apply UInt64.toBitVec_inj.mp; simp

set_option maxHeartbeats 4000000 in
theorem rt_errorf (j : Nat) (hj : RtErr.IsInfixAt Host.prog j) (hf : LabelsFresh RtErr j)
    (Heap : Nat → DataMem → Prop) (S : Nat) : FmtErrorfC Heap S := by
  intro st ret avail fs args stk spill F _hrbx hrdi _hrsi _hargs hstk hsp hm
  rw [label_at' hj hf (j := 0) (by rfl) (by rfl)]
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := st
  simp only at hrdi hm ⊢
  kat hj RtErr 0
  kat hj RtErr 1
  intro _
  kat hj RtErr 2
  split
  case isFalse h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
    have := congrArg BitVec.toNat h; simp at this; omega
  simp only [Effects.All]
  klabel hj hf RtErr 5
  kat hj RtErr 5
  kat hj RtErr 6
  kat hj RtErr 7
  apply load_step _ _ _ _ (Int.toBytes 8 ret.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  apply Eventually.done
  refine ⟨by simp, ?_, rfl, ?_, stk, spill, avail, hstk, hsp, Nat.le_refl _, by ecancel⟩
  · apply UInt64.toBitVec_inj.mp; simp
  · intro h; have := congrArg UInt64.toNat h; simp only [] at this; revert this; decide

set_option maxHeartbeats 4000000 in
/-- The same code meets `FmtErrorfWC` (re-proof fix X5): one `fmt.errorf`
satisfies its three contracts. -/
theorem rt_errorf_w (j : Nat) (hj : RtErr.IsInfixAt Host.prog j) (hf : LabelsFresh RtErr j)
    (Heap : Nat → DataMem → Prop) (S : Nat) : FmtErrorfWC Heap S := by
  intro st ret avail fs pre ity msg stk spill e sp F _hrbx hrdi _hrsi _hargs _hity hstk hsp _hav hm
  rw [label_at' hj hf (j := 0) (l := "fmt.errorf") (by rfl) (by rfl)]
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := st
  simp only at hrdi hm ⊢
  kat hj RtErr 0
  kat hj RtErr 1
  intro _
  kat hj RtErr 2
  split
  case isFalse h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
    have := congrArg BitVec.toNat h; simp at this; omega
  simp only [Effects.All]
  klabel hj hf RtErr 5
  kat hj RtErr 5
  kat hj RtErr 6
  kat hj RtErr 7
  apply load_step _ _ _ _ (Int.toBytes 8 ret.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  apply Eventually.done
  refine ⟨by simp, ?_, rfl, ?_, stk, spill, avail, hstk, hsp, Nat.le_refl _, by ecancel⟩
  · apply UInt64.toBitVec_inj.mp; simp
  · intro h; have := congrArg UInt64.toNat h; simp only [] at this; revert this; decide

set_option maxHeartbeats 4000000 in
theorem rt_convT64 (j : Nat) (hj : RtErr.IsInfixAt Host.prog j) (hf : LabelsFresh RtErr j)
    (Heap : Nat → DataMem → Prop) (S : Nat) : ConvT64C Heap S := by
  intro st ret avail stk spill F _hav hstk hsp hm
  rw [label_at' hj hf (j := 8) (by rfl) (by decide)]
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := st
  simp only at hm ⊢
  kat hj RtErr 8
  kat hj RtErr 9
  kat hj RtErr 10
  apply load_step _ _ _ _ (Int.toBytes 8 ret.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  apply Eventually.done
  refine ⟨by simp, ?_, rfl, ?_, stk, spill, avail, hstk, hsp, Nat.le_refl _, by omega, by ecancel⟩
  · apply UInt64.toBitVec_inj.mp; simp
  · intro h; have := congrArg UInt64.toNat h; simp only [] at this; revert this; decide

end Fk
