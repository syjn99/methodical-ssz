import Runtime.CopyModel
import Runtime.BumpAllocator

/-!
# Models of the `fmt.errorf` and `runtime.convT64` contracts

`ErrorfConvT64Model` (Runtime/ErrorfConvT64Model.S): `fmt.errorf` returns rax = 0 when `len(a)` (rdi) is 0 and
rax = 1 otherwise; it allocates nothing. `runtime.convT64` takes 8 bytes from
the bump heap, stores v there and returns the box (the heap case of `BoxIn`).
-/

open Machine Runtime

namespace Runtime
def ErrorfConvT64Model : Program := include_x64_code "Runtime/ErrorfConvT64Model.S"

variable [Host]

set_option maxHeartbeats 4000000 in
theorem model_errorf_nil (j : Nat) (hj : ErrorfConvT64Model.IsInfixAt Host.prog j) (hf : LabelsFresh ErrorfConvT64Model j) (S : Nat) :
    FmtErrorfNilContract S := by
  intro st ret fs stk spill F _hrbx hrdi _hpct hstk hsp hm
  rw [label_at' hj hf (j := 0) (by rfl) (by rfl)]
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := st
  simp only at hrdi hm ⊢
  subst hrdi
  step_directive hj ErrorfConvT64Model 0
  step_directive hj ErrorfConvT64Model 1
  intro _
  step_directive hj ErrorfConvT64Model 2
  split
  case isTrue h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
  simp only [Effects.All]
  step_directive hj ErrorfConvT64Model 3
  intro _
  step_directive hj ErrorfConvT64Model 4
  apply load_step _ _ _ _ (Int.toBytes 8 ret.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  unfold_step
  apply Eventually.done
  refine ⟨by simp, ?_, rfl, ?_, stk, spill, hstk, hsp, by ecancel⟩
  · apply UInt64.toBitVec_inj.mp; simp
  · apply UInt64.toBitVec_inj.mp; simp

set_option maxHeartbeats 4000000 in
/-- The same code meets `FmtErrorfWrapContract`. -/
theorem model_errorf_wrap (j : Nat) (hj : ErrorfConvT64Model.IsInfixAt Host.prog j) (hf : LabelsFresh ErrorfConvT64Model j)
    (Heap : Nat → DataMem → Prop) (fs : List UInt8) (RO : DataMem → Prop)
    (MsgIn : BitVec 64 → List UInt8 → List UInt8 → Prop) (S : Nat) : FmtErrorfWrapContract Heap fs RO MsgIn S := by
  intro st ret avail ity msg hm stk spill e sp F _hrbx hrdi _hrsi _hity _hmsg hstk hsp _hav hmem
  rw [label_at' hj hf (j := 0) (l := "fmt.errorf") (by rfl) (by rfl)]
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := st
  simp only at hrdi hmem ⊢
  subst hrdi
  step_directive hj ErrorfConvT64Model 0
  step_directive hj ErrorfConvT64Model 1
  intro _
  step_directive hj ErrorfConvT64Model 2
  split
  case isFalse h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
  simp only [Effects.All]
  label_address hj hf ErrorfConvT64Model 5
  step_directive hj ErrorfConvT64Model 5
  step_directive hj ErrorfConvT64Model 6
  step_directive hj ErrorfConvT64Model 7
  apply load_step _ _ _ _ (Int.toBytes 8 ret.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  unfold_step
  apply Eventually.done
  refine ⟨by simp, ?_, rfl, ?_, stk, spill, avail, hstk, hsp, Nat.le_refl _, by ecancel⟩
  · apply UInt64.toBitVec_inj.mp; simp
  · intro h; have := congrArg UInt64.toNat h; simp only [] at this; revert this; decide

set_option maxHeartbeats 4000000 in
/-- The same code meets `FmtErrorfDecimalWrapContract`. -/
theorem model_errorf_decimal_wrap (j : Nat) (hj : ErrorfConvT64Model.IsInfixAt Host.prog j) (hf : LabelsFresh ErrorfConvT64Model j)
    (Heap : Nat → DataMem → Prop) (fs : List UInt8) (tw : BitVec 64) (S : Nat) : FmtErrorfDecimalWrapContract Heap fs tw S := by
  intro st ret avail ity msg hb stk spill bx v e sp F _hrbx hrdi _hrsi _hity _hbox hstk hsp _hav hmem
  rw [label_at' hj hf (j := 0) (l := "fmt.errorf") (by rfl) (by rfl)]
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := st
  simp only at hrdi hmem ⊢
  subst hrdi
  step_directive hj ErrorfConvT64Model 0
  step_directive hj ErrorfConvT64Model 1
  intro _
  step_directive hj ErrorfConvT64Model 2
  split
  case isFalse h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
  simp only [Effects.All]
  label_address hj hf ErrorfConvT64Model 5
  step_directive hj ErrorfConvT64Model 5
  step_directive hj ErrorfConvT64Model 6
  step_directive hj ErrorfConvT64Model 7
  apply load_step _ _ _ _ (Int.toBytes 8 ret.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  unfold_step
  apply Eventually.done
  refine ⟨by simp, ?_, rfl, ?_, stk, spill, avail, hstk, hsp, Nat.le_refl _, by ecancel⟩
  · apply UInt64.toBitVec_inj.mp; simp
  · intro h; have := congrArg UInt64.toNat h; simp only [] at this; revert this; decide

set_option maxHeartbeats 4000000 in
/-- The same code meets `FmtErrorfDecimalDecimalContract`. -/
theorem model_errorf_decimal_decimal (j : Nat) (hj : ErrorfConvT64Model.IsInfixAt Host.prog j) (hf : LabelsFresh ErrorfConvT64Model j)
    (Heap : Nat → DataMem → Prop) (fs : List UInt8) (tw : BitVec 64) (S : Nat) : FmtErrorfDecimalDecimalContract Heap fs tw S := by
  intro st ret avail hb1 hb2 stk spill bx1 v1 bx2 v2 F _hrbx hrdi _hrsi _hb1 _hb2 hstk hsp _hav hmem
  rw [label_at' hj hf (j := 0) (l := "fmt.errorf") (by rfl) (by rfl)]
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := st
  simp only at hrdi hmem ⊢
  subst hrdi
  step_directive hj ErrorfConvT64Model 0
  step_directive hj ErrorfConvT64Model 1
  intro _
  step_directive hj ErrorfConvT64Model 2
  split
  case isFalse h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
  simp only [Effects.All]
  label_address hj hf ErrorfConvT64Model 5
  step_directive hj ErrorfConvT64Model 5
  step_directive hj ErrorfConvT64Model 6
  step_directive hj ErrorfConvT64Model 7
  apply load_step _ _ _ _ (Int.toBytes 8 ret.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  unfold_step
  apply Eventually.done
  refine ⟨by simp, ?_, rfl, ?_, stk, spill, avail, hstk, hsp, Nat.le_refl _, by ecancel⟩
  · apply UInt64.toBitVec_inj.mp; simp
  · intro h; have := congrArg UInt64.toNat h; simp only [] at this; revert this; decide

set_option maxHeartbeats 4000000 in
/-- The bump-heap `convT64` meets `ConvT64Contract`: 8 bytes from the heap hold v; the box
is the heap case of `BoxIn`. -/
theorem model_convT64 (j : Nat) (hj : ErrorfConvT64Model.IsInfixAt Host.prog j) (hf : LabelsFresh ErrorfConvT64Model j)
    (S : Nat) : ConvT64Contract bumpHeap S := by
  intro st ret avail stk spill F hav hstk hsp hm
  rw [label_at' hj hf (j := 8) (by rfl) (by decide)]
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := st
  simp only at hm ⊢
  have hm' : (bumpHeap avail ⋆ (Eq ((Int.toBytes 8 ret.toBitVec.toInt).At rsp.toBitVec)
      ⋆ Eq (stk.At (rsp.toBitVec - BitVec.ofNat 64 S)) ⋆ Eq (spill.At (rsp.toBitVec + 8))
      ⋆ StaticBox rax.toBitVec ⋆ F)) mem := by ecancel
  obtain ⟨p, hp⟩ := sep_exists_left (Q := fun (p : BitVec 64) (m : DataMem) => p.toNat + avail < 2 ^ 64 ∧
    (Eq ((Int.toBytes 8 p.toInt).At (label "runtime.modelBumpPointer").toBitVec) ⋆ Eq ((List.replicate avail 0).At p)) m) hm'
  obtain ⟨hpa, hp⟩ := sep_pure_left hp
  have hsplit : List.replicate avail (0 : UInt8) = List.replicate 8 0 ++ List.replicate (avail - 8) 0 := by
    rw [List.replicate_append_replicate]; congr 1; omega
  rw [hsplit, Mem.At_append_sep _ _ _ (by simp; omega)] at hp
  simp only [List.length_replicate] at hp
  step_directive hj ErrorfConvT64Model 8
  step_directive hj ErrorfConvT64Model 9
  apply load_step _ _ _ _ (Int.toBytes 8 p.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  unfold_step
  step_directive hj ErrorfConvT64Model 10
  step_directive hj ErrorfConvT64Model 11
  apply store_step _ _ _ _ _ (Int.toBytes 8 p.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  intro m1 H1
  simp only [Width.bytes, Width.bits] at H1
  unfold_step
  step_directive hj ErrorfConvT64Model 12
  apply store_step _ _ _ _ _ (List.replicate 8 0) _ _ (by ecancel) (by simp)
  intro m2 H2
  simp only [Width.bytes, Width.bits] at H2
  unfold_step
  step_directive hj ErrorfConvT64Model 13
  step_directive hj ErrorfConvT64Model 14
  apply load_step _ _ _ _ (Int.toBytes 8 ret.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  unfold_step
  apply Eventually.done
  have h8 : (8 : BitVec 64).toNat = 8 := rfl
  have hq : (p + (8 : BitVec 64)).toNat = p.toNat + 8 := by
    simp only [BitVec.toNat_add, h8]; omega
  have hq' : p + BitVec.ofNat 64 8 = p + (8 : BitVec 64) := rfl
  simp only [hq'] at H2
  have H3 : ((Eq ((Int.toBytes 8 (p + (8 : BitVec 64)).toInt).At (label "runtime.modelBumpPointer").toBitVec)
      ⋆ Eq ((List.replicate (avail - 8) 0).At (p + (8 : BitVec 64))))
      ⋆ (Eq ((Int.toBytes 8 ret.toBitVec.toInt).At rsp.toBitVec) ⋆ Eq (stk.At (rsp.toBitVec - BitVec.ofNat 64 S))
        ⋆ Eq (spill.At (rsp.toBitVec + 8)) ⋆ StaticBox rax.toBitVec ⋆ Eq ((Int.toBytes 8 rax.toBitVec.toInt).At p) ⋆ F)) m2 := by
    ecancel
  have H4 := sep_mono_left (P' := bumpHeap (avail - 8)) (fun m hm => ⟨p + (8 : BitVec 64), by omega, hm⟩) H3
  refine ⟨by simp, ?_, rfl, stk, spill, Int.toBytes 8 rax.toBitVec.toInt, avail - 8, hstk, hsp, Or.inr rfl,
    by simp [Int.toBytes_length]; omega, by omega, ?_⟩
  · apply UInt64.toBitVec_inj.mp; simp
  · dsimp only; ecancel

end Runtime
