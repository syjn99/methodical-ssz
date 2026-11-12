import Runtime.BumpAllocator
import Prysm.ElfData.SyncAggregateAndSyncCommittee

/-!
# A `runtime.makeslice` that satisfies both `MakesliceC` instances of the SyncCommittee decoder in one Host (witness model)

`Prysm/RuntimeModel/BumpAllocT.S` is the bump allocator of `Runtime/BumpAlloc1.S` with one dispatch on the element type word:
if rax is `type__+337600` (the `[]uint8` type of the SyncCommittee backing array, `ElfData.SyncAggregateAndSyncCommittee.lvSliceType_addr`)
it bumps by 24·cnt (`lea (%rcx,%rcx,2)`, `lea (%rdx,%rsi,8)`), otherwise by cnt. A Host has one
`runtime.makeslice`; the SyncCommittee decoder needs `MakesliceC … lvSliceType_addr 24 S` and `MakesliceC … e2eU8Type_addr 1 S`
together, so a model of esz 24 alone (the shape of `Runtime.bump_makeslice`) cannot sit in the same witness Host as
`bump_makeslice1`. The real Go `makeslice` reads `et.Size_` from the type descriptor; this model compares the type
word with one address. It is an abstract model for non-vacuity only, not a Go refinement.
Proof text: `Runtime.bump_makeslice1` with the dispatch steps added. The `.S` file is in the Lake `input_dir` `runtime_model_S`
of the `Prysm` library, so Lake rebuilds the library when it changes.
-/

open Machine Runtime TestTarget

namespace Prysm.RuntimeModel

def BumpAllocByteSliceDispatch : Program := include_x64_rt "Prysm/RuntimeModel/BumpAllocT.S"

variable [Host]

/-- The esz-1 branch: any type word other than `lvSliceType_addr`. -/
theorem bump_makeslice_byte_slice_dispatch_size1 (j : Nat) (hj : BumpAllocByteSliceDispatch.IsInfixAt Host.prog j)
    (hf : ∀ i < j, Host.prog[i]? ≠ some (.label "runtime.makeslice")) (ty : BitVec 64)
    (hne : ty ≠ ElfData.SyncAggregateAndSyncCommittee.lvSliceType_addr) {S : Nat} :
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
  kat hj BumpAllocByteSliceDispatch 0
  kat hj BumpAllocByteSliceDispatch 1
  kat hj BumpAllocByteSliceDispatch 2
  kat hj BumpAllocByteSliceDispatch 3
  split
  case isTrue h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
    simp only at _hty
    apply hne; rw [← _hty]
    simp only [ElfData.SyncAggregateAndSyncCommittee.lvSliceType_addr, Int64.toBitVec_add, Int64.toBitVec_ofNat]
    have h2 := congrArg (· + ((label "type__").toBitVec + 337600#64)) h
    simp only [BitVec.sub_add_cancel, BitVec.zero_add] at h2
    exact h2
  simp only [Effects.All]
  kat hj BumpAllocByteSliceDispatch 4
  apply load_step _ _ _ _ (Int.toBytes 8 p.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hj BumpAllocByteSliceDispatch 5
  kat hj BumpAllocByteSliceDispatch 6
  apply store_step _ _ _ _ _ (Int.toBytes 8 p.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  intro m1 H1
  simp only [Width.bytes, Width.bits] at H1
  kunfold
  kat hj BumpAllocByteSliceDispatch 7
  kat hj BumpAllocByteSliceDispatch 8
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

/-- The esz-24 branch: the type word `lvSliceType_addr`. -/
theorem bump_makeslice_byte_slice_dispatch_size24 (j : Nat) (hj : BumpAllocByteSliceDispatch.IsInfixAt Host.prog j)
    (hf : ∀ i < j, Host.prog[i]? ≠ some (.label "runtime.makeslice")) (hfl : LabelsFresh BumpAllocByteSliceDispatch j) {S : Nat} :
    MakesliceC bumpHeap ElfData.SyncAggregateAndSyncCommittee.lvSliceType_addr 24 S := by
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
  kat hj BumpAllocByteSliceDispatch 0
  kat hj BumpAllocByteSliceDispatch 1
  kat hj BumpAllocByteSliceDispatch 2
  kat hj BumpAllocByteSliceDispatch 3
  split
  case isFalse h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
    simp only at _hty
    apply h; rw [_hty]
    simp only [ElfData.SyncAggregateAndSyncCommittee.lvSliceType_addr, Int64.toBitVec_add, Int64.toBitVec_ofNat]
    exact BitVec.sub_self _
  simp only [Effects.All]
  klabel hj hfl BumpAllocByteSliceDispatch 9
  kat hj BumpAllocByteSliceDispatch 9
  kat hj BumpAllocByteSliceDispatch 10
  apply load_step _ _ _ _ (Int.toBytes 8 p.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hj BumpAllocByteSliceDispatch 11
  kat hj BumpAllocByteSliceDispatch 12
  kat hj BumpAllocByteSliceDispatch 13
  apply store_step _ _ _ _ _ (Int.toBytes 8 p.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  intro m1 H1
  simp only [Width.bytes, Width.bits] at H1
  kunfold
  kat hj BumpAllocByteSliceDispatch 14
  kat hj BumpAllocByteSliceDispatch 15
  apply load_step _ _ _ _ (Int.toBytes 8 ret.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  apply Eventually.done
  have hq : (p + (rcx.toBitVec + rcx.toBitVec * 2#64) * 8#64).toNat = p.toNat + 24 * cnt := by
    simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, UInt64.toNat_toBitVec]; omega
  have hq' : p + BitVec.ofNat 64 (24 * cnt) = p + (rcx.toBitVec + rcx.toBitVec * 2#64) * 8#64 := by
    apply BitVec.eq_of_toNat_eq; rw [hq]; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hsplit : List.replicate avail (0 : UInt8) = List.replicate (24 * cnt) 0 ++ List.replicate (avail - 24 * cnt) 0 := by
    rw [List.replicate_append_replicate]; congr 1; omega
  rw [hsplit, Mem.At_append_sep _ _ _ (by simp; omega)] at H1
  simp only [List.length_replicate, hq'] at H1
  have H2 : ((Eq ((Int.toBytes 8 (p + (rcx.toBitVec + rcx.toBitVec * 2#64) * 8#64).toInt).At (label "runtime.fvBump").toBitVec)
      ⋆ Eq ((List.replicate (avail - 24 * cnt) 0).At (p + (rcx.toBitVec + rcx.toBitVec * 2#64) * 8#64)))
      ⋆ (Eq ((Int.toBytes 8 ret.toBitVec.toInt).At rsp.toBitVec) ⋆ Eq (stk.At (rsp.toBitVec - BitVec.ofNat 64 S))
        ⋆ Eq (spill.At (rsp.toBitVec + 8)) ⋆ Eq ((List.replicate (24 * cnt) 0).At p) ⋆ F)) m1 := by ecancel
  have H3 := sep_mono_left (P' := bumpHeap (avail - 24 * cnt))
    (fun m hm => ⟨p + (rcx.toBitVec + rcx.toBitVec * 2#64) * 8#64, by omega, hm⟩) H2
  refine ⟨by simp, ?_, rfl, rfl, stk, spill, hstk, hsp, ?_⟩
  · apply UInt64.toBitVec_inj.mp; simp
  · dsimp only; ecancel

end Prysm.RuntimeModel
