import Runtime.BumpAllocator
import Runtime.BumpAllocatorVariants
import TestTarget.FunctionSpecs
import Prysm.ElfData.IndexedAttestation

/-!
# Type-dispatching bump model of `runtime.makeslice` for the decoder witness host

The decoder accept path needs `MakesliceC` with esz 1 (uint8 type word) and esz 8 (`lvU64Type_addr`) in one Host.
`Prysm/RuntimeModel/BumpAllocDc.S` is the text of the model `Prysm/RuntimeModel/BumpAllocT3.S` (branch `claude/ssz-fv-list-vector-20261112`,
commit `a1c5d0d`, not in this branch's base) with the label renamed: it bumps by 8·cnt for `type__+387456` and by cnt
otherwise. The two theorems below are the text of `Prysm.RuntimeModel.bump_makeslice_uint64_dispatch_size1` / `Prysm.RuntimeModel.bump_makeslice_uint64_dispatch_size8` of that commit (`Prysm/RuntimeModel/BumpAllocatorUint64AndStructDispatch.lean`)
with the names changed. Abstract model for non-vacuity only, not a Go refinement. The `.S` file is in
the Lake `input_dir` `runtime_model_S`.
-/

open Machine Runtime TestTarget

namespace Prysm.RuntimeModel

def BumpAllocUint64DispatchForDataColumnsByRootIdentifier : Program := include_x64_rt "Prysm/RuntimeModel/BumpAllocDc.S"

variable [Host]

/-- The esz-1 branch: any type word other than `lvU64Type_addr`. -/
theorem bump_makeslice_uint64_dispatch_for_data_columns_by_root_identifier_size1 (j : Nat) (hj : BumpAllocUint64DispatchForDataColumnsByRootIdentifier.IsInfixAt Host.prog j)
    (hf : ∀ i < j, Host.prog[i]? ≠ some (.label "runtime.makeslice")) (ty : BitVec 64)
    (hne : ty ≠ ElfData.IndexedAttestation.lvU64Type_addr) {S : Nat} :
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
  kat hj BumpAllocUint64DispatchForDataColumnsByRootIdentifier 0
  kat hj BumpAllocUint64DispatchForDataColumnsByRootIdentifier 1
  kat hj BumpAllocUint64DispatchForDataColumnsByRootIdentifier 2
  kat hj BumpAllocUint64DispatchForDataColumnsByRootIdentifier 3
  split
  case isTrue h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
    simp only at _hty
    apply hne; rw [← _hty]
    simp only [ElfData.IndexedAttestation.lvU64Type_addr, Int64.toBitVec_add, Int64.toBitVec_ofNat]
    have h2 := congrArg (· + ((label "type__").toBitVec + 387456#64)) h
    simp only [BitVec.sub_add_cancel, BitVec.zero_add] at h2
    exact h2
  simp only [Effects.All]
  kat hj BumpAllocUint64DispatchForDataColumnsByRootIdentifier 4
  apply load_step _ _ _ _ (Int.toBytes 8 p.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hj BumpAllocUint64DispatchForDataColumnsByRootIdentifier 5
  kat hj BumpAllocUint64DispatchForDataColumnsByRootIdentifier 6
  apply store_step _ _ _ _ _ (Int.toBytes 8 p.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  intro m1 H1
  simp only [Width.bytes, Width.bits] at H1
  kunfold
  kat hj BumpAllocUint64DispatchForDataColumnsByRootIdentifier 7
  kat hj BumpAllocUint64DispatchForDataColumnsByRootIdentifier 8
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
theorem bump_makeslice_uint64_dispatch_for_data_columns_by_root_identifier_size8 (j : Nat) (hj : BumpAllocUint64DispatchForDataColumnsByRootIdentifier.IsInfixAt Host.prog j)
    (hf : ∀ i < j, Host.prog[i]? ≠ some (.label "runtime.makeslice")) (hfl : LabelsFresh BumpAllocUint64DispatchForDataColumnsByRootIdentifier j) {S : Nat} :
    MakesliceC bumpHeap ElfData.IndexedAttestation.lvU64Type_addr 8 S := by
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
  kat hj BumpAllocUint64DispatchForDataColumnsByRootIdentifier 0
  kat hj BumpAllocUint64DispatchForDataColumnsByRootIdentifier 1
  kat hj BumpAllocUint64DispatchForDataColumnsByRootIdentifier 2
  kat hj BumpAllocUint64DispatchForDataColumnsByRootIdentifier 3
  split
  case isFalse h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
    simp only at _hty
    apply h; rw [_hty]
    simp only [ElfData.IndexedAttestation.lvU64Type_addr, Int64.toBitVec_add, Int64.toBitVec_ofNat]
    exact BitVec.sub_self _
  simp only [Effects.All]
  klabel hj hfl BumpAllocUint64DispatchForDataColumnsByRootIdentifier 9
  kat hj BumpAllocUint64DispatchForDataColumnsByRootIdentifier 9
  kat hj BumpAllocUint64DispatchForDataColumnsByRootIdentifier 10
  apply load_step _ _ _ _ (Int.toBytes 8 p.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hj BumpAllocUint64DispatchForDataColumnsByRootIdentifier 11
  kat hj BumpAllocUint64DispatchForDataColumnsByRootIdentifier 12
  apply store_step _ _ _ _ _ (Int.toBytes 8 p.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  intro m1 H1
  simp only [Width.bytes, Width.bits] at H1
  kunfold
  kat hj BumpAllocUint64DispatchForDataColumnsByRootIdentifier 13
  kat hj BumpAllocUint64DispatchForDataColumnsByRootIdentifier 14
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

end Prysm.RuntimeModel
