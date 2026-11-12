import Runtime.BumpAllocator
import Runtime.BumpAllocatorVariants
import TestTarget.FunctionSpecs

/-!
# Bump-allocator model of `runtime.newobject` for one 120-byte object (witness only)

`BumpNew120` (`E2eDepW/BumpNew120.S`) is `E2eAd/BumpNew72.S` with the object size 0x78; the theorem is
the text of `E2eAd.bump_newobject72` with 72 replaced by 120. It discharges `NewobjectC bumpHeap ty 120 S` in the
Deposit witness (the Deposit_Data object of the Go 1.26.10 ELF is 120 bytes, `depDataType` Size_ = 0x78). It is a
model in a witness host, not a claim about the Go runtime.
-/

open Machine Runtime TestTarget

namespace E2eDepW

def BumpNew120 : Program := include_x64_rt "E2eDepW/BumpNew120.S"

variable [Host]

theorem bump_newobject120 (j : Nat) (hj : BumpNew120.IsInfixAt Host.prog j)
    (hf : ∀ i < j, Host.prog[i]? ≠ some (.label "runtime.newobject")) (ty : BitVec 64) {S : Nat} :
    NewobjectC bumpHeap ty 120 S := by
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
  simp only [BumpNew120] at hk
  kat hj BumpNew120 0
  kat hj BumpNew120 1
  apply load_step _ _ _ _ (Int.toBytes 8 p.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hj BumpNew120 2
  kat hj BumpNew120 3
  apply store_step _ _ _ _ _ (Int.toBytes 8 p.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  intro m1 H1
  simp only [Width.bytes, Width.bits] at H1
  kunfold
  kat hj BumpNew120 4
  kat hj BumpNew120 5
  apply load_step _ _ _ _ (Int.toBytes 8 ret.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  apply Eventually.done
  have h120 : (120 : BitVec 64).toNat = 120 := rfl
  have hq : (p + (120 : BitVec 64)).toNat = p.toNat + 120 := by
    simp only [BitVec.toNat_add, h120]; omega
  have hq' : p + BitVec.ofNat 64 (120) = p + (120 : BitVec 64) := rfl
  have hsplit : List.replicate avail (0 : UInt8) = List.replicate (120) 0 ++ List.replicate (avail - 120) 0 := by
    rw [List.replicate_append_replicate]; congr 1; omega
  rw [hsplit, Mem.At_append_sep _ _ _ (by simp; omega)] at H1
  simp only [List.length_replicate, hq'] at H1
  have H2 : ((Eq ((Int.toBytes 8 (p + (120 : BitVec 64)).toInt).At (label "runtime.fvBump").toBitVec)
      ⋆ Eq ((List.replicate (avail - 120) 0).At (p + (120 : BitVec 64))))
      ⋆ (Eq ((Int.toBytes 8 ret.toBitVec.toInt).At rsp.toBitVec) ⋆ Eq (stk.At (rsp.toBitVec - BitVec.ofNat 64 S))
        ⋆ Eq (spill.At (rsp.toBitVec + 8)) ⋆ Eq ((List.replicate (120) 0).At p) ⋆ F)) m1 := by ecancel
  have H3 := sep_mono_left (P' := bumpHeap (avail - 120))
    (fun m hm => ⟨p + (120 : BitVec 64), by omega, hm⟩) H2
  refine ⟨by simp, ?_, rfl, rfl, stk, spill, hstk, hsp, ?_⟩
  · apply UInt64.toBitVec_inj.mp; simp
  · dsimp only; ecancel
end E2eDepW
