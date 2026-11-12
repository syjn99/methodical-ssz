import Runtime.BumpAllocator
import Runtime.BumpAllocatorVariants
import TestTarget.FunctionSpecs

/-!
# Bump-allocator model of `runtime.newobject` for one 72-byte object (witness only)

`BumpNew72` (`Prysm/AttestationData/BumpNew72.S`) is `Runtime/BumpNew32.S` with the object size 0x48; the theorem
is the text of `Runtime.bump_newobject32` with 32 replaced by 72. It discharges
`NewobjectC bumpHeap ty 72 S` in the AttestationData witnesses (the Checkpoint object of the
Go 1.26.10 ELF is 72 bytes, `adCpType` Size_ = 0x48). It is a model in a witness host, not a
claim about the Go runtime.
-/

open Machine Runtime TestTarget

namespace Prysm.AttestationData

def BumpNew72 : Program := include_x64_rt "Prysm/AttestationData/BumpNew72.S"

variable [Host]

set_option maxHeartbeats 4000000 in
theorem bump_newobject72 (j : Nat) (hj : BumpNew72.IsInfixAt Host.prog j)
    (hf : ∀ i < j, Host.prog[i]? ≠ some (.label "runtime.newobject")) (ty : BitVec 64) {S : Nat} :
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
  simp only [BumpNew72] at hk
  kat hj BumpNew72 0
  kat hj BumpNew72 1
  apply load_step _ _ _ _ (Int.toBytes 8 p.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hj BumpNew72 2
  kat hj BumpNew72 3
  apply store_step _ _ _ _ _ (Int.toBytes 8 p.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  intro m1 H1
  simp only [Width.bytes, Width.bits] at H1
  kunfold
  kat hj BumpNew72 4
  kat hj BumpNew72 5
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
end Prysm.AttestationData
