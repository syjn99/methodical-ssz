import Fk.Step
import Fk.Labels
import Fk.Bytes
import E2e.CpReject
import E2eList.StmtSc

/-!
# T2 `(*v1alpha1.SyncCommittee).UnmarshalSSZ`: size reject (LV)

Directives 2–7 (guard, prologue `sub $0x30`, rbx spill), 9–10 `cmp $0x6030,%rcx; jne L_7d` taken,
`L_7d` (30), the two loads of `ssz.ErrSize` (31–32), epilogue 33–35 (`add $0x30`).
Proof text: `E2eScal.H4.dd_e2e_reject_size_main` (`DdReject.lean`) with this decoder's directive indices
and frame size. The statement is the frozen `sc_reject_size_stmt`.
-/

open Fk E2eList.Code
variable [Host]

namespace E2eList

/-- **T2 size reject (machine)**; statement = the frozen `sc_reject_size_stmt`. -/
theorem sc_e2e_reject_size_main : sc_reject_size_stmt := by
  intro k hk hf s ra guard e0 e1 fp s2 hfp h2 R h_mem hguard hlen
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only [E2e.errSize_addr_eq] at h_mem hguard hlen ⊢
  have := rsp.toNat_lt_size; have := guard.toNat_lt_size; have := rcx.toNat_lt_size; simp only [UInt64.size] at *
  kat hk ScUnmarshal 0
  kat hk ScUnmarshal 1
  kat hk ScUnmarshal 2
  apply load_step _ _ _ _ (Int.toBytes 8 guard.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk ScUnmarshal 3
  split
  · rename_i h; exfalso
    simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned] at h
    rcases h with h | h
    · apply h; omega
    · have := congrArg BitVec.toNat h; simp [BitVec.toNat_sub] at this; omega
  simp only [Effects.All]
  kat hk ScUnmarshal 4
  apply store_step_at _ _ (rsp.toBitVec - 8) _ _ _ fp _ _ (by bv_omega) (by ecancel) (by exact hfp)
  intro m1 H1
  simp only [Width.bytes, Width.bits] at H1
  kunfold
  kat hk ScUnmarshal 5
  kat hk ScUnmarshal 6
  kat hk ScUnmarshal 7
  apply store_step_at _ _ (rsp.toBitVec + 16) _ _ _ s2 _ _ (by bv_omega) (by ecancel) (by exact h2)
  intro m2 H2
  simp only [Width.bytes, Width.bits] at H2
  kunfold
  kat hk ScUnmarshal 8
  kat hk ScUnmarshal 9
  kat hk ScUnmarshal 10
  split
  case isFalse h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
    apply hlen; apply UInt64.toBitVec_inj.mp; apply BitVec.eq_of_toNat_eq
    have := congrArg BitVec.toNat h; simp [BitVec.toNat_sub] at this ⊢; omega
  simp only [Effects.All]
  klabel hk hf ScUnmarshal 30
  kat hk ScUnmarshal 30
  kat hk ScUnmarshal 31
  apply load_step _ _ _ _ (Int.toBytes 8 e0.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk ScUnmarshal 32
  apply load_step _ _ _ _ (Int.toBytes 8 e1.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk ScUnmarshal 33
  kat hk ScUnmarshal 34
  rw [show (48 : BitVec 64) + (rsp.toBitVec - 8#64 - 48) = rsp.toBitVec - 8 by bv_omega]
  apply load_step _ _ _ _ (Int.toBytes 8 rbp.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk ScUnmarshal 35
  rw [show rsp.toBitVec - 8 + 8#64 = rsp.toBitVec by bv_omega]
  apply load_step _ _ _ _ (Int.toBytes 8 ra.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  apply Eventually.done
  simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  rotate_right
  · ecancel
  all_goals first
    | exact trivial
    | with_reducible rfl
    | (apply UInt64.toBitVec_inj.mp
       simp only [UInt64.toBitVec_add, UInt64.toBitVec_ofNat, BitVec.ofNat_eq_ofNat, Width.bits]
       done)
    | (apply UInt64.toBitVec_inj.mp; apply BitVec.eq_of_toNat_eq
       simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, UInt64.toBitVec_add,
         UInt64.toBitVec_ofNat, Width.bits]
       omega)

end E2eList
