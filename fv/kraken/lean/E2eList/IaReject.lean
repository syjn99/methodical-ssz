import Fk.Step
import Fk.Labels
import Fk.Bytes
import E2e.CpReject
import E2eScal.StackGuard
import E2eList.StmtIa
import E2eList.IaAddr

/-!
# `(*v1alpha1.IndexedAttestation).UnmarshalSSZ`: size reject and offset reject

- `ia_e2e_reject_size_main : ia_reject_size_stmt`: directives 2–4 (large-frame guard `lea -0x30(%rsp),%r12`, closed
  with `E2eScal.lea_cmp_be_false`, N = 48), 5–8 prologue (`sub $0xa8`, rbx spill to rsp + 16), 9–10
  `cmp $0xe4,%rcx; jb L_268` taken, `L_268` (137), the two loads of `ssz.ErrSize` (138–139), epilogue 140–142.
- `ia_e2e_reject_offset_main : ia_reject_offset_stmt`: 9–10 not taken, 11 `mov (%rbx),%edx` (32-bit load of `off`),
  16–17 `cmp $0xe4,%rdx; jne L_251` taken, `L_251` (131), the two loads of `ssz.ErrInvalidVariableOffset` (132–133),
  epilogue 134–136.
-/

open Fk E2eList.Code
variable [Host]

namespace E2eList


-- Measured cause: `kat` unfolds the 279-directive program literal `IaUnmarshal` with `simp`; at the
-- default `maxRecDepth` (512) that `simp` stops with "maximum recursion depth has been reached"; 1024 passes.
set_option maxRecDepth 1024 in
theorem ia_e2e_reject_size_main : ia_reject_size_stmt := by
  intro k hk hf s ra guard e0 e1 fp s2 hfp h2 R h_mem hguard hlen
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hguard hlen
  dsimp only
  have hz1 := rsp.toNat_lt_size; have hz2 := guard.toNat_lt_size; have hz3 := rcx.toNat_lt_size
  simp only [UInt64.size] at hz1 hz2 hz3
  kat hk IaUnmarshal 0
  kat hk IaUnmarshal 1
  kat hk IaUnmarshal 2
  kat hk IaUnmarshal 3
  apply load_step _ _ _ _ (Int.toBytes 8 guard.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk IaUnmarshal 4
  split
  case isTrue h =>
    exfalso
    rw [E2eScal.lea_cmp_be_false rsp.toBitVec _ guard.toBitVec _ _ 48 (by rfl) hguard] at h
    exact Bool.noConfusion h
  simp only [Effects.All]
  kat hk IaUnmarshal 5
  apply store_step_at _ _ (rsp.toBitVec - 8) _ _ _ fp _ _ (by iaaddr) (by ecancel) (by exact hfp)
  intro m1 H1
  simp only [Width.bytes, Width.bits] at H1
  kunfold
  kat hk IaUnmarshal 6
  kat hk IaUnmarshal 7
  kat hk IaUnmarshal 8
  apply store_step_at _ _ (rsp.toBitVec + 16) _ _ _ s2 _ _ (by iaaddr) (by ecancel) (by exact h2)
  intro m2 H2
  simp only [Width.bytes, Width.bits] at H2
  kunfold
  kat hk IaUnmarshal 9
  kat hk IaUnmarshal 10
  split
  case isFalse h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned] at h; omega
  simp only [Effects.All]
  klabel hk hf IaUnmarshal 137
  kat hk IaUnmarshal 137
  kat hk IaUnmarshal 138
  apply load_step _ _ _ _ (Int.toBytes 8 e0.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk IaUnmarshal 139
  apply load_step _ _ _ _ (Int.toBytes 8 e1.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk IaUnmarshal 140
  kat hk IaUnmarshal 141
  apply load_step_at _ _ (rsp.toBitVec - 8) _ _ (Int.toBytes 8 rbp.toBitVec.toInt) _ _ (by iaaddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk IaUnmarshal 142
  apply load_step_at _ _ rsp.toBitVec _ _ (Int.toBytes 8 ra.toBitVec.toInt) _ _ (by iaaddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  apply Eventually.done
  try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  rotate_right
  · ecancel
  all_goals first
    | exact trivial
    | with_reducible rfl
    | (apply UInt64.toBitVec_inj.mp
       simp only [UInt64.toBitVec_add, UInt64.toBitVec_ofNat, BitVec.ofNat_eq_ofNat, Width.bits]
       done)
    | (apply UInt64.toBitVec_inj.mp; iaaddr)

-- Same measured cause and value as `ia_e2e_reject_size_main`.
set_option maxRecDepth 1024 in
theorem ia_e2e_reject_offset_main : ia_reject_offset_stmt := by
  intro k hk hf s ra guard e0 e1 fp s2 hfp h2 off hoff4 hoff R h_mem hguard hlen
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hguard hlen
  dsimp only
  have hz1 := rsp.toNat_lt_size; have hz2 := guard.toNat_lt_size; have hz3 := rcx.toNat_lt_size
  simp only [UInt64.size] at hz1 hz2 hz3
  kat hk IaUnmarshal 0
  kat hk IaUnmarshal 1
  kat hk IaUnmarshal 2
  kat hk IaUnmarshal 3
  apply load_step _ _ _ _ (Int.toBytes 8 guard.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk IaUnmarshal 4
  split
  case isTrue h =>
    exfalso
    rw [E2eScal.lea_cmp_be_false rsp.toBitVec _ guard.toBitVec _ _ 48 (by rfl) hguard] at h
    exact Bool.noConfusion h
  simp only [Effects.All]
  kat hk IaUnmarshal 5
  apply store_step_at _ _ (rsp.toBitVec - 8) _ _ _ fp _ _ (by iaaddr) (by ecancel) (by exact hfp)
  intro m1 H1
  simp only [Width.bytes, Width.bits] at H1
  kunfold
  kat hk IaUnmarshal 6
  kat hk IaUnmarshal 7
  kat hk IaUnmarshal 8
  apply store_step_at _ _ (rsp.toBitVec + 16) _ _ _ s2 _ _ (by iaaddr) (by ecancel) (by exact h2)
  intro m2 H2
  simp only [Width.bytes, Width.bits] at H2
  kunfold
  kat hk IaUnmarshal 9
  kat hk IaUnmarshal 10
  split
  case isTrue h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned] at h; omega
  simp only [Effects.All]
  kat hk IaUnmarshal 11
  apply load_step _ _ _ _ off _ _ (by ecancel) (by exact hoff4)
  kunfold
  kat hk IaUnmarshal 12
  kat hk IaUnmarshal 13
  kat hk IaUnmarshal 14
  kat hk IaUnmarshal 15
  kat hk IaUnmarshal 16
  kat hk IaUnmarshal 17
  split
  case isFalse h =>
    exfalso; apply hoff
    have hz : BitVec.zeroExtend 64 (BitVec.ofInt 32 (Int.ofBytes off)) - 228 = 0 := by
      simpa [CondCode.interp, StatusFlags.from_result] using h
    have hv : BitVec.ofInt 32 (Int.ofBytes off) = 228#32 := by
      have h1 := congrArg (· + (228 : BitVec 64)) hz
      simp only [BitVec.sub_add_cancel, BitVec.zero_add] at h1
      have h2 := congrArg BitVec.toNat h1
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_setWidth, BitVec.truncate_eq_setWidth, BitVec.toNat_ofNat, BitVec.toNat_add,
        BitVec.ofNat_eq_ofNat, Nat.zero_add, Nat.zero_mod] at h2 ⊢
      have hlt : (BitVec.ofInt 32 (Int.ofBytes off)).toNat < 2 ^ 32 := BitVec.isLt _
      generalize (BitVec.ofInt 32 (Int.ofBytes off)).toNat = t at h2 hlt ⊢
      simp only [Nat.reducePow] at hlt h2 ⊢
      omega
    rw [← toBytes_ofInt_ofBytes 32 4 rfl off hoff4, hv]; decide
  simp only [Effects.All]
  klabel hk hf IaUnmarshal 131
  kat hk IaUnmarshal 131
  kat hk IaUnmarshal 132
  apply load_step _ _ _ _ (Int.toBytes 8 e0.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk IaUnmarshal 133
  apply load_step _ _ _ _ (Int.toBytes 8 e1.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk IaUnmarshal 134
  kat hk IaUnmarshal 135
  apply load_step_at _ _ (rsp.toBitVec - 8) _ _ (Int.toBytes 8 rbp.toBitVec.toInt) _ _ (by iaaddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk IaUnmarshal 136
  apply load_step_at _ _ rsp.toBitVec _ _ (Int.toBytes 8 ra.toBitVec.toInt) _ _ (by iaaddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  apply Eventually.done
  try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  rotate_right
  · ecancel
  all_goals first
    | exact trivial
    | with_reducible rfl
    | (apply UInt64.toBitVec_inj.mp
       simp only [UInt64.toBitVec_add, UInt64.toBitVec_ofNat, BitVec.ofNat_eq_ofNat, Width.bits]
       done)
    | (apply UInt64.toBitVec_inj.mp; iaaddr)

end E2eList
