import Fk.Step
import Fk.Labels
import Fk.Bytes
import E2e.CpReject
import E2eScal.StackGuard
import E2eDec.StmtDec

/-!
# ENC decoder `(*v1alpha1.DataColumnsByRootIdentifier).UnmarshalSSZ`: size reject (D1) and offset reject (D2)

The text of `E2eList/IaReject.lean` (T3 P1, P2) with this function's directive indices: guard 2–4
(`lea -0x10(%rsp),%r12`, `E2eScal.lea_cmp_be_false` with N = 16), prologue 5–8 (`sub $0x88`, rbx spill to x + 16),
D1: 9–10 `cmp $0x24,%rcx; jb L_2f9` taken, 174–179; D2: 11 the 32-bit load of buf[32:36], 14–15
`cmp $0x24,%rdx; jne L_2e2` taken, 168–173.
-/

open Fk E2eDec.Code
variable [Host]

namespace E2eDec

/-- Address equation by `toNat` and `omega` (`kaddr` plus `Width.bits`). -/
macro "dcaddr" : tactic => `(tactic| (
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_neg, BitVec.toNat_ofNat, BitVec.ofNat_eq_ofNat,
    UInt64.toNat_toBitVec, UInt64.toBitVec_add, UInt64.toBitVec_ofNat, Width.bits, Nat.reducePow]
  all_goals omega))

-- Measured cause (logs 123, 124): `kat` unfolds the 279-directive program literal `DcUnmarshal` with `simp`; at the
-- default `maxRecDepth` (512) that `simp` stops with "maximum recursion depth has been reached"; 1024 passes.
-- Measured again for `DcUnmarshal` (229 directives, ENC logs 83, 84): the default fails at the `klabel` (174, 168), 1024 passes.
set_option maxRecDepth 1024 in
theorem dcd_e2e_reject_size_main : dcd_reject_size_stmt := by
  intro k hk hf s ra guard e0 e1 fp s2 hfp h2 R h_mem hguard hlen
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hguard hlen
  dsimp only
  have hz1 := rsp.toNat_lt_size; have hz2 := guard.toNat_lt_size; have hz3 := rcx.toNat_lt_size
  simp only [UInt64.size] at hz1 hz2 hz3
  kat hk DcUnmarshal 0
  kat hk DcUnmarshal 1
  kat hk DcUnmarshal 2
  kat hk DcUnmarshal 3
  apply load_step _ _ _ _ (Int.toBytes 8 guard.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk DcUnmarshal 4
  split
  case isTrue h =>
    exfalso
    rw [E2eScal.lea_cmp_be_false rsp.toBitVec _ guard.toBitVec _ _ 16 (by rfl) hguard] at h
    exact Bool.noConfusion h
  simp only [Effects.All]
  kat hk DcUnmarshal 5
  apply store_step_at _ _ (rsp.toBitVec - 8) _ _ _ fp _ _ (by dcaddr) (by ecancel) (by exact hfp)
  intro m1 H1
  simp only [Width.bytes, Width.bits] at H1
  kunfold
  kat hk DcUnmarshal 6
  kat hk DcUnmarshal 7
  kat hk DcUnmarshal 8
  apply store_step_at _ _ (rsp.toBitVec + 16) _ _ _ s2 _ _ (by dcaddr) (by ecancel) (by exact h2)
  intro m2 H2
  simp only [Width.bytes, Width.bits] at H2
  kunfold
  kat hk DcUnmarshal 9
  kat hk DcUnmarshal 10
  split
  case isFalse h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned] at h; omega
  simp only [Effects.All]
  klabel hk hf DcUnmarshal 174
  kat hk DcUnmarshal 174
  kat hk DcUnmarshal 175
  apply load_step _ _ _ _ (Int.toBytes 8 e0.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk DcUnmarshal 176
  apply load_step _ _ _ _ (Int.toBytes 8 e1.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk DcUnmarshal 177
  kat hk DcUnmarshal 178
  apply load_step_at _ _ (rsp.toBitVec - 8) _ _ (Int.toBytes 8 rbp.toBitVec.toInt) _ _ (by dcaddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk DcUnmarshal 179
  apply load_step_at _ _ rsp.toBitVec _ _ (Int.toBytes 8 ra.toBitVec.toInt) _ _ (by dcaddr) (by ecancel)
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
    | (apply UInt64.toBitVec_inj.mp; dcaddr)

-- Same measured cause and value as `ia_e2e_reject_size_main` (logs 123, 124).
set_option maxRecDepth 1024 in
theorem dcd_e2e_reject_offset_main : dcd_reject_offset_stmt := by
  intro k hk hf s ra guard e0 e1 fp s2 hfp h2 off hoff4 hoff R h_mem hguard hlen
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hguard hlen
  dsimp only
  have hz1 := rsp.toNat_lt_size; have hz2 := guard.toNat_lt_size; have hz3 := rcx.toNat_lt_size
  simp only [UInt64.size] at hz1 hz2 hz3
  kat hk DcUnmarshal 0
  kat hk DcUnmarshal 1
  kat hk DcUnmarshal 2
  kat hk DcUnmarshal 3
  apply load_step _ _ _ _ (Int.toBytes 8 guard.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk DcUnmarshal 4
  split
  case isTrue h =>
    exfalso
    rw [E2eScal.lea_cmp_be_false rsp.toBitVec _ guard.toBitVec _ _ 16 (by rfl) hguard] at h
    exact Bool.noConfusion h
  simp only [Effects.All]
  kat hk DcUnmarshal 5
  apply store_step_at _ _ (rsp.toBitVec - 8) _ _ _ fp _ _ (by dcaddr) (by ecancel) (by exact hfp)
  intro m1 H1
  simp only [Width.bytes, Width.bits] at H1
  kunfold
  kat hk DcUnmarshal 6
  kat hk DcUnmarshal 7
  kat hk DcUnmarshal 8
  apply store_step_at _ _ (rsp.toBitVec + 16) _ _ _ s2 _ _ (by dcaddr) (by ecancel) (by exact h2)
  intro m2 H2
  simp only [Width.bytes, Width.bits] at H2
  kunfold
  kat hk DcUnmarshal 9
  kat hk DcUnmarshal 10
  split
  case isTrue h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned] at h; omega
  simp only [Effects.All]
  kat hk DcUnmarshal 11
  apply load_step_at _ _ (rbx.toBitVec + 32) _ _ off _ _ (by dcaddr) (by ecancel) (by exact hoff4)
  kunfold
  kat hk DcUnmarshal 12
  kat hk DcUnmarshal 13
  kat hk DcUnmarshal 14
  kat hk DcUnmarshal 15
  split
  case isFalse h =>
    exfalso; apply hoff
    have hz : BitVec.zeroExtend 64 (BitVec.ofInt 32 (Int.ofBytes off)) - 36 = 0 := by
      simpa [CondCode.interp, StatusFlags.from_result] using h
    have hv : BitVec.ofInt 32 (Int.ofBytes off) = 36#32 := by
      have h1 := congrArg (· + (36 : BitVec 64)) hz
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
  klabel hk hf DcUnmarshal 168
  kat hk DcUnmarshal 168
  kat hk DcUnmarshal 169
  apply load_step _ _ _ _ (Int.toBytes 8 e0.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk DcUnmarshal 170
  apply load_step _ _ _ _ (Int.toBytes 8 e1.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk DcUnmarshal 171
  kat hk DcUnmarshal 172
  apply load_step_at _ _ (rsp.toBitVec - 8) _ _ (Int.toBytes 8 rbp.toBitVec.toInt) _ _ (by dcaddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk DcUnmarshal 173
  apply load_step_at _ _ rsp.toBitVec _ _ (Int.toBytes 8 ra.toBitVec.toInt) _ _ (by dcaddr) (by ecancel)
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
    | (apply UInt64.toBitVec_inj.mp; dcaddr)

end E2eDec
