import Machine.Step
import Machine.Labels
import Machine.Bytes
import Prysm.Checkpoint.DecodeRejectSize
import Codec.StackGuard
import Prysm.IndexedAttestation.Statements
import Prysm.IndexedAttestation.AddressTactic
import Prysm.IndexedAttestation.DecodeRejectSize

/-!
# `(*v1alpha1.IndexedAttestation).UnmarshalSSZ`: offset reject

- `Decode.reject_offset : Decode.reject_offset_statement`: 9–10 not taken, 11 `mov (%rbx),%edx` (32-bit load of `off`),
  16–17 `cmp $0xe4,%rdx; jne L_251` taken, `L_251` (131), the two loads of `ssz.ErrInvalidVariableOffset` (132–133),
  epilogue 134–136. The size reject is in `Prysm/IndexedAttestation/DecodeRejectSize.lean`.
-/

open Machine Runtime Prysm.IndexedAttestation.Code
variable [Host]

namespace Prysm.IndexedAttestation

-- Same measured cause and value as `Decode.reject_size`.
set_option maxRecDepth 1024 in
theorem Decode.reject_offset : Decode.reject_offset_statement := by
  intro k hk hf s ra guard e0 e1 fp s2 hfp h2 off hoff4 hoff R h_mem hguard hlen
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hguard hlen
  dsimp only
  have hz1 := rsp.toNat_lt_size; have hz2 := guard.toNat_lt_size; have hz3 := rcx.toNat_lt_size
  simp only [UInt64.size] at hz1 hz2 hz3
  step_directive hk unmarshalSSZ 0
  step_directive hk unmarshalSSZ 1
  step_directive hk unmarshalSSZ 2
  step_directive hk unmarshalSSZ 3
  apply load_step _ _ _ _ (Int.toBytes 8 guard.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  unfold_step
  step_directive hk unmarshalSSZ 4
  split
  case isTrue h =>
    exfalso
    rw [Codec.lea_cmp_be_false rsp.toBitVec _ guard.toBitVec _ _ 48 (by rfl) hguard] at h
    exact Bool.noConfusion h
  simp only [Effects.All]
  step_directive hk unmarshalSSZ 5
  apply store_step_at _ _ (rsp.toBitVec - 8) _ _ _ fp _ _ (by indexed_attestation_addr) (by ecancel) (by exact hfp)
  intro m1 H1
  simp only [Width.bytes, Width.bits] at H1
  unfold_step
  step_directive hk unmarshalSSZ 6
  step_directive hk unmarshalSSZ 7
  step_directive hk unmarshalSSZ 8
  apply store_step_at _ _ (rsp.toBitVec + 16) _ _ _ s2 _ _ (by indexed_attestation_addr) (by ecancel) (by exact h2)
  intro m2 H2
  simp only [Width.bytes, Width.bits] at H2
  unfold_step
  step_directive hk unmarshalSSZ 9
  step_directive hk unmarshalSSZ 10
  split
  case isTrue h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned] at h; omega
  simp only [Effects.All]
  step_directive hk unmarshalSSZ 11
  apply load_step _ _ _ _ off _ _ (by ecancel) (by exact hoff4)
  unfold_step
  step_directive hk unmarshalSSZ 12
  step_directive hk unmarshalSSZ 13
  step_directive hk unmarshalSSZ 14
  step_directive hk unmarshalSSZ 15
  step_directive hk unmarshalSSZ 16
  step_directive hk unmarshalSSZ 17
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
  label_address hk hf unmarshalSSZ 131
  step_directive hk unmarshalSSZ 131
  step_directive hk unmarshalSSZ 132
  apply load_step _ _ _ _ (Int.toBytes 8 e0.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  unfold_step
  step_directive hk unmarshalSSZ 133
  apply load_step _ _ _ _ (Int.toBytes 8 e1.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  unfold_step
  step_directive hk unmarshalSSZ 134
  step_directive hk unmarshalSSZ 135
  apply load_step_at _ _ (rsp.toBitVec - 8) _ _ (Int.toBytes 8 rbp.toBitVec.toInt) _ _ (by indexed_attestation_addr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  unfold_step
  step_directive hk unmarshalSSZ 136
  apply load_step_at _ _ rsp.toBitVec _ _ (Int.toBytes 8 ra.toBitVec.toInt) _ _ (by indexed_attestation_addr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  unfold_step
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
    | (apply UInt64.toBitVec_inj.mp; indexed_attestation_addr)

end Prysm.IndexedAttestation
