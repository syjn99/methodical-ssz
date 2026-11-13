import Machine.Step
import Machine.Labels
import Machine.Bytes
import Prysm.Checkpoint.DecodeRejectSize
import Codec.StackGuard
import Prysm.IndexedAttestation.Statements
import Prysm.IndexedAttestation.AddressTactic

/-!
# `(*v1alpha1.IndexedAttestation).UnmarshalSSZ`: size reject and offset reject

- `Decode.reject_size : Decode.reject_size_statement`: directives 2–4 (large-frame guard `lea -0x30(%rsp),%r12`, closed
  with `Codec.lea_cmp_be_false`, N = 48), 5–8 prologue (`sub $0xa8`, rbx spill to rsp + 16), 9–10
  `cmp $0xe4,%rcx; jb L_268` taken, `L_268` (137), the two loads of `ssz.ErrSize` (138–139), epilogue 140–142.
- `Decode.reject_offset : Decode.reject_offset_statement`: 9–10 not taken, 11 `mov (%rbx),%edx` (32-bit load of `off`),
  16–17 `cmp $0xe4,%rdx; jne L_251` taken, `L_251` (131), the two loads of `ssz.ErrInvalidVariableOffset` (132–133),
  epilogue 134–136.
After the split of this module, the other reject path is in `Prysm/IndexedAttestation/DecodeRejectOffset.lean`.
-/

open Machine Runtime Prysm.IndexedAttestation.Code
variable [Host]

namespace Prysm.IndexedAttestation


-- Measured cause: `kat` unfolds the 279-directive program literal `unmarshalSSZ` with `simp`; at the
-- default `maxRecDepth` (512) that `simp` stops with "maximum recursion depth has been reached"; 1024 passes.
set_option maxRecDepth 1024 in
theorem Decode.reject_size : Decode.reject_size_statement := by
  intro k hk hf s ra guard e0 e1 fp s2 hfp h2 R h_mem hguard hlen
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hguard hlen
  dsimp only
  have hz1 := rsp.toNat_lt_size; have hz2 := guard.toNat_lt_size; have hz3 := rcx.toNat_lt_size
  simp only [UInt64.size] at hz1 hz2 hz3
  kat hk unmarshalSSZ 0
  kat hk unmarshalSSZ 1
  kat hk unmarshalSSZ 2
  kat hk unmarshalSSZ 3
  apply load_step _ _ _ _ (Int.toBytes 8 guard.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk unmarshalSSZ 4
  split
  case isTrue h =>
    exfalso
    rw [Codec.lea_cmp_be_false rsp.toBitVec _ guard.toBitVec _ _ 48 (by rfl) hguard] at h
    exact Bool.noConfusion h
  simp only [Effects.All]
  kat hk unmarshalSSZ 5
  apply store_step_at _ _ (rsp.toBitVec - 8) _ _ _ fp _ _ (by iaaddr) (by ecancel) (by exact hfp)
  intro m1 H1
  simp only [Width.bytes, Width.bits] at H1
  kunfold
  kat hk unmarshalSSZ 6
  kat hk unmarshalSSZ 7
  kat hk unmarshalSSZ 8
  apply store_step_at _ _ (rsp.toBitVec + 16) _ _ _ s2 _ _ (by iaaddr) (by ecancel) (by exact h2)
  intro m2 H2
  simp only [Width.bytes, Width.bits] at H2
  kunfold
  kat hk unmarshalSSZ 9
  kat hk unmarshalSSZ 10
  split
  case isFalse h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned] at h; omega
  simp only [Effects.All]
  klabel hk hf unmarshalSSZ 137
  kat hk unmarshalSSZ 137
  kat hk unmarshalSSZ 138
  apply load_step _ _ _ _ (Int.toBytes 8 e0.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk unmarshalSSZ 139
  apply load_step _ _ _ _ (Int.toBytes 8 e1.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk unmarshalSSZ 140
  kat hk unmarshalSSZ 141
  apply load_step_at _ _ (rsp.toBitVec - 8) _ _ (Int.toBytes 8 rbp.toBitVec.toInt) _ _ (by iaaddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk unmarshalSSZ 142
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

end Prysm.IndexedAttestation
