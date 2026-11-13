import Machine.Step
import Machine.Labels
import Machine.Bytes
import Prysm.AttestationData.Code
import Prysm.ElfData.PrysmTarget
import Prysm.Checkpoint.DecodeRejectSize

/-!
# Real Prysm `(*v1alpha1.AttestationData).UnmarshalSSZ`: size reject and the four unreachable error wraps

`Decode.reject_size` (`len(buf) ≠ 128`, Go source `return ssz.ErrSize`): directives
2–7 (guard, prologue, rbx spill), 9–10 `cmp $0x80,%rcx; jne L_3ad` taken, 226 `L_3ad`,
227–228 load the two words of `ssz.ErrSize` (`ElfData.PrysmTarget.sszErrSize_addr`, the same ELF symbol
as the Checkpoint decoder's; `attestation_data_link.py` asserts the operand), 229–231 epilogue. The two words
`e0`, `e1` are the global's value after package init (premise, as in `Prysm.Checkpoint.Decode.reject_size`).

**`unreachable_mc` rows** (own column, never reject coverage): after each callee returns with
`rax = 0` the code jumps over its `fmt.errorf` wrap with registers and memory unchanged:
Slot (directive 18 → 47, skips 20–46, "Slot: %w"), CommitteeIndex (56 → 85, skips 58–84,
"CommitteeIndex: %w"), Source (143 → 172, skips 145–171, "Source: %w"), Target (193 → 222,
skips 195–221, "Target: %w"). `Prysm.Slot.Decode.accept_function_spec`, `Prysm.CommitteeIndex.Decode.accept_function_spec` and `Prysm.Checkpoint.Decode.accept_function_spec` give `rax = 0` for the calls
that `Decode.accept` makes with `len(buf) = 128` (rcx = 8, 8, 40, 40); that theorem
passes through exactly these steps, so the wraps are absent from every execution with a
128-byte input.
After the split of this module, the four unreachable error wraps are in `Prysm/AttestationData/DecodeErrorWrapsUnreachable.lean`.
-/

open Machine Prysm.AttestationData.Code
variable [Host]

namespace Prysm.AttestationData

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem Decode.reject_size (k : Nat) (hk : unmarshalSSZ.IsInfixAt Host.prog k)
    (hf : LabelsFresh unmarshalSSZ k)
    (s : MachineData) (ra guard e0 e1 : UInt64) (fp s2 : List UInt8) (hfp : fp.length = 8) (h2 : s2.length = 8)
    (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At ElfData.PrysmTarget.sszErrSize_addr)
      ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrSize" + 8).toBitVec) ⋆ R)
    (hguard : guard.toNat < s.regs.rsp.toNat) (hlen : s.regs.rcx ≠ 128) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = e0 ∧ st.data.regs.rbx = e1
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14
        ∧ (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At ElfData.PrysmTarget.sszErrSize_addr)
          ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrSize" + 8).toBitVec) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only [ElfData.PrysmTarget.sszErrSize_addr_eq] at h_mem hguard hlen ⊢
  have := rsp.toNat_lt_size; have := guard.toNat_lt_size; have := rcx.toNat_lt_size; simp only [UInt64.size] at *
  step_directive hk unmarshalSSZ 0
  step_directive hk unmarshalSSZ 1
  step_directive hk unmarshalSSZ 2
  apply load_step _ _ _ _ (Int.toBytes 8 guard.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  unfold_step
  step_directive hk unmarshalSSZ 3
  split
  · rename_i h; exfalso
    simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned] at h
    rcases h with h | h
    · apply h; omega
    · have := congrArg BitVec.toNat h; simp [BitVec.toNat_sub] at this; omega
  simp only [Effects.All]
  step_directive hk unmarshalSSZ 4
  apply store_step_at _ _ (rsp.toBitVec - 8) _ _ _ fp _ _ (by bv_omega) (by ecancel) (by exact hfp)
  intro m1 H1
  simp only [Width.bytes, Width.bits] at H1
  unfold_step
  step_directive hk unmarshalSSZ 5
  step_directive hk unmarshalSSZ 6
  step_directive hk unmarshalSSZ 7
  apply store_step_at _ _ (rsp.toBitVec + 16) _ _ _ s2 _ _ (by bv_omega) (by ecancel) (by exact h2)
  intro m2 H2
  simp only [Width.bytes, Width.bits] at H2
  unfold_step
  step_directive hk unmarshalSSZ 8
  step_directive hk unmarshalSSZ 9
  step_directive hk unmarshalSSZ 10
  split
  case isFalse h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
    apply hlen; apply UInt64.toBitVec_inj.mp; apply BitVec.eq_of_toNat_eq
    have := congrArg BitVec.toNat h; simp [BitVec.toNat_sub] at this ⊢; omega
  simp only [Effects.All]
  label_address hk hf unmarshalSSZ 226
  step_directive hk unmarshalSSZ 226
  step_directive hk unmarshalSSZ 227
  apply load_step _ _ _ _ (Int.toBytes 8 e0.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  unfold_step
  step_directive hk unmarshalSSZ 228
  apply load_step _ _ _ _ (Int.toBytes 8 e1.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  unfold_step
  step_directive hk unmarshalSSZ 229
  step_directive hk unmarshalSSZ 230
  rw [show (112 : BitVec 64) + (rsp.toBitVec - 8#64 - 112) = rsp.toBitVec - 8 by bv_omega]
  apply load_step _ _ _ _ (Int.toBytes 8 rbp.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  unfold_step
  step_directive hk unmarshalSSZ 231
  rw [show rsp.toBitVec - 8 + 8#64 = rsp.toBitVec by bv_omega]
  apply load_step _ _ _ _ (Int.toBytes 8 ra.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  unfold_step
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


end Prysm.AttestationData
