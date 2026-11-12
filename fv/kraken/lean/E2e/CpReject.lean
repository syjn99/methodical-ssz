import Machine.Step
import Machine.Labels
import Machine.Bytes
import E2e.Code
import E2e.Data

/-!
# Real Prysm `(*v1alpha1.Checkpoint).UnmarshalSSZ`: size reject and the unreachable Epoch-error path

`cp_e2e_reject_size_main` (`len(buf) ≠ 40`, Go source `return ssz.ErrSize`):
directives 2–7 (guard, prologue, rbx spill), 9–10 `cmp $0x28,%rcx; jne L_16b`
taken, 91 `L_16b`, 92–93 load the two words of `ssz.ErrSize`, 94–96 epilogue.
The address is the data item `E2e.Data.e2eErrSize_addr` (its symbol checked
against the ELF by `link/check.py` (f)); the two words `e0`, `e1` are the
global's value after package init (premise; `e0 ≠ 0` there, so the error is
non-nil).

`cp_e2e_epoch_err_unreachable` (`unreachable_mc` row): after the Epoch call
(directive 18) with `rax = 0` the code jumps to `L_b4` (directive 47) with the
registers and memory unchanged, so directives 20–46 (`fmt.errorf("Epoch: %w")`,
the `runtime.newobject` fallback) are not executed. The Epoch function spec
`EpUAccC` (proved by `ep_uacc_holds`) gives `rax = 0` for the call with
`rcx = 8` that directive 15 sets; with `len(buf) = 40` the path to the error
return is therefore absent from every execution (`cp_e2e_accept_main` passes
through exactly this step). The Go-source reject site stays in the list; this
row does not count as reject coverage.
-/

open Machine TestTarget E2e.Code
variable [Host]

namespace E2e

theorem errSize_addr_eq : E2e.Data.e2eErrSize_addr = (label "ssz.ErrSize").toBitVec := rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem cp_e2e_reject_size_main (k : Nat) (hk : CpUnmarshal.IsInfixAt Host.prog k)
    (hf : LabelsFresh CpUnmarshal k)
    (s : MachineData) (ra guard e0 e1 : UInt64) (fp s2 : List UInt8) (hfp : fp.length = 8) (h2 : s2.length = 8)
    (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At E2e.Data.e2eErrSize_addr)
      ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrSize" + 8).toBitVec) ⋆ R)
    (hguard : guard.toNat < s.regs.rsp.toNat) (hlen : s.regs.rcx ≠ 40) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = e0 ∧ st.data.regs.rbx = e1
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14
        ∧ (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At E2e.Data.e2eErrSize_addr)
          ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrSize" + 8).toBitVec) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only [errSize_addr_eq] at h_mem hguard hlen ⊢
  have := rsp.toNat_lt_size; have := guard.toNat_lt_size; have := rcx.toNat_lt_size; simp only [UInt64.size] at *
  kat hk CpUnmarshal 0
  kat hk CpUnmarshal 1
  kat hk CpUnmarshal 2
  apply load_step _ _ _ _ (Int.toBytes 8 guard.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk CpUnmarshal 3
  split
  · rename_i h; exfalso
    simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned] at h
    rcases h with h | h
    · apply h; omega
    · have := congrArg BitVec.toNat h; simp [BitVec.toNat_sub] at this; omega
  simp only [Effects.All]
  kat hk CpUnmarshal 4
  apply store_step_at _ _ (rsp.toBitVec - 8) _ _ _ fp _ _ (by bv_omega) (by ecancel) (by exact hfp)
  intro m1 H1
  simp only [Width.bytes, Width.bits] at H1
  kunfold
  kat hk CpUnmarshal 5
  kat hk CpUnmarshal 6
  kat hk CpUnmarshal 7
  apply store_step_at _ _ (rsp.toBitVec + 16) _ _ _ s2 _ _ (by bv_omega) (by ecancel) (by exact h2)
  intro m2 H2
  simp only [Width.bytes, Width.bits] at H2
  kunfold
  kat hk CpUnmarshal 8
  kat hk CpUnmarshal 9
  kat hk CpUnmarshal 10
  split
  case isFalse h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
    apply hlen; apply UInt64.toBitVec_inj.mp; apply BitVec.eq_of_toNat_eq
    have := congrArg BitVec.toNat h; simp [BitVec.toNat_sub] at this ⊢; omega
  simp only [Effects.All]
  klabel hk hf CpUnmarshal 91
  kat hk CpUnmarshal 91
  kat hk CpUnmarshal 92
  apply load_step _ _ _ _ (Int.toBytes 8 e0.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk CpUnmarshal 93
  apply load_step _ _ _ _ (Int.toBytes 8 e1.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk CpUnmarshal 94
  kat hk CpUnmarshal 95
  rw [show (80 : BitVec 64) + (rsp.toBitVec - 8#64 - 80) = rsp.toBitVec - 8 by bv_omega]
  apply load_step _ _ _ _ (Int.toBytes 8 rbp.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk CpUnmarshal 96
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

/-- **`unreachable_mc`: the `fmt.errorf("Epoch: %w")` path.** From the return of the
Epoch call (directive 18) with `rax = 0`, the code reaches `L_b4` (directive 47)
with registers and memory unchanged: directives 20–46 are not executed. -/
theorem cp_e2e_epoch_err_unreachable (k : Nat) (hk : CpUnmarshal.IsInfixAt Host.prog k)
    (hf : LabelsFresh CpUnmarshal k) (s : MachineData) (h0 : s.regs.rax = 0) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 47) ∧ st.data.regs = s.regs ∧ st.data.dmem = s.dmem)
      ⟨s, Host.addrOf (k + 18)⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h0 ⊢
  subst h0
  kat hk CpUnmarshal 18
  intro _
  kat hk CpUnmarshal 19
  split
  case isFalse h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
  simp only [Effects.All]
  klabel hk hf CpUnmarshal 47
  exact Eventually.done _ ⟨rfl, rfl, rfl⟩

end E2e
