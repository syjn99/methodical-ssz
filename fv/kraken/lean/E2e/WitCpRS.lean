import E2e.WitCpR
import E2e.CpSpecK

/-!
# Witness of `cp_e2e_reject_size_spec` on concrete input arrays

Same Host and memory as `E2e.WitCpR`. The input arrays are concrete (`39`, `41`
and `0` bytes of `0x11`); EthLib rejects each (`∃ e, deserialize … = .error e`)
and the machine code returns the two `ssz.ErrSize` words.
-/

open Machine Runtime TestTarget Machine.Witness E2e E2e.Code EthLib.Serialization.Ssz

namespace E2e.WitCpR

set_option maxHeartbeats 4000000 in
/-- **Non-vacuity of `cp_e2e_reject_size_spec`** on `Array.replicate n 0x11`, `n ≠ 40`. -/
theorem cp_reject_spec_runs (n : Nat) (hn : n ≠ 40) (hn64 : n < 2 ^ 64) (zmms : RegZmms) (flags : StatusFlags) :
    (∃ e, deserialize prysmCpDesc (Array.replicate n (0x11 : UInt8)) = .error e) ∧
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec (0 : UInt64).toBitVec ∧ st.data.regs.rax = 0x10e8
        ∧ st.data.regs.rbx = 0x2a)
      ⟨cs0 (UInt64.ofNat n) zmms flags, Host.addrOf 1⟩ :=
  let h := cp_e2e_reject_size_spec 1 hk1 hf1 (Array.replicate n (0x11 : UInt8)) (by simpa using hn)
    (cs0 (UInt64.ofNat n) zmms flags) 0 0 0x10e8 0x2a (z 8) (z 8) rfl rfl R0
    (by
      have H : Eq (block.At (0x10000 : BitVec 64)) mem := rfl
      wit_split []
      simp only [cs0, R0, w, E2e.Data.e2eErrSize_addr, label_err, UInt64.toBitVec_ofNat, Int64.toBitVec_ofNat,
        Int64.toBitVec_add, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, BitVec.reduceSub] at H ⊢
      simp only [Std.ExtHashMap.sep_assoc] at H ⊢
      simp only [Std.ExtHashMap.sep_comm, Std.ExtHashMap.sep_comm_l] at H ⊢
      exact H)
    (by simp [cs0]) (by simp [cs0]; try omega)
  ⟨h.1, eventually_mono h.2 (fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩)⟩

example (z' : RegZmms) (f : StatusFlags) := cp_reject_spec_runs 39 (by decide) (by decide) z' f
example (z' : RegZmms) (f : StatusFlags) := cp_reject_spec_runs 41 (by decide) (by decide) z' f
example (z' : RegZmms) (f : StatusFlags) := cp_reject_spec_runs 0 (by decide) (by decide) z' f

end E2e.WitCpR
