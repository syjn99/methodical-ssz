import Prysm.Checkpoint.EncodeCoverFramed
import Prysm.Checkpoint.WitnessEncodeRejectLengthCover
import Machine.WitnessSplit

/-!
# Witness of `Encode.reject_length_cover_framed`: `len(Root) ≠ 32`, every capacity range

Same host, block, registers and instances as `Prysm/Checkpoint/WitnessEncodeRejectLengthCover.lean` (the `Prysm/Checkpoint/WitnessEncodeRejectLengthCover.lean` Host is the only one in
scope, because two `Host` instances in one file make instance resolution unfold both programs): len 30, cap 30 + n (n ≤ 64), nil `dst`, any `rl ≠ 32` (a Go value only for `rl ≤ 48`:
`Prysm.Checkpoint.witness_encode_reject_length_cover_recv`, `Prysm.Checkpoint.witness_encode_reject_length_cover_recv_bad`).
-/

open Machine Runtime Machine.Witness Prysm.Checkpoint.Code EthLib.Serialization.Ssz

namespace Prysm.Checkpoint.Witness.EncodeRejectLengthCoverFramed

open Prysm.Checkpoint.Witness.EncodeRejectLengthCover

set_option maxRecDepth 100000

set_option maxHeartbeats 64000000 in
/-- **Non-vacuity of `Encode.reject_length_cover_framed`**, len 30, cap 30 + n (n ≤ 64). -/
theorem runs (e8 : List UInt8) (he8 : e8.length = 8) (rl : UInt64) (hrl : rl ≠ 32) (n : Nat) (hn : n ≤ 64)
    (zmms : RegZmms) (flags : StatusFlags) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec (0 : UInt64).toBitVec ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0
        ∧ st.data.regs.rcx = 0 ∧ st.data.regs.rdi = 0x10e8 ∧ st.data.regs.rsi = 0x2b)
      ⟨cs0 e8 rl (pre30 ++ z n) 0x12428 30 (UInt64.ofNat (30 + n)) zmms flags, Host.addrOf 9⟩ := by
  have hc : (UInt64.ofNat (30 + n)).toNat = 30 + n := by simp; omega
  refine eventually_mono (Encode.reject_length_cover_framed 9 hk9 hf9 (z 8) e8 (w 48) (z 32) pre30 (z n) rfl he8 rfl rfl
    0x5000 rl 0x10e8 0x2b hrl (cs0 e8 rl (pre30 ++ z n) 0x12428 30 (UInt64.ofNat (30 + n)) zmms flags) 0 0 rfl (by simp only [cs0, hc]; simp [pre30])
    (z 8) (z 8) (z 8) (z 8) (z 8) (z 8) (z 8) (z 16) (z 16) (z 8) (z 40) (z 8)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    Std.ExtHashMap.emp 0 [] rfl bumpHeap 9000
    (by
      have H : Eq ((block e8 rl (pre30 ++ z n)).At (0x10000 : BitVec 64)) (mem e8 rl (pre30 ++ z n)) := rfl
      wit_split_n [he8, show pre30.length = 30 from rfl]
      rw [Std.ExtHashMap.sep_comm_l (Eq ((w 0x2b).At _)) (Eq ((z 9000).At _)),
        Std.ExtHashMap.sep_comm_l (Eq ((w 0x10e8).At _)) (Eq ((z 9000).At _))] at H
      have H2 := lift_heap H
      rw [at_app pre30 (z n) rfl (by simp [pre30]; omega)]
      simp only [cs0, w, nil_At_emp, List.nil_append, Std.ExtHashMap.sep_emp, Std.ExtHashMap.emp_sep,
        show pre30.length = 30 from rfl, ElfData.CheckpointAndEpoch.e2eErrBytesLength_addr, label_ebl,
        UInt64.toBitVec_ofNat, Int64.toBitVec_ofNat, Int64.toBitVec_add, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, BitVec.reduceSub,
        List.length_nil] at H2 ⊢
      generalize e8 = e8' at H2 ⊢
      simp only [Std.ExtHashMap.sep_assoc] at H2 ⊢
      simp only [Std.ExtHashMap.sep_comm, Std.ExtHashMap.sep_comm_l] at H2 ⊢
      exact H2)
    (by simp [cs0]) (by simp [cs0]) (by simp [cs0]; try omega) (by unfold maxAlloc; omega)
    (rt_growslice 100 hk100 hf100 _ 0)) ?_
  rintro st ⟨f1, f2, f3, f4, f5, f6, -⟩
  exact ⟨f1, f2, f3, f4, f5, f6⟩

set_option maxHeartbeats 64000000 in
/-- **Non-vacuity of `Encode.reject_length_cover_framed`** (nil dst). -/
theorem runs_nil (e8 : List UInt8) (he8 : e8.length = 8) (rl : UInt64) (hrl : rl ≠ 32)
    (zmms : RegZmms) (flags : StatusFlags) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec (0 : UInt64).toBitVec ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0
        ∧ st.data.regs.rcx = 0 ∧ st.data.regs.rdi = 0x10e8 ∧ st.data.regs.rsi = 0x2b)
      ⟨cs0 e8 rl [] 0 0 0 zmms flags, Host.addrOf 9⟩ := by
  refine eventually_mono (Encode.reject_length_cover_framed 9 hk9 hf9 (z 8) e8 (w 48) (z 32) [] [] rfl he8 rfl rfl
    0x5000 rl 0x10e8 0x2b hrl (cs0 e8 rl [] 0 0 0 zmms flags) 0 0 rfl rfl
    (z 8) (z 8) (z 8) (z 8) (z 8) (z 8) (z 8) (z 16) (z 16) (z 8) (z 40) (z 8)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    Std.ExtHashMap.emp 0 [] rfl bumpHeap 9000
    (by
      have H : Eq ((block e8 rl []).At (0x10000 : BitVec 64)) (mem e8 rl []) := rfl
      wit_split_n [he8]
      rw [Std.ExtHashMap.sep_comm_l (Eq ((w 0x2b).At _)) (Eq ((z 9000).At _)),
        Std.ExtHashMap.sep_comm_l (Eq ((w 0x10e8).At _)) (Eq ((z 9000).At _))] at H
      have H2 := lift_heap H
      simp only [cs0, w, nil_At_emp, List.nil_append, Std.ExtHashMap.sep_emp, Std.ExtHashMap.emp_sep,
        show pre30.length = 30 from rfl, ElfData.CheckpointAndEpoch.e2eErrBytesLength_addr, label_ebl,
        UInt64.toBitVec_ofNat, Int64.toBitVec_ofNat, Int64.toBitVec_add, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, BitVec.reduceSub,
        List.length_nil] at H2 ⊢
      generalize e8 = e8' at H2 ⊢
      simp only [Std.ExtHashMap.sep_assoc] at H2 ⊢
      simp only [Std.ExtHashMap.sep_comm, Std.ExtHashMap.sep_comm_l] at H2 ⊢
      exact H2)
    (by simp [cs0]) (by simp [cs0]) (by simp [cs0]) (by unfold maxAlloc; omega)
    (rt_growslice 100 hk100 hf100 _ 0)) ?_
  rintro st ⟨f1, f2, f3, f4, f5, f6, -⟩
  exact ⟨f1, f2, f3, f4, f5, f6⟩

/-- cap = len, len + 3 (first growslice, then the reject), len + 8, len + 40 (no growth); nil dst; rl = 31, 0, 33, 48. -/
example (z' : RegZmms) (f : StatusFlags) := runs (Int.toBytes 8 7) rfl 31 (by decide) 0 (by decide) z' f
example (z' : RegZmms) (f : StatusFlags) := runs (Int.toBytes 8 7) rfl 0 (by decide) 3 (by decide) z' f
example (z' : RegZmms) (f : StatusFlags) := runs (Int.toBytes 8 7) rfl 33 (by decide) 8 (by decide) z' f
example (z' : RegZmms) (f : StatusFlags) := runs (Int.toBytes 8 7) rfl 48 (by decide) 40 (by decide) z' f
example (z' : RegZmms) (f : StatusFlags) := runs_nil (Int.toBytes 8 7) rfl 31 (by decide) z' f

end Prysm.Checkpoint.Witness.EncodeRejectLengthCoverFramed
