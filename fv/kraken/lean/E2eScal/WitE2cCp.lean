import E2eScal.Gen6CpEnc
import Runtime.CopyModel
import Machine.WitnessHost

/-!
# Witness of `cp_g6e_fast` (Checkpoint encoder fast path, generated theorem; unit E2-C)

Emitted by the unit's evidence tool `e2cemit.py` (not the generator) from the committed statement text and
the IR; then built and kernel-checked. Host: the real Go 1.26.10 `MarshalSSZTo` (index 0) and `RtCopy` (index 91, `rt_memmove`, S = 0).
One memory block at `0x10000`: guard word (r14 = 0xfff0); the receiver at 0x10008 (`prysm/ir/ir-mainnet.json`
gc amd64 layout, 72 bytes; byte fields = (pointer, n, n) with the n bytes after the receiver; unexported tail
zero); the stack window (rsp = 0x100e8: rsp − 120 … rsp + 23); `dst` at 0x10100: the prefix, the old output
bytes, the spare capacity. Frame `R`: every byte of the block that no premise chunk names, and the spare.
Two instances: empty prefix with `cap = 40`; prefix `[0xaa, 0xbb, 0xcc]` with 5 spare bytes. For every
field value of the stated lengths every premise of `cp_g6e_fast` holds (non-vacuity of the fast path).
-/

open Machine Runtime TestTarget Machine.Witness E2eScal Codec E2eScal.Gen6Enc Prysm.Checkpoint.Code

namespace E2eScal.WitE2cCp

set_option maxRecDepth 100000

def P : Program := marshalSSZTo ++ RtCopy

theorem P_len : P.length = 117 := by rfl

instance host : Host := mkHost P (by rw [P_len]; decide)

theorem hk0 : marshalSSZTo.IsInfixAt Host.prog 0 := infixAt_of [] RtCopy (by simp [Host.prog, mkHost, P]) rfl
theorem hkR : RtCopy.IsInfixAt Host.prog 91 := infixAt_of marshalSSZTo [] (by simp [Host.prog, mkHost, P]) (by rfl)
theorem hf0 : LabelsFresh marshalSSZTo 0 := fun i hi => absurd hi (Nat.not_lt_zero _)
theorem hfR : LabelsFresh RtCopy 91 := labelsFresh_of (by decide)

abbrev z (k : Nat) : List UInt8 := List.replicate k 0
abbrev w (v : UInt64) : List UInt8 := Int.toBytes 8 v.toBitVec.toInt

def block (v0 b1 pre spare : List UInt8) : List UInt8 :=
  (w 0) ++ ((z 8) ++ (v0 ++ ((w 0x10050) ++ ((Int.toBytes 8 32) ++ ((w 32) ++ ((z 32) ++ (b1 ++ ((z 8) ++ ((z 48) ++ ((z 16) ++ ((z 16) ++ ((z 8) ++ ((z 8) ++ ((z 8) ++ ((z 8) ++ ((w 0) ++ ((z 8) ++ ((z 8) ++ (pre ++ ((z 8) ++ ((z 32) ++ (spare))))))))))))))))))))))

def mem (v0 b1 pre spare : List UInt8) : DataMem := (block v0 b1 pre spare).At (0x10000 : BitVec 64)

def cs0 (v0 b1 pre spare : List UInt8) (zmms : RegZmms) (flags : StatusFlags) : MachineData :=
  ⟨⟨0x10008, 0x10100, UInt64.ofNat pre.length, 0, 0, UInt64.ofNat (pre.length + 40 + spare.length), 0x100e8, 0,
    0, 0, 0, 0, 0, 0, 0xfff0, 0⟩, zmms, flags, mem v0 b1 pre spare⟩

set_option maxHeartbeats 16000000 in
/-- Empty prefix, `cap = 40`. -/
theorem cp_e2c_wit_empty (v0 : List UInt8) (b1 : List UInt8)
    (h_v0 : v0.length = 8) (h_b1 : b1.length = 32)
    (zmms : RegZmms) (flags : StatusFlags) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec (0 : UInt64).toBitVec ∧ st.data.regs.rax = 0x10100
        ∧ st.data.regs.rdi = 0 ∧ st.data.regs.rsi = 0)
      ⟨cs0 v0 b1 [] [] zmms flags, Host.addrOf 0⟩ :=
  eventually_mono (cp_g6e_fast 0 hk0 hf0 (z 8) v0 (w 32) b1 [] (z 8) (z 32) rfl h_v0 rfl h_b1 rfl rfl (0x10050 : BitVec 64) (cs0 v0 b1 [] [] zmms flags) 0 0 rfl (z 8) (z 8) (z 8) (z 8) (z 8) (z 16) (z 16) (z 8) rfl rfl rfl rfl rfl rfl rfl rfl (Eq ((z 32).At (0x10030 : BitVec 64)) ⋆ Eq ((z 48).At (0x10078 : BitVec 64)) ⋆ Eq ((z 8).At (0x100f0 : BitVec 64))) 0 [] rfl 
    (by
      have H : Eq ((block v0 b1 [] []).At (0x10000 : BitVec 64))
        (mem v0 b1 [] []) := rfl
      wit_split [h_v0, h_b1]
      simp only [cs0, w, nil_At_emp, Std.ExtHashMap.sep_emp, Std.ExtHashMap.emp_sep, UInt64.toBitVec_ofNat,
        BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, BitVec.reduceSub, List.length_nil, List.length_cons,
        List.length_replicate, show (UInt64.ofNat 0).toBitVec = 0#64 from rfl] at H ⊢
      simp only [Std.ExtHashMap.sep_assoc] at H ⊢
      simp only [Std.ExtHashMap.sep_comm, Std.ExtHashMap.sep_comm_l] at H ⊢
      exact H)
    (by simp [cs0]) (by simp [cs0]) (by simp [cs0]) (by simp [cs0]) (rt_memmove 91 hkR hfR 0))
    (fun _ h => ⟨h.1, h.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1⟩)

set_option maxHeartbeats 16000000 in
/-- Prefix `[0xaa, 0xbb, 0xcc]`, 5 spare bytes (`cap = len + 45`). -/
theorem cp_e2c_wit_prefix (v0 : List UInt8) (b1 : List UInt8)
    (h_v0 : v0.length = 8) (h_b1 : b1.length = 32)
    (zmms : RegZmms) (flags : StatusFlags) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec (0 : UInt64).toBitVec ∧ st.data.regs.rax = 0x10100
        ∧ st.data.regs.rdi = 0 ∧ st.data.regs.rsi = 0)
      ⟨cs0 v0 b1 [0xaa, 0xbb, 0xcc] (z 5) zmms flags, Host.addrOf 0⟩ :=
  eventually_mono (cp_g6e_fast 0 hk0 hf0 (z 8) v0 (w 32) b1 [0xaa, 0xbb, 0xcc] (z 8) (z 32) rfl h_v0 rfl h_b1 rfl rfl (0x10050 : BitVec 64) (cs0 v0 b1 [0xaa, 0xbb, 0xcc] (z 5) zmms flags) 0 0 rfl (z 8) (z 8) (z 8) (z 8) (z 8) (z 16) (z 16) (z 8) rfl rfl rfl rfl rfl rfl rfl rfl (Eq ((z 32).At (0x10030 : BitVec 64)) ⋆ Eq ((z 48).At (0x10078 : BitVec 64)) ⋆ Eq ((z 8).At (0x100f0 : BitVec 64)) ⋆ Eq ((z 5).At (0x1012b : BitVec 64))) 0 [] rfl 
    (by
      have H : Eq ((block v0 b1 [0xaa, 0xbb, 0xcc] (z 5)).At (0x10000 : BitVec 64))
        (mem v0 b1 [0xaa, 0xbb, 0xcc] (z 5)) := rfl
      wit_split [h_v0, h_b1]
      simp only [cs0, w, nil_At_emp, Std.ExtHashMap.sep_emp, Std.ExtHashMap.emp_sep, UInt64.toBitVec_ofNat,
        BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, BitVec.reduceSub, List.length_nil, List.length_cons,
        List.length_replicate, show (UInt64.ofNat 3).toBitVec = 3#64 from rfl] at H ⊢
      simp only [Std.ExtHashMap.sep_assoc] at H ⊢
      simp only [Std.ExtHashMap.sep_comm, Std.ExtHashMap.sep_comm_l] at H ⊢
      exact H)
    (by simp [cs0]) (by simp [cs0]) (by simp [cs0]) (by simp [cs0]) (rt_memmove 91 hkR hfR 0))
    (fun _ h => ⟨h.1, h.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1⟩)

example (z' : RegZmms) (f : StatusFlags) :=
  cp_e2c_wit_empty (Int.toBytes 8 0) (List.replicate 32 0) (by decide) rfl z' f
example (z' : RegZmms) (f : StatusFlags) :=
  cp_e2c_wit_prefix (Int.toBytes 8 0x0123456789abcdef) (List.replicate 32 0x5a) (by decide) rfl z' f
example (z' : RegZmms) (f : StatusFlags) :=
  cp_e2c_wit_prefix (Int.toBytes 8 (2 ^ 64 - 1)) (List.replicate 32 0xff) (by decide) rfl z' f

end E2eScal.WitE2cCp
