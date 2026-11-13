import Prysm.PowBlock.GeneratedEncodeFastPath
import Runtime.CopyModel
import Machine.WitnessHost

/-!
# Witness of `Encode.generated_fast` (PowBlock encoder fast path, generated theorem)

Emitted by the unit's evidence tool `e2cemit.py` (not the generator) from the committed statement text and
the IR; then built and kernel-checked. Host: the real Go 1.26.10 `MarshalSSZTo` (index 0) and `RtCopy` (index 153, `rt_memmove`, S = 0).
One memory block at `0x10000`: guard word (r14 = 0xfff0); the receiver at 0x10008 (`prysm/ir/ir-mainnet.json`
gc amd64 layout, 72 bytes; byte fields = (pointer, n, n) with the n bytes after the receiver; unexported tail
zero); the stack window (rsp = 0x10110: rsp − 96 … rsp + 23); `dst` at 0x10128: the prefix, the old output
bytes, the spare capacity. Frame `R`: every byte of the block that no premise chunk names, and the spare.
Two instances: empty prefix with `cap = 96`; prefix `[0xaa, 0xbb, 0xcc]` with 5 spare bytes. For every
field value of the stated lengths every premise of `Encode.generated_fast` holds (non-vacuity of the fast path).
-/

open Machine Runtime Machine.Witness Codec Prysm.PowBlock.Code

namespace Prysm.PowBlock.Witness.GeneratedEncodeFastPath

set_option maxRecDepth 100000

def P : Program := marshalSSZTo ++ RtCopy

theorem P_len : P.length = 179 := by rfl

instance host : Host := mkHost P (by rw [P_len]; decide)

theorem hk0 : marshalSSZTo.IsInfixAt Host.prog 0 := infixAt_of [] RtCopy (by simp [Host.prog, mkHost, P]) rfl
theorem hkR : RtCopy.IsInfixAt Host.prog 153 := infixAt_of marshalSSZTo [] (by simp [Host.prog, mkHost, P]) (by rfl)
theorem hf0 : LabelsFresh marshalSSZTo 0 := fun i hi => absurd hi (Nat.not_lt_zero _)
theorem hfR : LabelsFresh RtCopy 153 := labelsFresh_of (by decide)

abbrev z (k : Nat) : List UInt8 := List.replicate k 0
abbrev w (v : UInt64) : List UInt8 := Int.toBytes 8 v.toBitVec.toInt

def block (b0 b1 b2 pre spare : List UInt8) : List UInt8 :=
  (w 0) ++ ((w 0x10050) ++ ((Int.toBytes 8 32) ++ ((w 32) ++ ((w 0x10070) ++ ((Int.toBytes 8 32) ++ ((w 32) ++ ((w 0x10090) ++ ((Int.toBytes 8 32) ++ ((w 32) ++ (b0 ++ (b1 ++ (b2 ++ ((z 8) ++ ((z 48) ++ ((z 8) ++ ((z 8) ++ ((z 8) ++ ((z 8) ++ ((z 8) ++ ((w 0) ++ ((z 8) ++ ((z 8) ++ (pre ++ ((z 32) ++ ((z 32) ++ ((z 32) ++ (spare)))))))))))))))))))))))))))

def mem (b0 b1 b2 pre spare : List UInt8) : DataMem := (block b0 b1 b2 pre spare).At (0x10000 : BitVec 64)

def cs0 (b0 b1 b2 pre spare : List UInt8) (zmms : RegZmms) (flags : StatusFlags) : MachineData :=
  ⟨⟨0x10008, 0x10128, UInt64.ofNat pre.length, 0, 0, UInt64.ofNat (pre.length + 96 + spare.length), 0x10110, 0,
    0, 0, 0, 0, 0, 0, 0xfff0, 0⟩, zmms, flags, mem b0 b1 b2 pre spare⟩

set_option maxHeartbeats 16000000 in
/-- Empty prefix, `cap = 96`. -/
theorem runs_empty (b0 : List UInt8) (b1 : List UInt8) (b2 : List UInt8)
    (h_b0 : b0.length = 32) (h_b1 : b1.length = 32) (h_b2 : b2.length = 32)
    (zmms : RegZmms) (flags : StatusFlags) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec (0 : UInt64).toBitVec ∧ st.data.regs.rax = 0x10128
        ∧ st.data.regs.rdi = 0 ∧ st.data.regs.rsi = 0)
      ⟨cs0 b0 b1 b2 [] [] zmms flags, Host.addrOf 0⟩ :=
  eventually_mono (Encode.generated_fast 0 hk0 hf0 (w 32) (w 32) (w 32) b0 b1 b2 [] (z 32) (z 32) (z 32) rfl rfl rfl h_b0 h_b1 h_b2 rfl rfl rfl (0x10050 : BitVec 64) (0x10070 : BitVec 64) (0x10090 : BitVec 64) (cs0 b0 b1 b2 [] [] zmms flags) 0 0 rfl (z 8) (z 8) (z 8) (z 8) (z 8) (z 8) (z 8) rfl rfl rfl rfl rfl rfl rfl (Eq ((z 48).At (0x100b8 : BitVec 64)) ⋆ Eq ((z 8).At (0x100f8 : BitVec 64))) 0 [] rfl 
    (by
      have H : Eq ((block b0 b1 b2 [] []).At (0x10000 : BitVec 64))
        (mem b0 b1 b2 [] []) := rfl
      wit_split [h_b0, h_b1, h_b2]
      simp only [cs0, w, nil_At_emp, Std.ExtHashMap.sep_emp, Std.ExtHashMap.emp_sep, UInt64.toBitVec_ofNat,
        BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, BitVec.reduceSub, List.length_nil, List.length_cons,
        List.length_replicate, show (UInt64.ofNat 0).toBitVec = 0#64 from rfl] at H ⊢
      simp only [Std.ExtHashMap.sep_assoc] at H ⊢
      simp only [Std.ExtHashMap.sep_comm, Std.ExtHashMap.sep_comm_l] at H ⊢
      exact H)
    (by simp [cs0]) (by simp [cs0]) (by simp [cs0]) (by simp [cs0]) (rt_memmove 153 hkR hfR 0))
    (fun _ h => ⟨h.1, h.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1⟩)

set_option maxHeartbeats 16000000 in
/-- Prefix `[0xaa, 0xbb, 0xcc]`, 5 spare bytes (`cap = len + 101`). -/
theorem runs_prefix (b0 : List UInt8) (b1 : List UInt8) (b2 : List UInt8)
    (h_b0 : b0.length = 32) (h_b1 : b1.length = 32) (h_b2 : b2.length = 32)
    (zmms : RegZmms) (flags : StatusFlags) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec (0 : UInt64).toBitVec ∧ st.data.regs.rax = 0x10128
        ∧ st.data.regs.rdi = 0 ∧ st.data.regs.rsi = 0)
      ⟨cs0 b0 b1 b2 [0xaa, 0xbb, 0xcc] (z 5) zmms flags, Host.addrOf 0⟩ :=
  eventually_mono (Encode.generated_fast 0 hk0 hf0 (w 32) (w 32) (w 32) b0 b1 b2 [0xaa, 0xbb, 0xcc] (z 32) (z 32) (z 32) rfl rfl rfl h_b0 h_b1 h_b2 rfl rfl rfl (0x10050 : BitVec 64) (0x10070 : BitVec 64) (0x10090 : BitVec 64) (cs0 b0 b1 b2 [0xaa, 0xbb, 0xcc] (z 5) zmms flags) 0 0 rfl (z 8) (z 8) (z 8) (z 8) (z 8) (z 8) (z 8) rfl rfl rfl rfl rfl rfl rfl (Eq ((z 48).At (0x100b8 : BitVec 64)) ⋆ Eq ((z 8).At (0x100f8 : BitVec 64)) ⋆ Eq ((z 5).At (0x1018b : BitVec 64))) 0 [] rfl 
    (by
      have H : Eq ((block b0 b1 b2 [0xaa, 0xbb, 0xcc] (z 5)).At (0x10000 : BitVec 64))
        (mem b0 b1 b2 [0xaa, 0xbb, 0xcc] (z 5)) := rfl
      wit_split [h_b0, h_b1, h_b2]
      simp only [cs0, w, nil_At_emp, Std.ExtHashMap.sep_emp, Std.ExtHashMap.emp_sep, UInt64.toBitVec_ofNat,
        BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, BitVec.reduceSub, List.length_nil, List.length_cons,
        List.length_replicate, show (UInt64.ofNat 3).toBitVec = 3#64 from rfl] at H ⊢
      simp only [Std.ExtHashMap.sep_assoc] at H ⊢
      simp only [Std.ExtHashMap.sep_comm, Std.ExtHashMap.sep_comm_l] at H ⊢
      exact H)
    (by simp [cs0]) (by simp [cs0]) (by simp [cs0]) (by simp [cs0]) (rt_memmove 153 hkR hfR 0))
    (fun _ h => ⟨h.1, h.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1⟩)

example (z' : RegZmms) (f : StatusFlags) :=
  runs_empty (List.replicate 32 0) (List.replicate 32 0) (List.replicate 32 0) rfl rfl rfl z' f
example (z' : RegZmms) (f : StatusFlags) :=
  runs_prefix (List.replicate 32 0x5a) (List.replicate 32 0x5a) (List.replicate 32 0x5a) rfl rfl rfl z' f
example (z' : RegZmms) (f : StatusFlags) :=
  runs_prefix (List.replicate 32 0xff) (List.replicate 32 0xff) (List.replicate 32 0xff) rfl rfl rfl z' f

end Prysm.PowBlock.Witness.GeneratedEncodeFastPath
