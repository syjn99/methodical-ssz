import Prysm.Checkpoint.CapacityReservedEncodeFastPath
import Runtime.CopyModel
import Machine.WitnessHost
import Machine.WitnessSplit
import Prysm.Checkpoint.GoValue

/-!
# OPT-R1 witness of `CapacityReserved.Encode.fast_path` (fast path, `cap − len ≥ 40`)

Host: the reserve encoder `marshalSSZTo` (index 0) and `RtCopy` (index 135, `rt_memmove`, S = 0). One memory
block at `0x10000`: guard word (r14 = 0xfff0), the 72-byte receiver (`Epoch` = `e8`, `Root` = (0x10050, 32, 32)),
the 32 root bytes, the stack window rsp − 160 … rsp + 32 (rsp = 0x10110) and `dst` at 0x10130: the prefix,
8 + 32 bytes of old contents, the spare capacity. Frame `R`: the untouched 88-byte frame gap (rsp − 152 …
rsp − 65; the reserve's `z` and the growslice spill area are not used on this path) and the spare capacity.
Instances: empty prefix with `cap = 40` (spare exactly 40), a 3-byte prefix with 5 more spare bytes.
`recv`: the receiver bytes are a Go value of `v1alpha1.Checkpoint` (`Prysm.Checkpoint.goValue`).
-/

open Machine Runtime Machine.Witness Prysm.Checkpoint.CapacityReserved Prysm.Checkpoint.CapacityReserved.Code

namespace Prysm.Checkpoint.Witness.CapacityReservedEncodeFastPath

set_option maxRecDepth 100000

def P : Program := marshalSSZTo ++ RtCopy

theorem P_len : P.length = 161 := by rfl

instance host : Host := mkHost P (by rw [P_len]; decide)

theorem hk0 : marshalSSZTo.IsInfixAt Host.prog 0 := infixAt_of [] RtCopy (by simp [Host.prog, mkHost, P]) rfl
theorem hk135 : RtCopy.IsInfixAt Host.prog 135 := infixAt_of marshalSSZTo [] (by simp [Host.prog, mkHost, P]) (by rfl)
theorem hf0 : LabelsFresh marshalSSZTo 0 := fun i hi => absurd hi (Nat.not_lt_zero _)
theorem hf135 : LabelsFresh RtCopy 135 := labelsFresh_of (by decide)

abbrev z (k : Nat) : List UInt8 := List.replicate k 0
abbrev w (v : UInt64) : List UInt8 := Int.toBytes 8 v.toBitVec.toInt

/-- guard · receiver (72) · root (32) · rslot · gap (88) · t40 (16) · t30 (16) · l32 · l24 · l16 · fp ·
return slot · spill rax · spill rbx · spill rcx · dst = prefix · d0 (8) · d1 (32) · spare. -/
def block (e8 root pre spare : List UInt8) : List UInt8 :=
  w 0 ++ (z 8 ++ (e8 ++ (w 0x10050 ++ (w 32 ++ (w 32 ++ (z 32 ++ (root ++ (z 8 ++ (z 88 ++ (z 16 ++ (z 16
    ++ (z 8 ++ (z 8 ++ (z 8 ++ (z 8 ++ (w 0 ++ (z 8 ++ (z 8 ++ (z 8 ++ (pre ++ (z 8 ++ (z 32 ++ spare))))))))))))))))))))))

def mem (e8 root pre spare : List UInt8) : DataMem := (block e8 root pre spare).At (0x10000 : BitVec 64)

def cs0 (e8 root pre spare : List UInt8) (zmms : RegZmms) (flags : StatusFlags) : MachineData :=
  ⟨⟨0x10008, 0x10130, UInt64.ofNat pre.length, 0, 0, UInt64.ofNat (pre.length + 40 + spare.length), 0x10110, 0,
    0, 0, 0, 0, 0, 0, 0xfff0, 0⟩, zmms, flags, mem e8 root pre spare⟩

set_option maxHeartbeats 16000000 in
/-- Empty prefix, `cap = 40`. -/
theorem runs_empty (e8 root : List UInt8) (he8 : e8.length = 8) (hroot : root.length = 32)
    (zmms : RegZmms) (flags : StatusFlags) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec (0 : UInt64).toBitVec ∧ st.data.regs.rax = 0x10130
        ∧ st.data.regs.rdi = 0 ∧ st.data.regs.rsi = 0)
      ⟨cs0 e8 root [] [] zmms flags, Host.addrOf 0⟩ :=
  eventually_mono (CapacityReserved.Encode.fast_path 0 hk0 hf0 (z 8) e8 (w 32) (z 32) root [] (z 8) (z 32) rfl he8 rfl rfl hroot
    rfl rfl 0x10050 (cs0 e8 root [] [] zmms flags) 0 0 rfl (z 8) (z 8) (z 8) (z 8) (z 8) (z 8) (z 8) (z 16) (z 16)
    (z 8) rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    (Eq ((z 88).At (0x10078 : BitVec 64)))
    0 [] rfl
    (by
      have H : Eq ((block e8 root [] []).At (0x10000 : BitVec 64)) (mem e8 root [] []) := rfl
      wit_split_n [he8, hroot]
      simp only [cs0, w, nil_At_emp, Std.ExtHashMap.sep_emp, Std.ExtHashMap.emp_sep, UInt64.toBitVec_ofNat,
        BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, BitVec.reduceSub, List.length_nil,
        show (UInt64.ofNat 0).toBitVec = 0#64 from rfl] at H ⊢
      simp only [Std.ExtHashMap.sep_assoc] at H ⊢
      simp only [Std.ExtHashMap.sep_comm, Std.ExtHashMap.sep_comm_l] at H ⊢
      exact H)
    (by simp [cs0]) (by simp [cs0]) (by simp [cs0]) (rt_memmove 135 hk135 hf135 0))
    (fun _ h => ⟨h.1, h.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1⟩)

set_option maxHeartbeats 16000000 in
/-- Prefix `[0xaa, 0xbb, 0xcc]`, 5 spare bytes after the 40 (`cap = len + 45`). -/
theorem runs_prefix (e8 root : List UInt8) (he8 : e8.length = 8) (hroot : root.length = 32)
    (zmms : RegZmms) (flags : StatusFlags) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec (0 : UInt64).toBitVec ∧ st.data.regs.rax = 0x10130
        ∧ st.data.regs.rdi = 0 ∧ st.data.regs.rsi = 0)
      ⟨cs0 e8 root [0xaa, 0xbb, 0xcc] (z 5) zmms flags, Host.addrOf 0⟩ :=
  eventually_mono (CapacityReserved.Encode.fast_path 0 hk0 hf0 (z 8) e8 (w 32) (z 32) root [0xaa, 0xbb, 0xcc] (z 8) (z 32) rfl he8 rfl
    rfl hroot rfl rfl 0x10050 (cs0 e8 root [0xaa, 0xbb, 0xcc] (z 5) zmms flags) 0 0 rfl (z 8) (z 8) (z 8) (z 8) (z 8)
    (z 8) (z 8) (z 16) (z 16) (z 8) rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    (Eq ((z 88).At (0x10078 : BitVec 64)) ⋆ Eq ((z 5).At (0x1015b : BitVec 64)))
    0 [] rfl
    (by
      have H : Eq ((block e8 root [0xaa, 0xbb, 0xcc] (z 5)).At (0x10000 : BitVec 64)) (mem e8 root [0xaa, 0xbb, 0xcc] (z 5)) := rfl
      wit_split_n [he8, hroot]
      simp only [cs0, w, nil_At_emp, Std.ExtHashMap.sep_emp, Std.ExtHashMap.emp_sep, UInt64.toBitVec_ofNat,
        BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, BitVec.reduceSub, List.length_nil, List.length_cons,
        List.length_replicate, show (UInt64.ofNat 3).toBitVec = 3#64 from rfl] at H ⊢
      simp only [Std.ExtHashMap.sep_assoc] at H ⊢
      simp only [Std.ExtHashMap.sep_comm, Std.ExtHashMap.sep_comm_l] at H ⊢
      exact H)
    (by simp [cs0]) (by simp [cs0]) (by simp [cs0]) (rt_memmove 135 hk135 hf135 0))
    (fun _ h => ⟨h.1, h.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1⟩)

example (z' : RegZmms) (f : StatusFlags) := runs_empty (Int.toBytes 8 0) (z 32) (by decide) rfl z' f
example (z' : RegZmms) (f : StatusFlags) :=
  runs_prefix (Int.toBytes 8 0x0123456789abcdef) ((List.range 32).map (fun i => (UInt8.ofNat i))) (by decide) rfl z' f
example (z' : RegZmms) (f : StatusFlags) :=
  runs_prefix (Int.toBytes 8 (2 ^ 64 - 1)) (List.replicate 32 0xff) (by decide) rfl z' f

/-- Go-value element: the receiver of this witness (offset 8 of the block; Root = (0x10050, 32, 32)). -/
theorem recv : goValue (recvAt (block (Int.toBytes 8 0x0123456789abcdef) (List.replicate 32 0xff)
    [0xaa, 0xbb, 0xcc] (z 5)) 8) = true := by decide

end Prysm.Checkpoint.Witness.CapacityReservedEncodeFastPath
