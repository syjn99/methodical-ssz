import Prysm.Eth1Data.EncodeFastPath
import Runtime.CopyModel
import Machine.WitnessHost

/-!
# Witness of `Encode.fast_path` (Eth1Data encoder, fast path only)

Hand-written (the text of `Prysm/BeaconBlockHeader/WitnessEncodeFastPath.lean` with the Eth1Data host and layout).
Host: the real Go 1.26.10 `(*v1alpha1.Eth1Data).MarshalSSZTo` (index 0) and `MemmoveGrowsliceModel` (index 119,
`model_memmove`, S = 0). One memory block at `0x10000`: guard word (r14 = 0xfff0), the 96-byte receiver at
0x10008 (`prysm/ir/ir-mainnet.json` gc amd64 layout: `state` 0, DepositRoot = (0x10068, 32, 32),
DepositCount = `dc`, BlockHash = (0x10088, 32, 32), `unknownFields`/`sizeCache`/padding = 32 zero bytes),
the two 32-byte root arrays, the stack window (rsp = 0x10138: `memmove` return slot at rsp − 144, frame,
saved rbp, return slot, the two argument spill slots) and `dst` at 0x10150: the prefix, 32 + 8 + 32 bytes
of old contents, the spare capacity. Frame `R`: the untouched receiver tail (32 bytes), the untouched
frame bytes rsp − 136 … rsp − 57 (80), and the spare capacity.
The receiver is a Go value of `v1alpha1.Eth1Data` (zero `state`, two roots with len = cap = 32).
Two instances: empty prefix with `cap = 72`, and a 3-byte prefix with 5 spare bytes. For every
DepositCount and root contents every premise of the theorem holds.
-/

open Machine Runtime Machine.Witness Codec Prysm.Eth1Data.Code

namespace Prysm.Eth1Data.Witness.EncodeFastPath

set_option maxRecDepth 100000

def program : Program := marshalSSZTo ++ MemmoveGrowsliceModel

theorem program_length : program.length = 145 := by rfl

instance host : Host := mkHost program (by rw [program_length]; decide)

theorem placed_at_0 : marshalSSZTo.IsInfixAt Host.prog 0 := infixAt_of [] MemmoveGrowsliceModel (by simp [Host.prog, mkHost, program]) rfl
theorem placed_at_119 : MemmoveGrowsliceModel.IsInfixAt Host.prog 119 := infixAt_of marshalSSZTo [] (by simp [Host.prog, mkHost, program]) (by rfl)
theorem labels_fresh_at_0 : LabelsFresh marshalSSZTo 0 := fun i hi => absurd hi (Nat.not_lt_zero _)
theorem labels_fresh_at_119 : LabelsFresh MemmoveGrowsliceModel 119 := labelsFresh_of (by decide)

abbrev zeros (k : Nat) : List UInt8 := List.replicate k 0
abbrev word_bytes (v : UInt64) : List UInt8 := Int.toBytes 8 v.toBitVec.toInt

/-- guard · receiver (`state`, DepositRoot header, DepositCount, BlockHash header, 32-byte tail) · r1 · r2 ·
rslot · gap (80) · l56 · l48 · l40 · l32 · l24 · l16 · fp · return slot · spill rax · spill rbx ·
dst = prefix · d0 (32) · d1 (8) · d2 (32) · spare. -/
def block (dc r1 r2 pre spare : List UInt8) : List UInt8 :=
  word_bytes 0 ++ (zeros 8 ++ (word_bytes 0x10068 ++ (Int.toBytes 8 32 ++ (word_bytes 32 ++ (dc ++ (word_bytes 0x10088 ++ (Int.toBytes 8 32 ++ (word_bytes 32 ++ (zeros 32 ++ (r1 ++ (r2 ++ (zeros 8 ++ (zeros 80 ++ (zeros 8 ++ (zeros 8 ++ (zeros 8 ++ (zeros 8 ++ (zeros 8 ++ (zeros 8 ++ (zeros 8 ++ (word_bytes 0 ++ (zeros 8 ++ (zeros 8 ++ (pre ++ (zeros 32 ++ (zeros 8 ++ (zeros 32 ++ (spare))))))))))))))))))))))))))))

def mem (dc r1 r2 pre spare : List UInt8) : DataMem := (block dc r1 r2 pre spare).At (0x10000 : BitVec 64)

def initial_state (dc r1 r2 pre spare : List UInt8) (zmms : RegZmms) (flags : StatusFlags) : MachineData :=
  ⟨⟨0x10008, 0x10150, UInt64.ofNat pre.length, 0, 0, UInt64.ofNat (pre.length + 72 + spare.length), 0x10138, 0,
    0, 0, 0, 0, 0, 0, 0xfff0, 0⟩, zmms, flags, mem dc r1 r2 pre spare⟩

set_option maxHeartbeats 16000000 in
/-- Empty prefix, `cap = 72`. -/
theorem runs_empty (dc r1 r2 : List UInt8) (hdc : dc.length = 8)
    (hr1 : r1.length = 32) (hr2 : r2.length = 32)
    (zmms : RegZmms) (flags : StatusFlags) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec (0 : UInt64).toBitVec ∧ st.data.regs.rax = 0x10150
        ∧ st.data.regs.rdi = 0 ∧ st.data.regs.rsi = 0)
      ⟨initial_state dc r1 r2 [] [] zmms flags, Host.addrOf 0⟩ :=
  eventually_mono (Encode.fast_path 0 placed_at_0 labels_fresh_at_0 (zeros 8) dc (word_bytes 32) (word_bytes 32) r1 r2 []
    (zeros 32) (zeros 8) (zeros 32) rfl hdc rfl rfl hr1 hr2 rfl rfl rfl
    0x10068 0x10088 (initial_state dc r1 r2 [] [] zmms flags) 0 0 rfl
    (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 8)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    (Eq ((zeros 32).At (0x10048 : BitVec 64)) ⋆ Eq ((zeros 80).At (0x100b0 : BitVec 64)))
    0 [] rfl
    (by
      have H : Eq ((block dc r1 r2 [] []).At (0x10000 : BitVec 64))
        (mem dc r1 r2 [] []) := rfl
      witness_split [hdc, hr1, hr2]
      simp only [initial_state, word_bytes, nil_At_emp, Std.ExtHashMap.sep_emp, Std.ExtHashMap.emp_sep, UInt64.toBitVec_ofNat,
        BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, BitVec.reduceSub, List.length_nil,
        show (UInt64.ofNat 0).toBitVec = 0#64 from rfl] at H ⊢
      simp only [Std.ExtHashMap.sep_assoc] at H ⊢
      simp only [Std.ExtHashMap.sep_comm, Std.ExtHashMap.sep_comm_l] at H ⊢
      exact H)
    (by simp [initial_state]) (by simp [initial_state]) (by simp [initial_state]) (by simp [initial_state]) (model_memmove 119 placed_at_119 labels_fresh_at_119 0))
    (fun _ h => ⟨h.1, h.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1⟩)

set_option maxHeartbeats 16000000 in
/-- Prefix `[0xaa, 0xbb, 0xcc]`, 5 spare bytes (`cap = len + 77`). -/
theorem runs_prefix (dc r1 r2 : List UInt8) (hdc : dc.length = 8)
    (hr1 : r1.length = 32) (hr2 : r2.length = 32)
    (zmms : RegZmms) (flags : StatusFlags) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec (0 : UInt64).toBitVec ∧ st.data.regs.rax = 0x10150
        ∧ st.data.regs.rdi = 0 ∧ st.data.regs.rsi = 0)
      ⟨initial_state dc r1 r2 [0xaa, 0xbb, 0xcc] (zeros 5) zmms flags, Host.addrOf 0⟩ :=
  eventually_mono (Encode.fast_path 0 placed_at_0 labels_fresh_at_0 (zeros 8) dc (word_bytes 32) (word_bytes 32) r1 r2 [0xaa, 0xbb, 0xcc]
    (zeros 32) (zeros 8) (zeros 32) rfl hdc rfl rfl hr1 hr2 rfl rfl rfl
    0x10068 0x10088 (initial_state dc r1 r2 [0xaa, 0xbb, 0xcc] (zeros 5) zmms flags) 0 0 rfl
    (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 8)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    (Eq ((zeros 32).At (0x10048 : BitVec 64)) ⋆ Eq ((zeros 80).At (0x100b0 : BitVec 64))
      ⋆ Eq ((zeros 5).At (0x1019b : BitVec 64)))
    0 [] rfl
    (by
      have H : Eq ((block dc r1 r2 [0xaa, 0xbb, 0xcc] (zeros 5)).At (0x10000 : BitVec 64))
        (mem dc r1 r2 [0xaa, 0xbb, 0xcc] (zeros 5)) := rfl
      witness_split [hdc, hr1, hr2]
      simp only [initial_state, word_bytes, nil_At_emp, Std.ExtHashMap.sep_emp, Std.ExtHashMap.emp_sep, UInt64.toBitVec_ofNat,
        BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, BitVec.reduceSub, List.length_nil, List.length_cons, List.length_replicate,
        show (UInt64.ofNat 3).toBitVec = 3#64 from rfl] at H ⊢
      simp only [Std.ExtHashMap.sep_assoc] at H ⊢
      simp only [Std.ExtHashMap.sep_comm, Std.ExtHashMap.sep_comm_l] at H ⊢
      exact H)
    (by simp [initial_state]) (by simp [initial_state]) (by simp [initial_state]) (by simp [initial_state]) (model_memmove 119 placed_at_119 labels_fresh_at_119 0))
    (fun _ h => ⟨h.1, h.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1⟩)

example (z' : RegZmms) (f : StatusFlags) :=
  runs_empty (Int.toBytes 8 0) (zeros 32) (zeros 32) (by decide) rfl rfl z' f
example (z' : RegZmms) (f : StatusFlags) :=
  runs_prefix (Int.toBytes 8 0x0123456789abcdef) ((List.range 32).map (fun i => (UInt8.ofNat i)))
    (List.replicate 32 0x22) (by decide) rfl rfl z' f
example (z' : RegZmms) (f : StatusFlags) :=
  runs_prefix (Int.toBytes 8 (2 ^ 64 - 1)) (List.replicate 32 0xff) (List.replicate 32 0xff)
    (by decide) rfl rfl z' f

end Prysm.Eth1Data.Witness.EncodeFastPath
