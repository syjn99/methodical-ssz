import Prysm.Epoch.EncodeFastPath
import Runtime.CopyModel
import Machine.WitnessHost

/-!
# Witness of `Encode.fast_path` (encoder fast path)

Host: the real Go 1.26.10 `(*primitives.Epoch).MarshalSSZTo` alone (index 0); the fast path calls no function.
One memory block at `0x10000`: guard word (r14 = 0xfff0), the 8-byte receiver `e8`,
the stack window (rsp = 0x10038: the 32-byte temp, the frame pointer slot, the return slot, a gap and the rbx spill slot)
and `dst` at 0x10050: the prefix, 8 bytes of old contents, the spare capacity.
Frame `R`: the gap at rsp + 8 and the spare capacity.
Two instances: empty prefix with `cap = 8`, and a 3-byte prefix with 5 spare bytes.
-/

open Machine Runtime Machine.Witness Prysm.Epoch.Code

namespace Prysm.Epoch.Witness.EncodeFastPath

instance host : Host := mkHost marshalSSZTo (by decide)

theorem placed_at_0 : marshalSSZTo.IsInfixAt Host.prog 0 := ⟨[], by simp [Host.prog, mkHost]⟩
theorem labels_fresh_at_0 : LabelsFresh marshalSSZTo 0 := fun i hi => absurd hi (Nat.not_lt_zero _)

abbrev zeros (k : Nat) : List UInt8 := List.replicate k 0
abbrev word_bytes (v : UInt64) : List UInt8 := Int.toBytes 8 v.toBitVec.toInt

/-- guard · receiver (8) · temp (16 + 16) · fp · return slot · gap · spill rbx · dst = prefix · d0 (8) · spare. -/
def block (e8 pre spare : List UInt8) : List UInt8 :=
  word_bytes 0 ++ (e8 ++ (zeros 16 ++ (zeros 16 ++ (zeros 8 ++ (word_bytes 0 ++ (zeros 8 ++ (zeros 8
    ++ (pre ++ (zeros 8 ++ spare)))))))))

def mem (e8 pre spare : List UInt8) : DataMem := (block e8 pre spare).At (0x10000 : BitVec 64)

def initial_state (e8 pre spare : List UInt8) (zmms : RegZmms) (flags : StatusFlags) : MachineData :=
  ⟨⟨0x10008, 0x10050, UInt64.ofNat pre.length, 0, 0, UInt64.ofNat (pre.length + 8 + spare.length), 0x10038, 0,
    0, 0, 0, 0, 0, 0, 0xfff0, 0⟩, zmms, flags, mem e8 pre spare⟩

/-- Empty prefix, `cap = 8`. -/
theorem runs_empty (e8 : List UInt8) (he8 : e8.length = 8) (zmms : RegZmms) (flags : StatusFlags) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec (0 : UInt64).toBitVec ∧ st.data.regs.rax = 0x10050
        ∧ st.data.regs.rdi = 0 ∧ st.data.regs.rsi = 0)
      ⟨initial_state e8 [] [] zmms flags, Host.addrOf 0⟩ :=
  eventually_mono (Encode.fast_path 0 placed_at_0 labels_fresh_at_0 e8 [] (zeros 8) he8 rfl
    (initial_state e8 [] [] zmms flags) 0 0 rfl (zeros 8) (zeros 8) (zeros 16) (zeros 16) rfl rfl rfl rfl
    (Eq ((zeros 8).At (0x10040 : BitVec 64)))
    (by
      have H : Eq ((block e8 [] []).At (0x10000 : BitVec 64)) (mem e8 [] []) := rfl
      witness_split [he8]
      simp only [initial_state, word_bytes, nil_At_emp, Std.ExtHashMap.sep_emp, Std.ExtHashMap.emp_sep, UInt64.toBitVec_ofNat,
        BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, BitVec.reduceSub, List.length_nil,
        show (UInt64.ofNat 0).toBitVec = 0#64 from rfl] at H ⊢
      simp only [Std.ExtHashMap.sep_assoc] at H ⊢
      simp only [Std.ExtHashMap.sep_comm, Std.ExtHashMap.sep_comm_l] at H ⊢
      exact H)
    (by simp [initial_state]) (by simp [initial_state]))
    (fun _ h => ⟨h.1, h.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1⟩)

/-- Prefix `[0xaa, 0xbb, 0xcc]`, 5 spare bytes (`cap = len + 13`). -/
theorem runs_prefix (e8 : List UInt8) (he8 : e8.length = 8) (zmms : RegZmms) (flags : StatusFlags) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec (0 : UInt64).toBitVec ∧ st.data.regs.rax = 0x10050
        ∧ st.data.regs.rdi = 0 ∧ st.data.regs.rsi = 0)
      ⟨initial_state e8 [0xaa, 0xbb, 0xcc] (zeros 5) zmms flags, Host.addrOf 0⟩ :=
  eventually_mono (Encode.fast_path 0 placed_at_0 labels_fresh_at_0 e8 [0xaa, 0xbb, 0xcc] (zeros 8) he8 rfl
    (initial_state e8 [0xaa, 0xbb, 0xcc] (zeros 5) zmms flags) 0 0 rfl (zeros 8) (zeros 8) (zeros 16) (zeros 16)
    rfl rfl rfl rfl
    (Eq ((zeros 8).At (0x10040 : BitVec 64)) ⋆ Eq ((zeros 5).At (0x1005b : BitVec 64)))
    (by
      have H : Eq ((block e8 [0xaa, 0xbb, 0xcc] (zeros 5)).At (0x10000 : BitVec 64)) (mem e8 [0xaa, 0xbb, 0xcc] (zeros 5)) := rfl
      witness_split [he8]
      simp only [initial_state, word_bytes, nil_At_emp, Std.ExtHashMap.sep_emp, Std.ExtHashMap.emp_sep, UInt64.toBitVec_ofNat,
        BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, BitVec.reduceSub, List.length_nil, List.length_cons, List.length_replicate,
        show (UInt64.ofNat 3).toBitVec = 3#64 from rfl] at H ⊢
      simp only [Std.ExtHashMap.sep_assoc] at H ⊢
      simp only [Std.ExtHashMap.sep_comm, Std.ExtHashMap.sep_comm_l] at H ⊢
      exact H)
    (by simp [initial_state]) (by simp [initial_state]))
    (fun _ h => ⟨h.1, h.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1⟩)

example (z' : RegZmms) (f : StatusFlags) := runs_empty (Int.toBytes 8 0) (by decide) z' f
example (z' : RegZmms) (f : StatusFlags) := runs_prefix (Int.toBytes 8 0x0123456789abcdef) (by decide) z' f
example (z' : RegZmms) (f : StatusFlags) := runs_prefix (Int.toBytes 8 (2 ^ 64 - 1)) (by decide) z' f

end Prysm.Epoch.Witness.EncodeFastPath
