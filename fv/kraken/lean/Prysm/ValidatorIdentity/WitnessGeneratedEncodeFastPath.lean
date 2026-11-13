import Prysm.ValidatorIdentity.GeneratedEncodeFastPath
import Runtime.CopyModel
import Machine.WitnessHost

/-!
# Witness of `Encode.generated_fast` (ValidatorIdentity encoder fast path, generated theorem; 24 flat hold-out types, text of the encoder specification emitter)

Emitted by the unit's evidence tool `encode_spec_emitter.py` (not the generator) from the committed statement text and
the IR; then built and kernel-checked. Host: the real Go 1.26.10 `MarshalSSZTo` (index 0) and `MemmoveGrowsliceModel` (index 119, `model_memmove`, S = 0).
One memory block at `0x10000`: guard word (r14 = 0xfff0); the receiver at 0x10008 (`prysm/ir/ir-mainnet.json`
gc amd64 layout, 80 bytes; byte fields = (pointer, n, n) with the n bytes after the receiver; unexported tail
zero); the stack window (rsp = 0x10128: rsp − 160 … rsp + 23); `dst` at 0x10140: the prefix, the old output
bytes, the spare capacity. Frame `R`: every byte of the block that no premise chunk names, and the spare.
Two instances: empty prefix with `cap = 64`; prefix `[0xaa, 0xbb, 0xcc]` with 5 spare bytes. For every
field value of the stated lengths every premise of `Encode.generated_fast` holds (non-vacuity of the fast path).
-/

open Machine Runtime Machine.Witness Codec Prysm.ValidatorIdentity.Code

namespace Prysm.ValidatorIdentity.Witness.GeneratedEncodeFastPath

set_option maxRecDepth 100000

def program : Program := marshalSSZTo ++ MemmoveGrowsliceModel

theorem program_length : program.length = 145 := by rfl

instance host : Host := mkHost program (by rw [program_length]; decide)

theorem placed_at_0 : marshalSSZTo.IsInfixAt Host.prog 0 := infixAt_of [] MemmoveGrowsliceModel (by simp [Host.prog, mkHost, program]) rfl
theorem placed_copy_model : MemmoveGrowsliceModel.IsInfixAt Host.prog 119 := infixAt_of marshalSSZTo [] (by simp [Host.prog, mkHost, program]) (by rfl)
theorem labels_fresh_at_0 : LabelsFresh marshalSSZTo 0 := fun i hi => absurd hi (Nat.not_lt_zero _)
theorem labels_fresh_copy_model : LabelsFresh MemmoveGrowsliceModel 119 := labelsFresh_of (by decide)

abbrev zeros (k : Nat) : List UInt8 := List.replicate k 0
abbrev word_bytes (v : UInt64) : List UInt8 := Int.toBytes 8 v.toBitVec.toInt

def block (v0 v2 b1 pre spare : List UInt8) : List UInt8 :=
  (word_bytes 0) ++ ((zeros 8) ++ (v0 ++ ((word_bytes 0x10058) ++ ((Int.toBytes 8 48) ++ ((word_bytes 48) ++ (v2 ++ ((zeros 32) ++ (b1 ++ ((zeros 8) ++ ((zeros 48) ++ ((zeros 8) ++ ((zeros 8) ++ ((zeros 16) ++ ((zeros 16) ++ ((zeros 16) ++ ((zeros 16) ++ ((zeros 8) ++ ((zeros 8) ++ ((zeros 8) ++ ((word_bytes 0) ++ ((zeros 8) ++ ((zeros 8) ++ (pre ++ ((zeros 8) ++ ((zeros 48) ++ ((zeros 8) ++ (spare)))))))))))))))))))))))))))

def mem (v0 v2 b1 pre spare : List UInt8) : DataMem := (block v0 v2 b1 pre spare).At (0x10000 : BitVec 64)

def initial_state (v0 v2 b1 pre spare : List UInt8) (zmms : RegZmms) (flags : StatusFlags) : MachineData :=
  ⟨⟨0x10008, 0x10140, UInt64.ofNat pre.length, 0, 0, UInt64.ofNat (pre.length + 64 + spare.length), 0x10128, 0,
    0, 0, 0, 0, 0, 0, 0xfff0, 0⟩, zmms, flags, mem v0 v2 b1 pre spare⟩

set_option maxHeartbeats 16000000 in
/-- Empty prefix, `cap = 64`. -/
theorem runs_empty (v0 : List UInt8) (v2 : List UInt8) (b1 : List UInt8)
    (h_v0 : v0.length = 8) (h_v2 : v2.length = 8) (h_b1 : b1.length = 48)
    (zmms : RegZmms) (flags : StatusFlags) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec (0 : UInt64).toBitVec ∧ st.data.regs.rax = 0x10140
        ∧ st.data.regs.rdi = 0 ∧ st.data.regs.rsi = 0)
      ⟨initial_state v0 v2 b1 [] [] zmms flags, Host.addrOf 0⟩ :=
  eventually_mono (Encode.generated_fast 0 placed_at_0 labels_fresh_at_0 (zeros 8) v0 v2 (word_bytes 48) b1 [] (zeros 8) (zeros 48) (zeros 8) rfl h_v0 h_v2 rfl h_b1 rfl rfl rfl (0x10058 : BitVec 64) (initial_state v0 v2 b1 [] [] zmms flags) 0 0 rfl (zeros 8) (zeros 8) (zeros 8) (zeros 16) (zeros 16) (zeros 8) (zeros 8) (zeros 8) (zeros 16) (zeros 16) (zeros 8) rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl (Eq ((zeros 32).At (0x10038 : BitVec 64)) ⋆ Eq ((zeros 48).At (0x10090 : BitVec 64)) ⋆ Eq ((zeros 8).At (0x10118 : BitVec 64))) 0 [] rfl 
    (by
      have H : Eq ((block v0 v2 b1 [] []).At (0x10000 : BitVec 64))
        (mem v0 v2 b1 [] []) := rfl
      witness_split [h_v0, h_v2, h_b1]
      simp only [initial_state, word_bytes, nil_At_emp, Std.ExtHashMap.sep_emp, Std.ExtHashMap.emp_sep, UInt64.toBitVec_ofNat,
        BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, BitVec.reduceSub, List.length_nil, List.length_cons,
        List.length_replicate, show (UInt64.ofNat 0).toBitVec = 0#64 from rfl] at H ⊢
      simp only [Std.ExtHashMap.sep_assoc] at H ⊢
      simp only [Std.ExtHashMap.sep_comm, Std.ExtHashMap.sep_comm_l] at H ⊢
      exact H)
    (by simp [initial_state]) (by simp [initial_state]) (by simp [initial_state]) (by simp [initial_state]) (model_memmove 119 placed_copy_model labels_fresh_copy_model 0))
    (fun _ h => ⟨h.1, h.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1⟩)

set_option maxHeartbeats 16000000 in
/-- Prefix `[0xaa, 0xbb, 0xcc]`, 5 spare bytes (`cap = len + 69`). -/
theorem runs_prefix (v0 : List UInt8) (v2 : List UInt8) (b1 : List UInt8)
    (h_v0 : v0.length = 8) (h_v2 : v2.length = 8) (h_b1 : b1.length = 48)
    (zmms : RegZmms) (flags : StatusFlags) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec (0 : UInt64).toBitVec ∧ st.data.regs.rax = 0x10140
        ∧ st.data.regs.rdi = 0 ∧ st.data.regs.rsi = 0)
      ⟨initial_state v0 v2 b1 [0xaa, 0xbb, 0xcc] (zeros 5) zmms flags, Host.addrOf 0⟩ :=
  eventually_mono (Encode.generated_fast 0 placed_at_0 labels_fresh_at_0 (zeros 8) v0 v2 (word_bytes 48) b1 [0xaa, 0xbb, 0xcc] (zeros 8) (zeros 48) (zeros 8) rfl h_v0 h_v2 rfl h_b1 rfl rfl rfl (0x10058 : BitVec 64) (initial_state v0 v2 b1 [0xaa, 0xbb, 0xcc] (zeros 5) zmms flags) 0 0 rfl (zeros 8) (zeros 8) (zeros 8) (zeros 16) (zeros 16) (zeros 8) (zeros 8) (zeros 8) (zeros 16) (zeros 16) (zeros 8) rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl (Eq ((zeros 32).At (0x10038 : BitVec 64)) ⋆ Eq ((zeros 48).At (0x10090 : BitVec 64)) ⋆ Eq ((zeros 8).At (0x10118 : BitVec 64)) ⋆ Eq ((zeros 5).At (0x10183 : BitVec 64))) 0 [] rfl 
    (by
      have H : Eq ((block v0 v2 b1 [0xaa, 0xbb, 0xcc] (zeros 5)).At (0x10000 : BitVec 64))
        (mem v0 v2 b1 [0xaa, 0xbb, 0xcc] (zeros 5)) := rfl
      witness_split [h_v0, h_v2, h_b1]
      simp only [initial_state, word_bytes, nil_At_emp, Std.ExtHashMap.sep_emp, Std.ExtHashMap.emp_sep, UInt64.toBitVec_ofNat,
        BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, BitVec.reduceSub, List.length_nil, List.length_cons,
        List.length_replicate, show (UInt64.ofNat 3).toBitVec = 3#64 from rfl] at H ⊢
      simp only [Std.ExtHashMap.sep_assoc] at H ⊢
      simp only [Std.ExtHashMap.sep_comm, Std.ExtHashMap.sep_comm_l] at H ⊢
      exact H)
    (by simp [initial_state]) (by simp [initial_state]) (by simp [initial_state]) (by simp [initial_state]) (model_memmove 119 placed_copy_model labels_fresh_copy_model 0))
    (fun _ h => ⟨h.1, h.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1⟩)

example (z' : RegZmms) (f : StatusFlags) :=
  runs_empty (Int.toBytes 8 0) (Int.toBytes 8 0) (List.replicate 48 0) (by decide) (by decide) rfl z' f
example (z' : RegZmms) (f : StatusFlags) :=
  runs_prefix (Int.toBytes 8 0x0123456789abcdef) (Int.toBytes 8 0x0123456789abcdef) (List.replicate 48 0x5a) (by decide) (by decide) rfl z' f
example (z' : RegZmms) (f : StatusFlags) :=
  runs_prefix (Int.toBytes 8 (2 ^ 64 - 1)) (Int.toBytes 8 (2 ^ 64 - 1)) (List.replicate 48 0xff) (by decide) (by decide) rfl z' f

end Prysm.ValidatorIdentity.Witness.GeneratedEncodeFastPath
