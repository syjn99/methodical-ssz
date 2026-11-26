module

public import Prysm.AttestationData.EncodeFastPath
public import Runtime.CopyModel
public import Machine.WitnessHost

@[expose] public section

/-!
# Witness of `Encode.fast_path` (encoder fast path)

The host has `MemmoveGrowsliceModel` at index 0 (`model_memmove`, S = 0).
It has the Go 1.26.10 `(*v1alpha1.Checkpoint).MarshalSSZTo` at index 26.
It has `(*v1alpha1.AttestationData).MarshalSSZTo` at index 117.
One memory block starts at `0x10000` with the guard word (r14 = 0xfff0).
The first 64 bytes of the receiver are at 0x10008.
The receiver has `BeaconBlockRoot` = (0x10048, 32), `Source` = 0x10068 and `Target` = 0x100d0.
Then come the 32 root bytes, the Source object (72 bytes), its root, the Target object and its root.
Then come the 336-byte stack window (rsp = 0x10270) and `dst` at 0x10288.
`dst` has an empty prefix and 128 bytes of old contents, and `cap = 128`.
The frame `R` has the `state` word, the root capacity word and three untouched frame gaps.
-/

open Machine Runtime Machine.Witness

namespace Prysm.AttestationData.Witness.EncodeFastPath

def program : Program :=
  MemmoveGrowsliceModel ++ (Prysm.Checkpoint.Code.marshalSSZTo ++ Prysm.AttestationData.Code.marshalSSZTo)

theorem model_length : MemmoveGrowsliceModel.length = 26 := by rfl
theorem checkpoint_length : Prysm.Checkpoint.Code.marshalSSZTo.length = 91 := by rfl
theorem code_length : Prysm.AttestationData.Code.marshalSSZTo.length = 237 := by rfl
theorem program_length : program.length = 354 := by
  simp only [program, List.length_append, model_length, checkpoint_length, code_length]

instance host : Host := mkHost program (by rw [program_length]; decide)

theorem placed_model : MemmoveGrowsliceModel.IsInfixAt Host.prog 0 :=
  infixAt_of [] (Prysm.Checkpoint.Code.marshalSSZTo ++ Prysm.AttestationData.Code.marshalSSZTo) rfl rfl
theorem placed_checkpoint : Prysm.Checkpoint.Code.marshalSSZTo.IsInfixAt Host.prog 26 :=
  infixAt_of MemmoveGrowsliceModel Prysm.AttestationData.Code.marshalSSZTo rfl model_length
theorem placed_code : Prysm.AttestationData.Code.marshalSSZTo.IsInfixAt Host.prog 117 :=
  infixAt_of (MemmoveGrowsliceModel ++ Prysm.Checkpoint.Code.marshalSSZTo) []
    (by rw [List.append_nil, List.append_assoc]; rfl)
    (by rw [List.length_append, model_length, checkpoint_length])
theorem fresh_model : LabelsFresh MemmoveGrowsliceModel 0 := fun _ hi => absurd hi (Nat.not_lt_zero _)
theorem fresh_checkpoint : LabelsFresh Prysm.Checkpoint.Code.marshalSSZTo 26 := labelsFresh_of (by decide)
theorem fresh_code : LabelsFresh Prysm.AttestationData.Code.marshalSSZTo 117 := labelsFresh_of (by decide)

abbrev zeros (k : Nat) : List UInt8 := List.replicate k 0
abbrev word_bytes (v : UInt64) : List UInt8 := Int.toBytes 8 v.toBitVec.toInt

/-- The memory block in address order.
First the guard word and the receiver words (state, Slot, CommitteeIndex, root ptr, len, cap, Source, Target).
Then the root, the Source object and root, and the Target object and root.
Then the low stack block (120), the return slot, a gap and rsp − 176.
Then a gap (40), rsp − 128, rsp − 120, the two temps and rsp − 48.
Then a gap (32), fp, the return address, the two spill slots and `dst` (128). -/
def block (sl ix root e1 root1 e2 root2 : List UInt8) : List UInt8 :=
  word_bytes 0 ++ (zeros 8 ++ (sl ++ (ix ++ (Int.toBytes 8 (0x10048 : BitVec 64).toInt ++ (Int.toBytes 8 32
  ++ (zeros 8 ++ (Int.toBytes 8 (0x10068 : BitVec 64).toInt ++ (Int.toBytes 8 (0x100d0 : BitVec 64).toInt
  ++ (root ++ (zeros 8 ++ (e1 ++ (Int.toBytes 8 (0x100b0 : BitVec 64).toInt ++ (Int.toBytes 8 32
  ++ (word_bytes 32 ++ (zeros 32 ++ (root1 ++ (zeros 8 ++ (e2 ++ (Int.toBytes 8 (0x10118 : BitVec 64).toInt
  ++ (Int.toBytes 8 32 ++ (word_bytes 32 ++ (zeros 32 ++ (root2 ++ (zeros 120 ++ (zeros 8 ++ (zeros 8
  ++ (zeros 8 ++ (zeros 40 ++ (zeros 8 ++ (zeros 8 ++ (zeros 16 ++ (zeros 16 ++ (zeros 16 ++ (zeros 16
  ++ (zeros 8 ++ (zeros 32 ++ (zeros 8 ++ (word_bytes 0 ++ (zeros 8 ++ (zeros 8 ++ (zeros 8 ++ (zeros 8
  ++ (zeros 32 ++ (zeros 8 ++ (zeros 32 ++ (zeros 8 ++ (zeros 32)))))))))))))))))))))))))))))))))))))))))))))))

def mem (sl ix root e1 root1 e2 root2 : List UInt8) : DataMem := (block sl ix root e1 root1 e2 root2).At (0x10000 : BitVec 64)

def initial_state (sl ix root e1 root1 e2 root2 : List UInt8) (zmms : RegZmms) (flags : StatusFlags) : MachineData :=
  ⟨⟨0x10008, 0x10288, 0, 0, 0, 128, 0x10270, 0, 0, 0, 0, 0, 0, 0, 0xfff0, 0⟩, zmms, flags,
    mem sl ix root e1 root1 e2 root2⟩

/-- The memory premise of `Encode.fast_path` on the witness state. -/
theorem mem_premise (sl ix root e1 root1 e2 root2 : List UInt8) (hsl : sl.length = 8) (hix : ix.length = 8)
    (hroot : root.length = 32) (he1 : e1.length = 8) (hroot1 : root1.length = 32) (he2 : e2.length = 8)
    (hroot2 : root2.length = 32) (zmms : RegZmms) (flags : StatusFlags) :
    (initial_state sl ix root e1 root1 e2 root2 zmms flags).dmem =⋆
      Eq ((Int.toBytes 8 (0 : UInt64).toBitVec.toInt).At (initial_state sl ix root e1 root1 e2 root2 zmms flags).regs.rsp.toBitVec)
        ⋆ Eq ((zeros 8).At ((initial_state sl ix root e1 root1 e2 root2 zmms flags).regs.rsp.toBitVec - 8)) ⋆ Eq ((zeros 8).At ((initial_state sl ix root e1 root1 e2 root2 zmms flags).regs.rsp.toBitVec + 8))
        ⋆ Eq ((zeros 8).At ((initial_state sl ix root e1 root1 e2 root2 zmms flags).regs.rsp.toBitVec + 16)) ⋆ Eq ((zeros 16).At ((initial_state sl ix root e1 root1 e2 root2 zmms flags).regs.rsp.toBitVec - 80))
        ⋆ Eq ((zeros 16).At ((initial_state sl ix root e1 root1 e2 root2 zmms flags).regs.rsp.toBitVec - 64)) ⋆ Eq ((zeros 16).At ((initial_state sl ix root e1 root1 e2 root2 zmms flags).regs.rsp.toBitVec - 112))
        ⋆ Eq ((zeros 16).At ((initial_state sl ix root e1 root1 e2 root2 zmms flags).regs.rsp.toBitVec - 96)) ⋆ Eq ((zeros 8).At ((initial_state sl ix root e1 root1 e2 root2 zmms flags).regs.rsp.toBitVec - 48))
        ⋆ Eq ((zeros 8).At ((initial_state sl ix root e1 root1 e2 root2 zmms flags).regs.rsp.toBitVec - 120)) ⋆ Eq ((zeros 8).At ((initial_state sl ix root e1 root1 e2 root2 zmms flags).regs.rsp.toBitVec - 128))
        ⋆ Eq ((zeros 8).At ((initial_state sl ix root e1 root1 e2 root2 zmms flags).regs.rsp.toBitVec - 176))
        ⋆ Eq ((zeros 8).At ((initial_state sl ix root e1 root1 e2 root2 zmms flags).regs.rsp.toBitVec - 192)) ⋆ Eq ((zeros 120).At ((initial_state sl ix root e1 root1 e2 root2 zmms flags).regs.rsp.toBitVec - 312 - BitVec.ofNat 64 0))
        ⋆ Eq ((Int.toBytes 8 (0 : UInt64).toBitVec.toInt).At ((initial_state sl ix root e1 root1 e2 root2 zmms flags).regs.r14.toBitVec + 16))
        ⋆ Eq (sl.At ((initial_state sl ix root e1 root1 e2 root2 zmms flags).regs.rax.toBitVec + 8)) ⋆ Eq (ix.At ((initial_state sl ix root e1 root1 e2 root2 zmms flags).regs.rax.toBitVec + 16))
        ⋆ Eq ((Int.toBytes 8 (0x10048 : BitVec 64).toInt).At ((initial_state sl ix root e1 root1 e2 root2 zmms flags).regs.rax.toBitVec + 24)) ⋆ Eq ((Int.toBytes 8 32).At ((initial_state sl ix root e1 root1 e2 root2 zmms flags).regs.rax.toBitVec + 32))
        ⋆ Eq ((Int.toBytes 8 (0x10068 : BitVec 64).toInt).At ((initial_state sl ix root e1 root1 e2 root2 zmms flags).regs.rax.toBitVec + 48))
        ⋆ Eq ((Int.toBytes 8 (0x100d0 : BitVec 64).toInt).At ((initial_state sl ix root e1 root1 e2 root2 zmms flags).regs.rax.toBitVec + 56))
        ⋆ Eq (root.At (0x10048 : BitVec 64))
        ⋆ Eq ((zeros 8).At (0x10068 : BitVec 64)) ⋆ Eq (e1.At ((0x10068 : BitVec 64) + 8)) ⋆ Eq ((Int.toBytes 8 (0x100b0 : BitVec 64).toInt).At ((0x10068 : BitVec 64) + 16))
        ⋆ Eq ((Int.toBytes 8 32).At ((0x10068 : BitVec 64) + 24)) ⋆ Eq ((word_bytes 32).At ((0x10068 : BitVec 64) + 32)) ⋆ Eq ((zeros 32).At ((0x10068 : BitVec 64) + 40)) ⋆ Eq (root1.At (0x100b0 : BitVec 64))
        ⋆ Eq ((zeros 8).At (0x100d0 : BitVec 64)) ⋆ Eq (e2.At ((0x100d0 : BitVec 64) + 8)) ⋆ Eq ((Int.toBytes 8 (0x10118 : BitVec 64).toInt).At ((0x100d0 : BitVec 64) + 16))
        ⋆ Eq ((Int.toBytes 8 32).At ((0x100d0 : BitVec 64) + 24)) ⋆ Eq ((word_bytes 32).At ((0x100d0 : BitVec 64) + 32)) ⋆ Eq ((zeros 32).At ((0x100d0 : BitVec 64) + 40)) ⋆ Eq (root2.At (0x10118 : BitVec 64))
        ⋆ Eq (([] : List UInt8).At (initial_state sl ix root e1 root1 e2 root2 zmms flags).regs.rbx.toBitVec)
        ⋆ Eq ((zeros 8).At ((initial_state sl ix root e1 root1 e2 root2 zmms flags).regs.rbx.toBitVec + (initial_state sl ix root e1 root1 e2 root2 zmms flags).regs.rcx.toBitVec))
        ⋆ Eq ((zeros 8).At ((initial_state sl ix root e1 root1 e2 root2 zmms flags).regs.rbx.toBitVec + (initial_state sl ix root e1 root1 e2 root2 zmms flags).regs.rcx.toBitVec + 8))
        ⋆ Eq ((zeros 32).At ((initial_state sl ix root e1 root1 e2 root2 zmms flags).regs.rbx.toBitVec + (initial_state sl ix root e1 root1 e2 root2 zmms flags).regs.rcx.toBitVec + 16))
        ⋆ Eq ((zeros 8).At ((initial_state sl ix root e1 root1 e2 root2 zmms flags).regs.rbx.toBitVec + (initial_state sl ix root e1 root1 e2 root2 zmms flags).regs.rcx.toBitVec + 48))
        ⋆ Eq ((zeros 32).At ((initial_state sl ix root e1 root1 e2 root2 zmms flags).regs.rbx.toBitVec + (initial_state sl ix root e1 root1 e2 root2 zmms flags).regs.rcx.toBitVec + 56))
        ⋆ Eq ((zeros 8).At ((initial_state sl ix root e1 root1 e2 root2 zmms flags).regs.rbx.toBitVec + (initial_state sl ix root e1 root1 e2 root2 zmms flags).regs.rcx.toBitVec + 88))
        ⋆ Eq ((zeros 32).At ((initial_state sl ix root e1 root1 e2 root2 zmms flags).regs.rbx.toBitVec + (initial_state sl ix root e1 root1 e2 root2 zmms flags).regs.rcx.toBitVec + 96)) ⋆ (Eq ((zeros 8).At (0x10008 : BitVec 64)) ⋆ Eq ((zeros 8).At (0x10030 : BitVec 64)) ⋆ Eq ((zeros 8).At (0x101b8 : BitVec 64))
          ⋆ Eq ((zeros 40).At (0x101c8 : BitVec 64)) ⋆ Eq ((zeros 32).At (0x10248 : BitVec 64))) := by
  have H : Eq ((block sl ix root e1 root1 e2 root2).At (0x10000 : BitVec 64)) (mem sl ix root e1 root1 e2 root2) := rfl
  witness_split [hsl, hix, hroot, he1, hroot1, he2, hroot2]
  simp only [initial_state, word_bytes, nil_At_emp, Std.ExtHashMap.sep_emp, Std.ExtHashMap.emp_sep, UInt64.toBitVec_ofNat,
    BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, BitVec.reduceSub, List.length_nil] at H ⊢
  exact cast (congrFun (by ac_rfl) _) H

/-- **Non-vacuity of `Encode.fast_path`.**
With an empty prefix and `cap = 128`, the encoder returns `dst.ptr` and a nil error. -/
theorem runs_empty (sl ix root e1 root1 e2 root2 : List UInt8) (hsl : sl.length = 8) (hix : ix.length = 8)
    (hroot : root.length = 32) (he1 : e1.length = 8) (hroot1 : root1.length = 32) (he2 : e2.length = 8)
    (hroot2 : root2.length = 32) (zmms : RegZmms) (flags : StatusFlags) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec (0 : UInt64).toBitVec ∧ st.data.regs.rax = 0x10288
        ∧ st.data.regs.rdi = 0 ∧ st.data.regs.rsi = 0)
      ⟨initial_state sl ix root e1 root1 e2 root2 zmms flags, Host.addrOf 117⟩ :=
  eventually_mono (Encode.fast_path 117 placed_code fresh_code 26 placed_checkpoint fresh_checkpoint 0 (by decide)
    (model_memmove 0 placed_model fresh_model 0) (initial_state sl ix root e1 root1 e2 root2 zmms flags) 0 0
    0x10048 0x10068 0x100d0 0x100b0 0x10118 (by decide) (by decide)
    sl ix root (zeros 8) e1 (word_bytes 32) (zeros 32) root1 (zeros 8) e2 (word_bytes 32) (zeros 32) root2 []
    (zeros 8) (zeros 8) (zeros 32) (zeros 8) (zeros 32) (zeros 8) (zeros 32)
    hsl hix hroot rfl he1 rfl rfl hroot1 rfl he2 rfl rfl hroot2 rfl rfl rfl rfl rfl rfl rfl rfl
    (zeros 8) (zeros 8) (zeros 8) (zeros 16) (zeros 16) (zeros 16) (zeros 16) (zeros 8) (zeros 8) (zeros 8) (zeros 8)
    (zeros 8) (zeros 120) rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    _ (mem_premise sl ix root e1 root1 e2 root2 hsl hix hroot he1 hroot1 he2 hroot2 zmms flags)
    (by simp [initial_state]) (by simp [initial_state]) (by simp [initial_state]))
    (fun _ h => ⟨h.1, h.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1⟩)

example (z' : RegZmms) (f : StatusFlags) :=
  runs_empty (Int.toBytes 8 0x0123456789abcdef) (Int.toBytes 8 7) ((List.range 32).map (fun i => (UInt8.ofNat i)))
    (Int.toBytes 8 1) (List.replicate 32 0xaa) (Int.toBytes 8 (2 ^ 64 - 1)) (List.replicate 32 0xff)
    (by decide) (by decide) rfl (by decide) rfl (by decide) rfl z' f

/-! The witness state with a 3-byte prefix. The names `block` and `H` are the ones that `witness_split` uses. -/
namespace Prefix

/-- The memory block of `EncodeFastPath.block` with the 3-byte prefix `[0xaa, 0xbb, 0xcc]` before the 128 old `dst` bytes. -/
def block (sl ix root e1 root1 e2 root2 : List UInt8) : List UInt8 :=
  word_bytes 0 ++ (zeros 8 ++ (sl ++ (ix ++ (Int.toBytes 8 (0x10048 : BitVec 64).toInt ++ (Int.toBytes 8 32
  ++ (zeros 8 ++ (Int.toBytes 8 (0x10068 : BitVec 64).toInt ++ (Int.toBytes 8 (0x100d0 : BitVec 64).toInt
  ++ (root ++ (zeros 8 ++ (e1 ++ (Int.toBytes 8 (0x100b0 : BitVec 64).toInt ++ (Int.toBytes 8 32
  ++ (word_bytes 32 ++ (zeros 32 ++ (root1 ++ (zeros 8 ++ (e2 ++ (Int.toBytes 8 (0x10118 : BitVec 64).toInt
  ++ (Int.toBytes 8 32 ++ (word_bytes 32 ++ (zeros 32 ++ (root2 ++ (zeros 120 ++ (zeros 8 ++ (zeros 8
  ++ (zeros 8 ++ (zeros 40 ++ (zeros 8 ++ (zeros 8 ++ (zeros 16 ++ (zeros 16 ++ (zeros 16 ++ (zeros 16
  ++ (zeros 8 ++ (zeros 32 ++ (zeros 8 ++ (word_bytes 0 ++ (zeros 8 ++ (zeros 8 ++ ([0xaa, 0xbb, 0xcc] ++ (zeros 8 ++ (zeros 8
  ++ (zeros 32 ++ (zeros 8 ++ (zeros 32 ++ (zeros 8 ++ (zeros 32))))))))))))))))))))))))))))))))))))))))))))))))

def mem (sl ix root e1 root1 e2 root2 : List UInt8) : DataMem :=
  (block sl ix root e1 root1 e2 root2).At (0x10000 : BitVec 64)

/-- The witness state with the prefix `[0xaa, 0xbb, 0xcc]` at 0x10288, `len = 3` and `cap = 131`. -/
def initial_state (sl ix root e1 root1 e2 root2 : List UInt8) (zmms : RegZmms) (flags : StatusFlags) : MachineData :=
  ⟨⟨0x10008, 0x10288, 3, 0, 0, 131, 0x10270, 0, 0, 0, 0, 0, 0, 0, 0xfff0, 0⟩, zmms, flags,
    mem sl ix root e1 root1 e2 root2⟩

/-- The memory premise of `Encode.fast_path` on the witness state with a 3-byte prefix. -/
theorem mem_premise (sl ix root e1 root1 e2 root2 : List UInt8) (hsl : sl.length = 8) (hix : ix.length = 8)
    (hroot : root.length = 32) (he1 : e1.length = 8) (hroot1 : root1.length = 32) (he2 : e2.length = 8)
    (hroot2 : root2.length = 32) (zmms : RegZmms) (flags : StatusFlags) :
    (initial_state sl ix root e1 root1 e2 root2 zmms flags).dmem =⋆
      Eq ((Int.toBytes 8 (0 : UInt64).toBitVec.toInt).At (initial_state sl ix root e1 root1 e2 root2 zmms flags).regs.rsp.toBitVec)
        ⋆ Eq ((zeros 8).At ((initial_state sl ix root e1 root1 e2 root2 zmms flags).regs.rsp.toBitVec - 8)) ⋆ Eq ((zeros 8).At ((initial_state sl ix root e1 root1 e2 root2 zmms flags).regs.rsp.toBitVec + 8))
        ⋆ Eq ((zeros 8).At ((initial_state sl ix root e1 root1 e2 root2 zmms flags).regs.rsp.toBitVec + 16)) ⋆ Eq ((zeros 16).At ((initial_state sl ix root e1 root1 e2 root2 zmms flags).regs.rsp.toBitVec - 80))
        ⋆ Eq ((zeros 16).At ((initial_state sl ix root e1 root1 e2 root2 zmms flags).regs.rsp.toBitVec - 64)) ⋆ Eq ((zeros 16).At ((initial_state sl ix root e1 root1 e2 root2 zmms flags).regs.rsp.toBitVec - 112))
        ⋆ Eq ((zeros 16).At ((initial_state sl ix root e1 root1 e2 root2 zmms flags).regs.rsp.toBitVec - 96)) ⋆ Eq ((zeros 8).At ((initial_state sl ix root e1 root1 e2 root2 zmms flags).regs.rsp.toBitVec - 48))
        ⋆ Eq ((zeros 8).At ((initial_state sl ix root e1 root1 e2 root2 zmms flags).regs.rsp.toBitVec - 120)) ⋆ Eq ((zeros 8).At ((initial_state sl ix root e1 root1 e2 root2 zmms flags).regs.rsp.toBitVec - 128))
        ⋆ Eq ((zeros 8).At ((initial_state sl ix root e1 root1 e2 root2 zmms flags).regs.rsp.toBitVec - 176))
        ⋆ Eq ((zeros 8).At ((initial_state sl ix root e1 root1 e2 root2 zmms flags).regs.rsp.toBitVec - 192)) ⋆ Eq ((zeros 120).At ((initial_state sl ix root e1 root1 e2 root2 zmms flags).regs.rsp.toBitVec - 312 - BitVec.ofNat 64 0))
        ⋆ Eq ((Int.toBytes 8 (0 : UInt64).toBitVec.toInt).At ((initial_state sl ix root e1 root1 e2 root2 zmms flags).regs.r14.toBitVec + 16))
        ⋆ Eq (sl.At ((initial_state sl ix root e1 root1 e2 root2 zmms flags).regs.rax.toBitVec + 8)) ⋆ Eq (ix.At ((initial_state sl ix root e1 root1 e2 root2 zmms flags).regs.rax.toBitVec + 16))
        ⋆ Eq ((Int.toBytes 8 (0x10048 : BitVec 64).toInt).At ((initial_state sl ix root e1 root1 e2 root2 zmms flags).regs.rax.toBitVec + 24)) ⋆ Eq ((Int.toBytes 8 32).At ((initial_state sl ix root e1 root1 e2 root2 zmms flags).regs.rax.toBitVec + 32))
        ⋆ Eq ((Int.toBytes 8 (0x10068 : BitVec 64).toInt).At ((initial_state sl ix root e1 root1 e2 root2 zmms flags).regs.rax.toBitVec + 48))
        ⋆ Eq ((Int.toBytes 8 (0x100d0 : BitVec 64).toInt).At ((initial_state sl ix root e1 root1 e2 root2 zmms flags).regs.rax.toBitVec + 56))
        ⋆ Eq (root.At (0x10048 : BitVec 64))
        ⋆ Eq ((zeros 8).At (0x10068 : BitVec 64)) ⋆ Eq (e1.At ((0x10068 : BitVec 64) + 8)) ⋆ Eq ((Int.toBytes 8 (0x100b0 : BitVec 64).toInt).At ((0x10068 : BitVec 64) + 16))
        ⋆ Eq ((Int.toBytes 8 32).At ((0x10068 : BitVec 64) + 24)) ⋆ Eq ((word_bytes 32).At ((0x10068 : BitVec 64) + 32)) ⋆ Eq ((zeros 32).At ((0x10068 : BitVec 64) + 40)) ⋆ Eq (root1.At (0x100b0 : BitVec 64))
        ⋆ Eq ((zeros 8).At (0x100d0 : BitVec 64)) ⋆ Eq (e2.At ((0x100d0 : BitVec 64) + 8)) ⋆ Eq ((Int.toBytes 8 (0x10118 : BitVec 64).toInt).At ((0x100d0 : BitVec 64) + 16))
        ⋆ Eq ((Int.toBytes 8 32).At ((0x100d0 : BitVec 64) + 24)) ⋆ Eq ((word_bytes 32).At ((0x100d0 : BitVec 64) + 32)) ⋆ Eq ((zeros 32).At ((0x100d0 : BitVec 64) + 40)) ⋆ Eq (root2.At (0x10118 : BitVec 64))
        ⋆ Eq (([0xaa, 0xbb, 0xcc] : List UInt8).At (initial_state sl ix root e1 root1 e2 root2 zmms flags).regs.rbx.toBitVec)
        ⋆ Eq ((zeros 8).At ((initial_state sl ix root e1 root1 e2 root2 zmms flags).regs.rbx.toBitVec + (initial_state sl ix root e1 root1 e2 root2 zmms flags).regs.rcx.toBitVec))
        ⋆ Eq ((zeros 8).At ((initial_state sl ix root e1 root1 e2 root2 zmms flags).regs.rbx.toBitVec + (initial_state sl ix root e1 root1 e2 root2 zmms flags).regs.rcx.toBitVec + 8))
        ⋆ Eq ((zeros 32).At ((initial_state sl ix root e1 root1 e2 root2 zmms flags).regs.rbx.toBitVec + (initial_state sl ix root e1 root1 e2 root2 zmms flags).regs.rcx.toBitVec + 16))
        ⋆ Eq ((zeros 8).At ((initial_state sl ix root e1 root1 e2 root2 zmms flags).regs.rbx.toBitVec + (initial_state sl ix root e1 root1 e2 root2 zmms flags).regs.rcx.toBitVec + 48))
        ⋆ Eq ((zeros 32).At ((initial_state sl ix root e1 root1 e2 root2 zmms flags).regs.rbx.toBitVec + (initial_state sl ix root e1 root1 e2 root2 zmms flags).regs.rcx.toBitVec + 56))
        ⋆ Eq ((zeros 8).At ((initial_state sl ix root e1 root1 e2 root2 zmms flags).regs.rbx.toBitVec + (initial_state sl ix root e1 root1 e2 root2 zmms flags).regs.rcx.toBitVec + 88))
        ⋆ Eq ((zeros 32).At ((initial_state sl ix root e1 root1 e2 root2 zmms flags).regs.rbx.toBitVec + (initial_state sl ix root e1 root1 e2 root2 zmms flags).regs.rcx.toBitVec + 96)) ⋆ (Eq ((zeros 8).At (0x10008 : BitVec 64)) ⋆ Eq ((zeros 8).At (0x10030 : BitVec 64)) ⋆ Eq ((zeros 8).At (0x101b8 : BitVec 64))
          ⋆ Eq ((zeros 40).At (0x101c8 : BitVec 64)) ⋆ Eq ((zeros 32).At (0x10248 : BitVec 64))) := by
  have H : Eq ((block sl ix root e1 root1 e2 root2).At (0x10000 : BitVec 64)) (mem sl ix root e1 root1 e2 root2) := rfl
  witness_split [hsl, hix, hroot, he1, hroot1, he2, hroot2]
  simp only [initial_state, word_bytes, nil_At_emp, Std.ExtHashMap.sep_emp, Std.ExtHashMap.emp_sep, UInt64.toBitVec_ofNat,
    BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, BitVec.reduceSub, List.length_nil, List.length_cons] at H ⊢
  exact cast (congrFun (by ac_rfl) _) H

end Prefix

/-- **Non-vacuity of `Encode.fast_path` with a prefix.**
With the prefix `[0xaa, 0xbb, 0xcc]` and `cap = 131`, the encoder returns `dst.ptr` and a nil error. -/
theorem runs_prefix (sl ix root e1 root1 e2 root2 : List UInt8) (hsl : sl.length = 8) (hix : ix.length = 8)
    (hroot : root.length = 32) (he1 : e1.length = 8) (hroot1 : root1.length = 32) (he2 : e2.length = 8)
    (hroot2 : root2.length = 32) (zmms : RegZmms) (flags : StatusFlags) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec (0 : UInt64).toBitVec ∧ st.data.regs.rax = 0x10288
        ∧ st.data.regs.rdi = 0 ∧ st.data.regs.rsi = 0)
      ⟨Prefix.initial_state sl ix root e1 root1 e2 root2 zmms flags, Host.addrOf 117⟩ :=
  eventually_mono (Encode.fast_path 117 placed_code fresh_code 26 placed_checkpoint fresh_checkpoint 0 (by decide)
    (model_memmove 0 placed_model fresh_model 0) (Prefix.initial_state sl ix root e1 root1 e2 root2 zmms flags) 0 0
    0x10048 0x10068 0x100d0 0x100b0 0x10118 (by decide) (by decide)
    sl ix root (zeros 8) e1 (word_bytes 32) (zeros 32) root1 (zeros 8) e2 (word_bytes 32) (zeros 32) root2 [0xaa, 0xbb, 0xcc]
    (zeros 8) (zeros 8) (zeros 32) (zeros 8) (zeros 32) (zeros 8) (zeros 32)
    hsl hix hroot rfl he1 rfl rfl hroot1 rfl he2 rfl rfl hroot2 rfl rfl rfl rfl rfl rfl rfl rfl
    (zeros 8) (zeros 8) (zeros 8) (zeros 16) (zeros 16) (zeros 16) (zeros 16) (zeros 8) (zeros 8) (zeros 8) (zeros 8)
    (zeros 8) (zeros 120) rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    _ (Prefix.mem_premise sl ix root e1 root1 e2 root2 hsl hix hroot he1 hroot1 he2 hroot2 zmms flags)
    (by simp [Prefix.initial_state]) (by simp [Prefix.initial_state]) (by simp [Prefix.initial_state]))
    (fun _ h => ⟨h.1, h.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1⟩)

example (z' : RegZmms) (f : StatusFlags) :=
  runs_prefix (Int.toBytes 8 0x0123456789abcdef) (Int.toBytes 8 7) ((List.range 32).map (fun i => (UInt8.ofNat i)))
    (Int.toBytes 8 1) (List.replicate 32 0xaa) (Int.toBytes 8 (2 ^ 64 - 1)) (List.replicate 32 0xff)
    (by decide) (by decide) rfl (by decide) rfl (by decide) rfl z' f

end Prysm.AttestationData.Witness.EncodeFastPath
