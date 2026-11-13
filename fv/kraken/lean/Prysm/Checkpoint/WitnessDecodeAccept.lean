import Prysm.Checkpoint.DecodeAccept
import Runtime.CopyModel
import Runtime.BumpAllocatorVariants
import Machine.WitnessHost

/-!
# Witness of `Decode.accept` (decoder accept path)

Host: data labels, the real Go 1.26.10 `(*v1alpha1.Checkpoint).UnmarshalSSZ`
(index 5), the real `(*primitives.Epoch).UnmarshalSSZ` (index 113), the
1-byte bump `runtime.makeslice` (index 176, `bump_makeslice1`) and `MemmoveGrowsliceModel`
(index 182, `model_memmove`). One memory block at `0x10000`: bump pointer,
writeBarrier word, the 32-byte heap, guard word, the 40 input bytes, the
72-byte receiver (`state`, `Epoch`, `Root` header, `unknownFields`,
`sizeCache` + padding, all zero: a fresh `&Checkpoint{}`), and the 128-byte
stack window (`S = 8`). The frame `R` is exactly the two untouched 16-byte
gaps of the frame (rsp − 64 … rsp − 49, rsp − 24 … rsp − 9). For every epoch
word and root, every premise holds and the decoder returns nil with the
receiver's `Epoch` = the 8 input bytes.
-/

open Machine Runtime Machine.Witness Prysm.Checkpoint.Code

namespace Prysm.Checkpoint.Witness.DecodeAccept

set_option maxRecDepth 100000

def dataLabels : Program :=
  [.label "runtime.modelBumpPointer", .label "pad1", .label "pad2", .label "pad3", .label "pad4", .label "pad5",
   .label "pad6", .label "pad7", .label "runtime.writeBarrier"]

def program : Program := dataLabels ++ unmarshalSSZ ++ Prysm.Epoch.Code.unmarshalSSZ ++ BumpMakeslice1 ++ MemmoveGrowsliceModel

theorem program_length : program.length = 212 := by rfl

instance host : Host := mkHost program (by rw [program_length]; decide)

theorem host_program_eq : Host.prog = program := rfl

theorem placed_at_9 : unmarshalSSZ.IsInfixAt Host.prog 9 :=
  infixAt_of dataLabels (Prysm.Epoch.Code.unmarshalSSZ ++ BumpMakeslice1 ++ MemmoveGrowsliceModel) (by simp [host_program_eq, program, List.append_assoc]) rfl

theorem placed_at_117 : Prysm.Epoch.Code.unmarshalSSZ.IsInfixAt Host.prog 117 :=
  infixAt_of (dataLabels ++ unmarshalSSZ) (BumpMakeslice1 ++ MemmoveGrowsliceModel) (by simp [host_program_eq, program, List.append_assoc]) (by rfl)

theorem placed_at_180 : BumpMakeslice1.IsInfixAt Host.prog 180 :=
  infixAt_of (dataLabels ++ unmarshalSSZ ++ Prysm.Epoch.Code.unmarshalSSZ) MemmoveGrowsliceModel (by simp [host_program_eq, program, List.append_assoc]) (by rfl)

theorem placed_at_186 : MemmoveGrowsliceModel.IsInfixAt Host.prog 186 :=
  infixAt_of (dataLabels ++ unmarshalSSZ ++ Prysm.Epoch.Code.unmarshalSSZ ++ BumpMakeslice1) [] (by simp [host_program_eq, program, List.append_assoc])
    (by rfl)

theorem labels_fresh_at_9 : LabelsFresh unmarshalSSZ 9 := labelsFresh_of (by rw [host_program_eq]; decide)
theorem labels_fresh_at_117 : LabelsFresh Prysm.Epoch.Code.unmarshalSSZ 117 := labelsFresh_of (by rw [host_program_eq]; decide)
theorem labels_fresh_at_186 : LabelsFresh MemmoveGrowsliceModel 186 := labelsFresh_of (by rw [host_program_eq]; decide)
theorem labels_fresh_at_180 : ∀ i < 180, Host.prog[i]? ≠ some (.label "runtime.makeslice") :=
  notLabel_of (by rw [host_program_eq]; decide)

theorem label_bump_pointer : label "runtime.modelBumpPointer" = 0x10000 :=
  mk_label program _ 0 _ (by simp [program, dataLabels]) (by simp [labs])

theorem label_write_barrier : label "runtime.writeBarrier" = 0x10008 :=
  mk_label program _ 8 _ (by simp [program, dataLabels]) (by decide)

abbrev zeros (k : Nat) : List UInt8 := List.replicate k 0
abbrev zero_word_bytes : List UInt8 := Int.toBytes 8 (0 : UInt64).toBitVec.toInt

/-- bump pointer (→ 0x1000c) · writeBarrier · heap (32) · guard · input (40) · receiver (72)
· stack window: scratch (8) · rslot · m0 · m1 · m2 · gap (16) · l30 · l28 · l20 · gap (16) · fp ·
return slot · spill rax · spill rbx. -/
def block (e8 root : List UInt8) : List UInt8 :=
  Int.toBytes 8 (0x1000c : BitVec 64).toInt ++ ([0, 0, 0, 0] ++ (zeros 32 ++ (zero_word_bytes ++ (e8 ++ (root ++ (zeros 8 ++ (zeros 8 ++ (zeros 8
    ++ (zeros 8 ++ (zeros 8 ++ (zeros 32 ++ (zeros 8 ++ (zeros 8 ++ (zeros 8 ++ (zeros 8 ++ (zeros 8 ++ (zeros 16 ++ (zeros 8 ++ (zeros 8 ++ (zeros 8
    ++ (zeros 16 ++ (zeros 8 ++ (zero_word_bytes ++ (zeros 8 ++ zeros 8))))))))))))))))))))))))

def mem (e8 root : List UInt8) : DataMem := (block e8 root).At (0x10000 : BitVec 64)

def initial_state (e8 root : List UInt8) (zmms : RegZmms) (flags : StatusFlags) : MachineData :=
  ⟨⟨0x1005c, 0x10034, 40, 0, 0, 0, 0x1010c, 0, 0, 0, 0, 0, 0, 0, 0x1001c, 0⟩, zmms, flags, mem e8 root⟩

/-- The frame of the witness: the two 16-byte gaps of the stack window. -/
def frame_rest : DataMem → Prop := Eq ((zeros 16).At (0x100cc : BitVec 64)) ⋆ Eq ((zeros 16).At (0x100f4 : BitVec 64))

theorem lift_heap {X : DataMem → Prop} {m : DataMem}
    (h : (Eq ((Int.toBytes 8 (0x1000c : BitVec 64).toInt).At (0x10000 : BitVec 64))
      ⋆ (Eq ((zeros 32).At (0x1000c : BitVec 64)) ⋆ X)) m) : (bumpHeap 32 ⋆ X) m := by
  rw [← Std.ExtHashMap.sep_assoc] at h
  exact sep_mono_left (fun m hm => ⟨0x1000c, by decide, by rw [label_bump_pointer]; exact hm⟩) h

set_option maxHeartbeats 16000000 in
/-- **Non-vacuity of `Decode.accept`.** -/
theorem runs (e8 root : List UInt8) (he8 : e8.length = 8) (hroot : root.length = 32)
    (zmms : RegZmms) (flags : StatusFlags) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec (0 : UInt64).toBitVec ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0)
      ⟨initial_state e8 root zmms flags, Host.addrOf 9⟩ :=
  eventually_mono (Decode.accept 9 placed_at_9 labels_fresh_at_9 117 placed_at_117 labels_fresh_at_117 e8 root he8 hroot (initial_state e8 root zmms flags) 0 0
    (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 32)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl frame_rest 8 (Nat.le_refl _) (by decide) (zeros 8) rfl
    bumpHeap 32
    (by
      have H : Eq ((block e8 root).At (0x10000 : BitVec 64)) (mem e8 root) := rfl
      witness_split [he8, hroot]
      rw [Std.ExtHashMap.sep_comm_l (Eq (([0, 0, 0, 0] : List UInt8).At _)) (Eq ((zeros 32).At _))] at H
      have H2 := lift_heap H
      simp only [initial_state, frame_rest, zero_word_bytes, label_write_barrier, UInt64.toBitVec_ofNat, Int64.toBitVec_ofNat, BitVec.ofNat_eq_ofNat,
        BitVec.reduceAdd, BitVec.reduceSub] at H2 ⊢
      simp only [Std.ExtHashMap.sep_assoc] at H2 ⊢
      simp only [Std.ExtHashMap.sep_comm, Std.ExtHashMap.sep_comm_l] at H2 ⊢
      exact H2)
    (by simp [initial_state]) rfl (by omega) (bump_makeslice1 180 placed_at_180 labels_fresh_at_180 _) (model_memmove 186 placed_at_186 labels_fresh_at_186 8))
    (fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩)

/-- epoch 0 / root 0; a representative value and pattern root; 2^64 − 1 and 0xff root. -/
example (z' : RegZmms) (f : StatusFlags) := runs (Int.toBytes 8 0) (zeros 32) (by decide) rfl z' f
example (z' : RegZmms) (f : StatusFlags) :=
  runs (Int.toBytes 8 0x0123456789abcdef) ((List.range 32).map (fun i => (UInt8.ofNat i))) (by decide) rfl z' f
example (z' : RegZmms) (f : StatusFlags) :=
  runs (Int.toBytes 8 (2 ^ 64 - 1)) (List.replicate 32 0xff) (by decide) rfl z' f

end Prysm.Checkpoint.Witness.DecodeAccept
