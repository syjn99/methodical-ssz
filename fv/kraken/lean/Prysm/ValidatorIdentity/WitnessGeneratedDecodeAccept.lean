import Prysm.ValidatorIdentity.GeneratedDecodeAccept
import Runtime.CopyModel
import Runtime.BumpAllocatorVariants
import Machine.WitnessHost

/-!
# Witness of the generated `Decode.generated_accept` (`v1alpha1.ValidatorIdentity` decoder accept path; 24 flat hold-out types)

Written by the evidence script `f24wit.py`: the text of `Prysm/PendingDeposit/WitnessDecodeAccept.lean` with the
v1alpha1.ValidatorIdentity host and layout. It shows that the premises of the generated accept theorem (statement = kind instance)
are satisfiable. Host: data labels, the real Go 1.26.10 `(*v1alpha1.ValidatorIdentity).UnmarshalSSZ` (index 9), `primitives.ValidatorIndex` UnmarshalSSZ, `primitives.Epoch` UnmarshalSSZ,
the 1-byte bump `runtime.makeslice` (276, `bump_makeslice1`) and `MemmoveGrowsliceModel` (282, `model_memmove`).
One memory block at `0x10000`: bump pointer, writeBarrier word, the 48-byte heap, guard word, the 64 input bytes,
the 80-byte receiver (`prysm/ir/ir-mainnet.json` gc amd64 layout: `state`, per byte field a slice header with an
old pointer word and len = cap = 0, per uint64 field a zero word, then 32 untouched tail bytes), the callee block
(`S = 8`), the return slot, the argument area, the untouched frame ranges, the slice pointer save, the saved rbp
and the caller's slots (rsp = 0x10144). The frame `R` is the receiver tail, the untouched frame ranges and the
caller's word at rsp + 24. For every input and every old pointer word every premise holds and the decoder returns
nil. The receiver is a Go value of `v1alpha1.ValidatorIdentity` (zero `state`, zero-length slices, zero integers).
-/

open Machine Runtime Machine.Witness Codec Prysm.ValidatorIdentity.Code

namespace Prysm.ValidatorIdentity.Witness.GeneratedDecodeAccept

set_option maxRecDepth 100000

def dataLabels : Program :=
  [.label "runtime.modelBumpPointer", .label "pad1", .label "pad2", .label "pad3", .label "pad4", .label "pad5",
   .label "pad6", .label "pad7", .label "runtime.writeBarrier"]

def program : Program := dataLabels ++ unmarshalSSZ ++ Prysm.ValidatorIndex.Code.unmarshalSSZ ++ Prysm.Epoch.Code.unmarshalSSZ ++ BumpMakeslice1 ++ MemmoveGrowsliceModel

theorem program_length : program.length = 308 := by rfl

instance host : Host := mkHost program (by rw [program_length]; decide)

theorem host_program_eq : Host.prog = program := rfl

theorem placed_at_9 : unmarshalSSZ.IsInfixAt Host.prog 9 :=
  infixAt_of dataLabels (Prysm.ValidatorIndex.Code.unmarshalSSZ ++ Prysm.Epoch.Code.unmarshalSSZ ++ BumpMakeslice1 ++ MemmoveGrowsliceModel) (by simp [host_program_eq, program, List.append_assoc]) rfl
theorem placed_at_150 : Prysm.ValidatorIndex.Code.unmarshalSSZ.IsInfixAt Host.prog 150 :=
  infixAt_of (dataLabels ++ unmarshalSSZ) (Prysm.Epoch.Code.unmarshalSSZ ++ BumpMakeslice1 ++ MemmoveGrowsliceModel)
    (by simp [host_program_eq, program, List.append_assoc]) (by rfl)
theorem labels_fresh_at_150 : LabelsFresh Prysm.ValidatorIndex.Code.unmarshalSSZ 150 := labelsFresh_of (by rw [host_program_eq]; decide)
theorem placed_at_213 : Prysm.Epoch.Code.unmarshalSSZ.IsInfixAt Host.prog 213 :=
  infixAt_of (dataLabels ++ unmarshalSSZ ++ Prysm.ValidatorIndex.Code.unmarshalSSZ) (BumpMakeslice1 ++ MemmoveGrowsliceModel)
    (by simp [host_program_eq, program, List.append_assoc]) (by rfl)
theorem labels_fresh_at_213 : LabelsFresh Prysm.Epoch.Code.unmarshalSSZ 213 := labelsFresh_of (by rw [host_program_eq]; decide)
theorem placed_at_276 : BumpMakeslice1.IsInfixAt Host.prog 276 :=
  infixAt_of (dataLabels ++ unmarshalSSZ ++ Prysm.ValidatorIndex.Code.unmarshalSSZ ++ Prysm.Epoch.Code.unmarshalSSZ) MemmoveGrowsliceModel
    (by simp [host_program_eq, program, List.append_assoc]) (by rfl)
theorem placed_at_282 : MemmoveGrowsliceModel.IsInfixAt Host.prog 282 :=
  infixAt_of (dataLabels ++ unmarshalSSZ ++ Prysm.ValidatorIndex.Code.unmarshalSSZ ++ Prysm.Epoch.Code.unmarshalSSZ ++ BumpMakeslice1) []
    (by simp [host_program_eq, program, List.append_assoc]) (by rfl)

theorem labels_fresh_at_9 : LabelsFresh unmarshalSSZ 9 := labelsFresh_of (by rw [host_program_eq]; decide)
theorem labels_fresh_at_282 : LabelsFresh MemmoveGrowsliceModel 282 := labelsFresh_of (by rw [host_program_eq]; decide)
theorem labels_fresh_at_276 : ∀ i < 276, Host.prog[i]? ≠ some (.label "runtime.makeslice") :=
  notLabel_of (by rw [host_program_eq]; decide)

theorem label_bump_pointer : label "runtime.modelBumpPointer" = 0x10000 :=
  mk_label program _ 0 _ (by simp [program, dataLabels]) (by simp [labs])

theorem label_write_barrier : label "runtime.writeBarrier" = 0x10008 :=
  mk_label program _ 8 _ (by simp [program, dataLabels]) (by decide)

abbrev zeros (k : Nat) : List UInt8 := List.replicate k 0
abbrev zero_word_bytes : List UInt8 := Int.toBytes 8 (0 : UInt64).toBitVec.toInt

def block (f0 f1 f2 oP1 : List UInt8) : List UInt8 :=
  (Int.toBytes 8 (0x1000c : BitVec 64).toInt) ++ (([0, 0, 0, 0]) ++ ((zeros 48) ++ (zero_word_bytes ++ (f0 ++ (f1 ++ (f2 ++ ((zeros 8) ++ ((zeros 8) ++ (oP1 ++ ((zeros 8) ++ ((zeros 8) ++ ((zeros 8) ++ ((zeros 32) ++ ((zeros 16) ++ ((zeros 8) ++ ((zeros 8) ++ ((zeros 8) ++ ((zeros 8) ++ ((zeros 16) ++ ((zeros 8) ++ ((zeros 32) ++ ((zeros 8) ++ (zero_word_bytes ++ ((zeros 8) ++ ((zeros 8) ++ ((zeros 8) ++ ((zeros 8))))))))))))))))))))))))))))

def mem (f0 f1 f2 oP1 : List UInt8) : DataMem :=
  (block f0 f1 f2 oP1).At (0x10000 : BitVec 64)

def initial_state (f0 f1 f2 oP1 : List UInt8) (zmms : RegZmms) (flags : StatusFlags) : MachineData :=
  ⟨⟨0x10084, 0x10044, 64, 0, 0, 64, 0x10144, 0, 0, 0, 0, 0, 0, 0, 0x1002c, 0⟩, zmms, flags,
    mem f0 f1 f2 oP1⟩

/-- The frame of the witness. -/
def frame_rest : DataMem → Prop :=
  Eq ((zeros 32).At (0x100b4 : BitVec 64)) ⋆ Eq ((zeros 16).At (0x10104 : BitVec 64)) ⋆ Eq ((zeros 32).At (0x1011c : BitVec 64))
    ⋆ Eq ((zeros 8).At (0x1015c : BitVec 64))

theorem lift_heap {X : DataMem → Prop} {m : DataMem}
    (h : (Eq ((Int.toBytes 8 (0x1000c : BitVec 64).toInt).At (0x10000 : BitVec 64))
      ⋆ (Eq ((zeros 48).At (0x1000c : BitVec 64)) ⋆ X)) m) : (bumpHeap 48 ⋆ X) m := by
  rw [← Std.ExtHashMap.sep_assoc] at h
  exact sep_mono_left (fun m hm => ⟨0x1000c, by decide, by rw [label_bump_pointer]; exact hm⟩) h

set_option maxHeartbeats 16000000 in
/-- **Non-vacuity of the generated `Decode.generated_accept`** (premises of the kind instance are satisfiable). -/
theorem runs (f0 f1 f2 oP1 : List UInt8) (hf0 : f0.length = 8) (hf1 : f1.length = 48) (hf2 : f2.length = 8) (h1 : oP1.length = 8)
    (zmms : RegZmms) (flags : StatusFlags) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec (0 : UInt64).toBitVec ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0)
      ⟨initial_state f0 f1 f2 oP1 zmms flags, Host.addrOf 9⟩ :=
  eventually_mono (Prysm.ValidatorIdentity.Decode.generated_accept 9 placed_at_9 labels_fresh_at_9 150 placed_at_150 labels_fresh_at_150 213 placed_at_213 labels_fresh_at_213
    f0 f1 f2 hf0 hf1 hf2 (initial_state f0 f1 f2 oP1 zmms flags)
    0 0 (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 16) (zeros 8) (zeros 8) oP1 (zeros 8) (zeros 8) (zeros 8)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl h1 rfl rfl rfl
    frame_rest 8 (by decide) rfl bumpHeap 48
    (by
      have H : Eq ((block f0 f1 f2 oP1).At (0x10000 : BitVec 64)) (mem f0 f1 f2 oP1) := rfl
      witness_split [hf0, hf1, hf2, h1]
      rw [Std.ExtHashMap.sep_comm_l (Eq (([0, 0, 0, 0] : List UInt8).At _)) (Eq ((zeros 48).At _))] at H
      have H2 := lift_heap H
      simp only [initial_state, frame_rest, zero_word_bytes, label_write_barrier, UInt64.toBitVec_ofNat, Int64.toBitVec_ofNat, BitVec.ofNat_eq_ofNat,
        BitVec.reduceAdd, BitVec.reduceSub] at H2 ⊢
      simp only [Std.ExtHashMap.sep_assoc] at H2 ⊢
      simp only [Std.ExtHashMap.sep_comm, Std.ExtHashMap.sep_comm_l] at H2 ⊢
      exact H2)
    (by simp [initial_state]) rfl (Nat.le_refl _) (bump_makeslice1 276 placed_at_276 labels_fresh_at_276 _) (model_memmove 282 placed_at_282 labels_fresh_at_282 _))
    (fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩)

/-- Zero input with nil slices; a representative input with non-nil old pointer words; all-0xff input. -/
example (z' : RegZmms) (f : StatusFlags) :=
  runs (zeros 8) (zeros 48) (zeros 8) (zeros 8) rfl rfl rfl rfl z' f
example (z' : RegZmms) (f : StatusFlags) :=
  runs (Int.toBytes 8 0x0123456789abcde0) ((List.range 48).map (fun i => UInt8.ofNat (i + 10))) (Int.toBytes 8 0x0123456789abcde2) (Int.toBytes 8 0x20000) (by decide) rfl (by decide) (by decide) z' f
example (z' : RegZmms) (f : StatusFlags) :=
  runs (List.replicate 8 0xff) (List.replicate 48 0xff) (List.replicate 8 0xff) (List.replicate 8 0xff) rfl rfl rfl rfl z' f

end Prysm.ValidatorIdentity.Witness.GeneratedDecodeAccept
